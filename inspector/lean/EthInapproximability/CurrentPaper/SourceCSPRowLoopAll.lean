import EthInapproximability.CurrentPaper.SourceCSPRowLoopIteration
import EthInapproximability.CurrentPaper.UnaryBinaryEncoding

/-!
# The reusable loop over every canonical source row

The same finite controller parses and validates each row from the unread
suffix. Its one-row cost is charged for every row, including the literal
clear/cap-restoration cost of the bank left by validation. At zero unary
counter, a separate physical check requires the suffix to be empty.
-/

namespace EthInapproximability.CurrentPaper.SourceCSPRowLoopAll

open Turing BitMachineEncoding
open SourceCSPRowLoopController

variable {n a q : Nat}

abbrev Row := SourceCSPCodec.Row n a q

def rowBytes (rows : List (Row (n := n) (a := a) (q := q))) : List Bool :=
  (rows.map SourceCSPCodec.rowFields).flatten

theorem rowBytes_nil : rowBytes ([] : List (Row (n := n) (a := a) (q := q))) = [] := rfl

theorem rowBytes_cons (row : Row (n := n) (a := a) (q := q)) (rows : List Row) :
    rowBytes (row :: rows) = SourceCSPCodec.rowFields row ++ rowBytes rows := rfl

def frameResetCost (q : Nat)
    (U : SourceCSPRowQueryFrame.Stack q → List Bool) (cap : List Bool) : Nat :=
  SourceCSPRowLoopIteration.resetCost q (Sum.elim U (fun _ => [])) cap

theorem resetCost_elim (q : Nat)
    (U : SourceCSPRowQueryFrame.Stack q → List Bool)
    (E : Fin 4 → List Bool) (cap : List Bool) :
    SourceCSPRowLoopIteration.resetCost q (Sum.elim U E) cap =
      frameResetCost q U cap := by
  unfold SourceCSPRowLoopIteration.resetCost frameResetCost
  have hs : (∑ i : Fin (q * 5 + 4),
        (Sum.elim U E (SourceCSPRowLoopClear.scratch q i)).length) =
      ∑ i : Fin (q * 5 + 4),
        (Sum.elim U (fun _ => []) (SourceCSPRowLoopClear.scratch q i)).length := by
    apply Finset.sum_congr rfl
    intro i _
    cases h : SourceCSPRowLoopClear.scratchEquiv q i with
    | inl p => simp [SourceCSPRowLoopClear.scratch,
        SourceCSPRowLoopClear.scratchSlot, h]
    | inr k => simp [SourceCSPRowLoopClear.scratch,
        SourceCSPRowLoopClear.scratchSlot, h]
  rw [hs]
  rfl

def queryCost (row : Row (n := n) (a := a) (q := q))
    (rest : List Bool) (L : Nat) : Nat :=
  1 + (q * (2 * (SourceCSPCodec.rowFields row ++ rest).length + 4) +
    2 * a ^ q + 3 + q * (100 * (L + 1) ^ 2) + 2)

def stepCost (row : Row (n := n) (a := a) (q := q))
    (rest : List Bool) (L : Nat)
    (U : SourceCSPRowQueryFrame.Stack q → List Bool) : Nat :=
  queryCost row rest L + 1 + frameResetCost q U
    (List.replicate (n - 1) true)

/-- A charge witness is a bank actually reached by the physical row-loop
program at `.yield`, from the canonical row prefix and a positive unary
remaining-row counter. It is not an arbitrary oversized scratch bank. -/
def Produced (row : Row (n := n) (a := a) (q := q))
    (rest count : List Bool)
    (U : SourceCSPRowQueryFrame.Stack q → List Bool) : Prop :=
  ∃ (ty : Nat) (v : QueryControl) (E : Fin 4 → List Bool),
    E 0 = true :: count ∧
    E 1 = List.replicate (n - 1) true ∧ E 3 = [] ∧
    ty ≤ queryCost row rest n ∧
    ((advance (program q (a ^ q)))^[ty])
      (⟨some (adminLabel .check), initialControl,
        Sum.elim (SourceCSPRowQueryFrame.initial
          (SourceCSPCodec.rowFields row ++ rest)
          (List.replicate (n - 1) true)) E⟩ : Config q (a ^ q)) =
      ⟨some (adminLabel .yield), queryControl v,
        Sum.elim U (Function.update E 0 count)⟩

theorem valid_row_step (row : Row (n := n) (a := a) (q := q))
    (hn : 0 < n) (rest : List Bool)
    (E : Fin 4 → List Bool) (count : List Bool)
    (hcount : E 0 = true :: count)
    (hcapE : E 1 = List.replicate (n - 1) true)
    (hscratch : E 3 = []) :
    ∃ (t : Nat) (U : SourceCSPRowQueryFrame.Stack q → List Bool),
      t ≤ stepCost row rest n U ∧ Produced row rest count U ∧
      ((advance (program q (a ^ q)))^[t])
        (⟨some (adminLabel .check), initialControl,
          Sum.elim (SourceCSPRowQueryFrame.initial
            (SourceCSPCodec.rowFields row ++ rest)
            (List.replicate (n - 1) true)) E⟩ : Config q (a ^ q)) =
        ⟨some (adminLabel .check), initialControl,
          Sum.elim (SourceCSPRowQueryFrame.initial rest
            (List.replicate (n - 1) true))
            (Function.update E 0 count)⟩ := by
  have hword : ∀ j : Fin q, (row.1 j).val.bits.length ≤ n := by
    intro j
    exact (UnaryBinaryEncoding.bits_length_le _).trans (Nat.le_of_lt (row.1 j).isLt)
  obtain ⟨ty, tf, v, U, hty, htf, hyield, hrun, _, _, _, _⟩ :=
    SourceCSPRowLoopIteration.valid_row_next row hn rest n hword
      (Nat.sub_le n 1) E count hcount hcapE hscratch
  refine ⟨tf, U, ?_, ⟨ty, v, E, hcount, hcapE, hscratch, ?_, hyield⟩,
    hrun⟩
  · rw [resetCost_elim] at htf
    dsimp only [stepCost, queryCost]
    omega
  · simpa only [queryCost] using hty

inductive Charges : List (Row (n := n) (a := a) (q := q)) → List Nat → Prop
  | nil : Charges [] []
  | cons (row : Row) (tail : List Row)
      (U : SourceCSPRowQueryFrame.Stack q → List Bool) (costs : List Nat)
      (hproduced : Produced row (rowBytes tail)
        (List.replicate tail.length true) U)
      (hcosts : Charges tail costs) :
      Charges (row :: tail)
        (stepCost row (rowBytes tail) n U :: costs)

theorem charges_length {rows : List (Row (n := n) (a := a) (q := q))}
    {costs : List Nat} (h : Charges rows costs) : costs.length = rows.length := by
  induction h with
  | nil => rfl
  | cons row tail U costs hproduced hcosts ih => simp [ih]

theorem rows_to_check (hn : 0 < n)
    (rows : List (Row (n := n) (a := a) (q := q)))
    (E : Fin 4 → List Bool)
    (hcount : E 0 = List.replicate rows.length true)
    (hcap : E 1 = List.replicate (n - 1) true)
    (hscratch : E 3 = []) :
    ∃ (t : Nat) (costs : List Nat),
      Charges rows costs ∧ t ≤ costs.sum ∧
      ((advance (program q (a ^ q)))^[t])
        (⟨some (adminLabel .check), initialControl,
          Sum.elim (SourceCSPRowQueryFrame.initial
            (rowBytes rows) (List.replicate (n - 1) true)) E⟩ :
          Config q (a ^ q)) =
        ⟨some (adminLabel .check), initialControl,
          Sum.elim (SourceCSPRowQueryFrame.initial []
            (List.replicate (n - 1) true))
            (Function.update E 0 [])⟩ := by
  induction rows generalizing E with
  | nil =>
      refine ⟨0, [], Charges.nil, by simp, ?_⟩
      have he : Function.update E 0 [] = E := by
        funext k
        by_cases hk : k = 0
        · subst k
          simpa only [Function.update_self] using hcount.symm
        · simp [Function.update_of_ne hk]
      simp only [rowBytes_nil, he, Function.iterate_zero, id_eq]
  | cons row tail ih =>
      have hcount' : E 0 = true :: List.replicate tail.length true := by
        simpa only [List.length_cons, List.replicate_succ] using hcount
      obtain ⟨t₁, U, ht₁, hproduced, hrun₁⟩ :=
        valid_row_step row hn (rowBytes tail) E
          (List.replicate tail.length true) hcount' hcap hscratch
      let E' := Function.update E 0 (List.replicate tail.length true)
      have hc' : E' 0 = List.replicate tail.length true :=
        Function.update_self 0 _ E
      have hcap' : E' 1 = List.replicate (n - 1) true := by
        simpa only [E', Function.update_of_ne (by decide : (1 : Fin 4) ≠ 0)]
          using hcap
      have hs' : E' 3 = [] := by
        simpa only [E', Function.update_of_ne (by decide : (3 : Fin 4) ≠ 0)]
          using hscratch
      obtain ⟨t₂, costs, hcosts, ht₂, hrun₂⟩ := ih E' hc' hcap' hs'
      refine ⟨t₁ + t₂,
        stepCost row (rowBytes tail) n U :: costs,
        Charges.cons row tail U costs hproduced hcosts, ?_, ?_⟩
      · simp only [List.sum_cons]
        omega
      · rw [show t₁ + t₂ = t₂ + t₁ by omega,
          Function.iterate_add_apply]
        simpa only [rowBytes_cons, E', Function.update_idem] using
          congrArg ((advance (program q (a ^ q)))^[t₂]) hrun₁ |>.trans hrun₂

/-- The same controller accepts exactly after the supplied unary count has
been consumed and the physical unread-row stack is empty. The `Charges`
list records every parsed row's query and literal reset cost. -/
theorem rows_accept (hn : 0 < n)
    (rows : List (Row (n := n) (a := a) (q := q)))
    (E : Fin 4 → List Bool)
    (hcount : E 0 = List.replicate rows.length true)
    (hcap : E 1 = List.replicate (n - 1) true)
    (hscratch : E 3 = []) :
    ∃ (t : Nat) (costs : List Nat),
      Charges rows costs ∧ costs.length = rows.length ∧
      t ≤ costs.sum + 3 ∧
      ((advance (program q (a ^ q)))^[t])
        (⟨some (adminLabel .check), initialControl,
          Sum.elim (SourceCSPRowQueryFrame.initial
            (rowBytes rows) (List.replicate (n - 1) true)) E⟩ :
          Config q (a ^ q)) =
        ⟨none, ((queryStart, resetStart), some true),
          Sum.elim (SourceCSPRowQueryFrame.initial []
            (List.replicate (n - 1) true))
            (Function.update E 0 [])⟩ := by
  obtain ⟨tr, costs, hcosts, htr, hrun⟩ :=
    rows_to_check hn rows E hcount hcap hscratch
  let S : Stack q → List Bool :=
    Sum.elim (SourceCSPRowQueryFrame.initial []
      (List.replicate (n - 1) true)) (Function.update E 0 [])
  have hc : S (.inr 0) = [] := by
    change Function.update E 0 [] 0 = []
    simp only [Function.update_self]
  have hs : S (.inl (.inr 0)) = [] := rfl
  have hf := finish_empty q (a ^ q) S hc hs
  refine ⟨tr + 3, costs, hcosts, charges_length hcosts, by omega, ?_⟩
  rw [show tr + 3 = 3 + tr by omega, Function.iterate_add_apply, hrun]
  exact hf

end EthInapproximability.CurrentPaper.SourceCSPRowLoopAll
