import EthInapproximability.CurrentPaper.SourceCSPRowLoopOne

/-!
# Executing one canonical source row in the fixed row loop

The physical unary counter is decremented before parsing. The final query
words, truth table, status, and exact unread suffix are exposed at `.yield`.
No row-list oracle or disjoint copy of the parser is used.
-/

namespace EthInapproximability.CurrentPaper.SourceCSPRowLoopIteration

open Turing BitMachineEncoding
open SourceCSPRowLoopController

theorem update_outer {q : Nat}
    (T : SourceCSPRowQueryFrame.Stack q → List Bool)
    (E : Fin 4 → List Bool) (word : List Bool) :
    Function.update (Sum.elim T E) (.inr 0) word =
      Sum.elim T (Function.update E 0 word) := by
  funext k
  cases k with
  | inl k => simp
  | inr k => simp

theorem valid_row_yield {n a q : Nat} (row : SourceCSPCodec.Row n a q)
    (hn : 0 < n) (rest : List Bool) (L : Nat)
    (hword : ∀ j : Fin q, (row.1 j).val.bits.length ≤ L)
    (hcap : n - 1 ≤ L) (E : Fin 4 → List Bool) (count : List Bool)
    (hcount : E 0 = true :: count) :
    ∃ (t : Nat) (v : QueryControl)
      (U : SourceCSPRowQueryFrame.Stack q → List Bool),
      t ≤ 1 + (q * (2 * (SourceCSPCodec.rowFields row ++ rest).length + 4) +
        2 * a ^ q + 3 + q * (100 * (L + 1) ^ 2) + 2) ∧
      ((advance (program q (a ^ q)))^[t])
        (⟨some (adminLabel .check), initialControl,
          Sum.elim (SourceCSPRowQueryFrame.initial
            (SourceCSPCodec.rowFields row ++ rest)
            (List.replicate (n - 1) true)) E⟩ : Config q (a ^ q)) =
        ⟨some (adminLabel .yield), queryControl v,
          Sum.elim U (Function.update E 0 count)⟩ ∧
      U (.inr 0) = rest ∧ U (.inr 4) = [true] ∧
      (∀ j : Fin q, U (.inl (j, 1)) =
        List.replicate (row.1 j).val true) ∧
      U (.inr 2) = true :: List.ofFn row.2 := by
  obtain ⟨t, c, ht, hr, hl, hs, hq, hsource, hout⟩ :=
    SourceCSPRowQueryUnary.combined_valid_row_unary row hn rest L hword hcap
  rcases c with ⟨l, v, U⟩
  cases l with
  | some l => cases hl
  | none =>
      have hrun : ((advance (SourceCSPRowQueryFrame.combinedProgram q (a ^ q)))^[t])
          (⟨some (BitMachineRawSequence.leftLabel
            (.start 0 : SourceCSPRowController.Label q (a ^ q))), queryStart,
            SourceCSPRowQueryFrame.initial
              (SourceCSPCodec.rowFields row ++ rest)
              (List.replicate (n - 1) true)⟩ :
            TM2.Cfg (fun _ : SourceCSPRowQueryFrame.Stack q => Bool)
              (QueryLabel q (a ^ q)) QueryControl) = ⟨none, v, U⟩ := by
        simpa only [queryStart] using hr
      let E' := Function.update E 0 count
      obtain ⟨u, hu, hquery⟩ := SourceCSPRowLoopOne.query_lift q (a ^ q)
        (SourceCSPRowQueryFrame.initial
          (SourceCSPCodec.rowFields row ++ rest)
          (List.replicate (n - 1) true)) U E' v t hrun
      let T : SourceCSPRowQueryFrame.Stack q → List Bool := SourceCSPRowQueryFrame.initial
        (SourceCSPCodec.rowFields row ++ rest)
        (List.replicate (n - 1) true)
      have hcheck := check_positive q (a ^ q) (Sum.elim T E) count hcount
      have hwhole : ((advance (program q (a ^ q)))^[1 + u])
          (⟨some (adminLabel .check), initialControl,
            Sum.elim T E⟩ : Config q (a ^ q)) =
          ⟨some (adminLabel .yield), queryControl v, Sum.elim U E'⟩ := by
        rw [show 1 + u = u + 1 by omega, Function.iterate_add_apply,
          Function.iterate_one, hcheck, update_outer, hquery]
      refine ⟨1 + u, v, U, by omega, ?_, hsource, hs, hq, hout⟩
      simpa only [T, E'] using hwhole

def resetCost (q : Nat) (S : Stack q → List Bool) (cap : List Bool) : Nat :=
  (∑ i : Fin (q * 5 + 4),
      (S (SourceCSPRowLoopClear.scratch q i)).length) +
    (q * 5 + 4) + 2 + (2 * cap.length + 2) + 1

theorem valid_row_next {n a q : Nat} (row : SourceCSPCodec.Row n a q)
    (hn : 0 < n) (rest : List Bool) (L : Nat)
    (hword : ∀ j : Fin q, (row.1 j).val.bits.length ≤ L)
    (hcap : n - 1 ≤ L) (E : Fin 4 → List Bool) (count : List Bool)
    (hcount : E 0 = true :: count)
    (hcapE : E 1 = List.replicate (n - 1) true)
    (hscratch : E 3 = []) :
    ∃ (ty tf : Nat) (v : QueryControl)
      (U : SourceCSPRowQueryFrame.Stack q → List Bool),
      ty ≤ 1 + (q * (2 * (SourceCSPCodec.rowFields row ++ rest).length + 4) +
        2 * a ^ q + 3 + q * (100 * (L + 1) ^ 2) + 2) ∧
      tf ≤ ty + 1 + resetCost q
        (Sum.elim U (Function.update E 0 count))
        (List.replicate (n - 1) true) ∧
      ((advance (program q (a ^ q)))^[ty])
        (⟨some (adminLabel .check), initialControl,
          Sum.elim (SourceCSPRowQueryFrame.initial
            (SourceCSPCodec.rowFields row ++ rest)
            (List.replicate (n - 1) true)) E⟩ : Config q (a ^ q)) =
        ⟨some (adminLabel .yield), queryControl v,
          Sum.elim U (Function.update E 0 count)⟩ ∧
      ((advance (program q (a ^ q)))^[tf])
        (⟨some (adminLabel .check), initialControl,
          Sum.elim (SourceCSPRowQueryFrame.initial
            (SourceCSPCodec.rowFields row ++ rest)
            (List.replicate (n - 1) true)) E⟩ : Config q (a ^ q)) =
        ⟨some (adminLabel .check), initialControl,
          Sum.elim (SourceCSPRowQueryFrame.initial rest
            (List.replicate (n - 1) true))
            (Function.update E 0 count)⟩ ∧
      U (.inr 0) = rest ∧ U (.inr 4) = [true] ∧
      (∀ j : Fin q, U (.inl (j, 1)) =
        List.replicate (row.1 j).val true) ∧
      U (.inr 2) = true :: List.ofFn row.2 := by
  obtain ⟨ty, v, U, hty, hyield, hsource, hstatus, hquery, htable⟩ :=
    valid_row_yield row hn rest L hword hcap E count hcount
  let E' := Function.update E 0 count
  let S : Stack q → List Bool := Sum.elim U E'
  have hcap' : S (.inr 1) = List.replicate (n - 1) true := by
    simpa only [S, E', Function.update_of_ne (by decide : (1 : Fin 4) ≠ 0)]
      using hcapE
  have hscratch' : S (.inr 3) = [] := by
    simpa only [S, E', Function.update_of_ne (by decide : (3 : Fin 4) ≠ 0)]
      using hscratch
  obtain ⟨tr, htr, hreset⟩ := SourceCSPRowLoopOne.reset_lift q (a ^ q)
    S rest (List.replicate (n - 1) true) hsource hcap' hscratch'
  have hstep := yield_true q (a ^ q) S v hstatus
  have hafter : ((advance (program q (a ^ q)))^[1 + ty])
      (⟨some (adminLabel .check), initialControl,
        Sum.elim (SourceCSPRowQueryFrame.initial
          (SourceCSPCodec.rowFields row ++ rest)
          (List.replicate (n - 1) true)) E⟩ : Config q (a ^ q)) =
      ⟨some (resetLabel (BitMachineRawSequence.leftLabel 0)),
        initialControl, S⟩ := by
    rw [Function.iterate_add_apply, hyield, Function.iterate_one]
    exact hstep
  have hwhole : ((advance (program q (a ^ q)))^[ty + 1 + tr])
      (⟨some (adminLabel .check), initialControl,
        Sum.elim (SourceCSPRowQueryFrame.initial
          (SourceCSPCodec.rowFields row ++ rest)
          (List.replicate (n - 1) true)) E⟩ : Config q (a ^ q)) =
      ⟨some (adminLabel .check), initialControl,
        Sum.elim (SourceCSPRowQueryFrame.initial rest
          (List.replicate (n - 1) true)) E'⟩ := by
    rw [show ty + 1 + tr = tr + (1 + ty) by omega,
      Function.iterate_add_apply, hafter]
    simpa only [S, E'] using hreset
  refine ⟨ty, ty + 1 + tr, v, U, hty, ?_, hyield, ?_,
    hsource, hstatus, hquery, htable⟩
  · change tr ≤ resetCost q S (List.replicate (n - 1) true) at htr
    change ty + 1 + tr ≤ ty + 1 + resetCost q S
      (List.replicate (n - 1) true)
    omega
  · simpa only [E'] using hwhole

end EthInapproximability.CurrentPaper.SourceCSPRowLoopIteration
