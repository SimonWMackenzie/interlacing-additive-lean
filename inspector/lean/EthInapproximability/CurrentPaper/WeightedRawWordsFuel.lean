import EthInapproximability.CurrentPaper.WeightedRawWordsHandoff
import EthInapproximability.CurrentPaper.MatrixBinaryAddress

/-! # S5 (partial): from little-endian `Nat.bits k` to unary fuel `k`

Checked here: the ordering bridge `valueFrom 0 (Nat.bits k).reverse = k`, a
physical reversal by transfer (pop/push, one step per bit plus one), and the
production `MatrixBinaryAddress.program` embedded on the global bank, composed
into one fixed program that turns a cell holding `Nat.bits k` into master
`K = unary k` with clock `(|bits|+1) + 1 + (4k + 3|bits| + 2)`.
NOT done here: the embedded `ClockRuntime` machine and the counter-field
projection that produce `Nat.bits k` from master `N`. -/

namespace EthInapproximability.CurrentPaper.WeightedRawWords

open Turing BitMachineEncoding BitMachineStackEmbedding

noncomputable section

/-! ## The ordering bridge -/

theorem valueFrom_append (n : ℕ) (q r : List Bool) :
    MatrixBinaryAddress.valueFrom n (q ++ r) =
      MatrixBinaryAddress.valueFrom (MatrixBinaryAddress.valueFrom n q) r := by
  induction q generalizing n with
  | nil => rfl
  | cons b q ih => exact ih _

theorem valueFrom_bits_reverse (k : ℕ) :
    MatrixBinaryAddress.valueFrom 0 (Nat.bits k).reverse = k := by
  induction k using Nat.binaryRec' with
  | zero => simp [MatrixBinaryAddress.valueFrom]
  | bit b n h ih =>
      rw [Nat.bits_append_bit _ _ h, List.reverse_cons, valueFrom_append, ih]
      cases b <;> simp [MatrixBinaryAddress.valueFrom, MatrixBinaryAddress.bitVal, Nat.bit] <;>
        omega

/-! ## Reversal by transfer -/

def transferProgram (src dst : Global) : Unit → TM2.Stmt (fun _ : Global => Bool) Unit (Option Bool)
  | () => .pop src (fun _ b => b)
      (.branch Option.isSome
        (.push dst (fun v => v.getD false) (.goto (fun _ => ())))
        .halt)

theorem transfer_run (src dst : Global) (hsd : src ≠ dst) (q : List Bool)
    (S : Global → List Bool) (hs : S src = q) (v : Option Bool) :
    ((advance (transferProgram src dst))^[q.length + 1])
      (⟨some (), v, S⟩ : TM2.Cfg (fun _ : Global => Bool) Unit (Option Bool)) =
      ⟨none, none, Function.update (Function.update S src []) dst (q.reverse ++ S dst)⟩ := by
  induction q generalizing S v with
  | nil =>
      have h1 : advance (transferProgram src dst)
          (⟨some (), v, S⟩ : TM2.Cfg (fun _ : Global => Bool) Unit (Option Bool)) =
          ⟨none, none, Function.update S src []⟩ := by
        simp [advance, TM2.step, transferProgram, TM2.stepAux, hs]
      rw [List.length_nil, Nat.zero_add, Function.iterate_one, h1]
      congr 1
      funext j
      by_cases hj : j = dst
      · subst hj; simp [Function.update_apply, Ne.symm hsd]
      · simp [Function.update_apply, hj]
  | cons b q ih =>
      have h1 : advance (transferProgram src dst)
          (⟨some (), v, S⟩ : TM2.Cfg (fun _ : Global => Bool) Unit (Option Bool)) =
          ⟨some (), some b, Function.update (Function.update S src q) dst (b :: S dst)⟩ := by
        simp [advance, TM2.step, transferProgram, TM2.stepAux, hs, Function.update_apply,
          Ne.symm hsd]
      rw [List.length_cons, Function.iterate_succ_apply, h1,
        ih _ (by simp [Function.update_apply, hsd]) (some b)]
      congr 1
      funext j
      by_cases hj : j = dst
      · subst hj; simp [Function.update_apply, Ne.symm hsd]
      · by_cases hj' : j = src
        · subst hj'; simp [Function.update_apply, hsd]
        · simp [Function.update_apply, hj, hj']

/-! ## Embedded binary-to-unary conversion -/

def addrSlots : Fin 3 ↪ Global where
  toFun
    | 0 => aux .K
    | 1 => aux (.nat 1 0)
    | 2 => aux (.nat 1 1)
  inj' := by
    intro x y h
    fin_cases x <;> fin_cases y <;> simp_all [aux]

def addrProgram := fun l => stackStmt addrSlots (MatrixBinaryAddress.program l)

theorem addr_run (q : List Bool) (S : Global → List Bool) (hK : S (aux .K) = q)
    (h1 : S (aux (.nat 1 0)) = []) (h2 : S (aux (.nat 1 1)) = []) (s : Bool × Bool) :
    ((advance addrProgram)^[MatrixBinaryAddress.workFrom 0 q])
      (⟨some .readBit, s, S⟩ : TM2.Cfg (fun _ : Global => Bool) MatrixBinaryAddress.Label
        (Bool × Bool)) =
      ⟨none, (false, false),
        Function.update S (aux .K) (List.replicate (MatrixBinaryAddress.valueFrom 0 q) true)⟩ := by
  have hr := MatrixBinaryAddress.run_correct q 0 s
  have h := region_run addrSlots MatrixBinaryAddress.program _ _ _ hr S
    (by
      intro k
      fin_cases k <;> simp [MatrixBinaryAddress.cfg, MatrixBinaryAddress.stackContents,
        addrSlots, hK, h1, h2])
  refine h.trans ?_
  simp only [MatrixBinaryAddress.cfg]
  congr 1
  have hloc : MatrixBinaryAddress.stackContents
      (List.replicate (MatrixBinaryAddress.valueFrom 0 q) true) [] [] =
      Function.update (fun k => S (addrSlots k)) 0
        (List.replicate (MatrixBinaryAddress.valueFrom 0 q) true) := by
    funext k
    fin_cases k <;> simp [MatrixBinaryAddress.stackContents, addrSlots, h1, h2]
  rw [hloc, bank_update, bank_restrict]
  rfl

/-! ## Bits cell to unary master `K` -/

def bitsCell : Global := aux (.nat 2 0)

def fuelProgram := BitMachineRawSequence.program (transferProgram bitsCell (aux .K)) addrProgram
  .readBit none (false, false)

def fuelBound (k : ℕ) : ℕ :=
  ((Nat.bits k).length + 1) + (4 * k + 3 * (Nat.bits k).length + 2) + 1

theorem fuel_run (k : ℕ) (S : Global → List Bool) (hb : S bitsCell = Nat.bits k)
    (hK : S (aux .K) = []) (h1 : S (aux (.nat 1 0)) = []) (h2 : S (aux (.nat 1 1)) = []) :
    ∃ t ≤ fuelBound k,
      ((advance fuelProgram)^[t])
        (⟨some (BitMachineRawSequence.leftLabel ()), (none, (false, false)), S⟩ :
          TM2.Cfg (fun _ : Global => Bool) _ _) =
        ⟨none, (none, (false, false)),
          Function.update (Function.update S bitsCell []) (aux .K)
            (List.replicate k true)⟩ := by
  have hne : bitsCell ≠ aux .K := by simp [bitsCell, aux]
  have s1 := transfer_run bitsCell (aux .K) hne (Nat.bits k) S hb none
  rw [hK, List.append_nil] at s1
  set S1 := Function.update (Function.update S bitsCell []) (aux .K) (Nat.bits k).reverse
    with hS1
  have s2 := addr_run (Nat.bits k).reverse S1 (by simp [hS1])
    (by simp [hS1, bitsCell, aux]; exact h1) (by simp [hS1, bitsCell, aux]; exact h2)
    (false, false)
  rw [valueFrom_bits_reverse, hS1, Function.update_idem] at s2
  obtain ⟨t, ht, h⟩ := BitMachineRawSequence.runs (transferProgram bitsCell (aux .K))
    addrProgram () .readBit none none (false, false) (false, false) S S1 _ _ _ s1 s2
  refine ⟨t, ?_, h⟩
  have hw := MatrixBinaryAddress.workFrom_bound 0 (Nat.bits k).reverse
  rw [valueFrom_bits_reverse, List.length_reverse] at hw
  unfold fuelBound
  omega

#print axioms valueFrom_bits_reverse
#print axioms transfer_run
#print axioms addr_run
#print axioms fuel_run

end
end EthInapproximability.CurrentPaper.WeightedRawWords
