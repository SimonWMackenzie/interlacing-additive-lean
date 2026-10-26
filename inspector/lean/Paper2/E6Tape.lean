import Paper2.E6Red
-- a-eth-owner-6 copy of frozen a-eth-owner-5/E5Tape.lean (SHA-256 58987427d8b0e2eb1fc577f3a17c5d52c7ebce75d3a3c2a3233e3a793c35d8cd); import lines renamed only.

/-! a-eth-owner-5 copy of frozen `a-eth-owner-4/E4Tape.lean` (SHA-256 cdba86ed503a0c3793fe9dbd4b854c9f3ed4bf5559975dca0353345c0235af09). Changes: import lines renamed E4Budget/E4Red/E4Hd/E4Size -> E5Budget/E5Red/E5Hd/E5Size; nothing else. -/

/-!
# Paper A (lock v12), lane `owner:a-eth-4`, segment 4 (partial, 4b machine): the R20 tape length of the composite decider

`tapeCA c a m = 2^(e0 (m + c) + a)`: ONE fixed length machine `CAMachine c a` prints `1^(tapeCA c a m)` from `1^m`
within `CAtime c a m ≤ (BT + 20) (c + 1)^2 (m + tapeCA c a m + 1)^2` (the R20 `lenPoly` shape), `tapeCA c a` is
`Subexp`, and at `c = phiLen N₁`, `a = 8 + cR` the tape of EVERY word `w` covers the reduction cut request of the routed
formula PLUS a classifier block of `cR · expLen N'` bits (`blocks_fit`), the block size that `E4Size.classifier_fit`
shows is enough for a selected classifier with tape constant `cR` on every printed header word.
No ledger row is closed. Nothing here is admitted.
-/

noncomputable section

namespace Paper2.AEth4

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open Paper2.Unit4Shell
open Paper2.Unit4Shell.Loops
open Paper2.Unit4Shell.KofLoops
open Paper2.AEth (llog expExp expLen Subexp loglogMachine le_llog llog_le loglog_outputs)

namespace PlusK

inductive QL
  | q1 | done
  deriving DecidableEq, Fintype

abbrev Stack := Fin 1
abbrev Control := Option Bool × Unit

def program (a : ℕ) : QL → TM2.Stmt (fun _ : Stack => Bool) QL Control
  | .q1 => pushTrues 0 a (.goto fun _ => QL.done)
  | .done => .halt

/-- `1^e ↦ 1^(e+a)` for the fixed constant `a`. -/
def machine (a : ℕ) : BitMachine.Machine :=
  ofFinite (0 : Stack) (0 : Stack) QL.q1 ((none, ()) : Control) (program a)

theorem outputs (a e : ℕ) :
    (machine a).OutputsWithin (List.replicate e true) (List.replicate (e + a) true) 2 := by
  let S0 : Stack → List Bool := fun j => if j = 0 then List.replicate e true else []
  have e1 : advance (program a) ⟨some QL.q1, ((none, ()) : Control), S0⟩ =
      ⟨some QL.done, ((none, ()) : Control),
        Function.update S0 0 (List.replicate a true ++ S0 0)⟩ := by
    simp only [advance, TM2.step, program, Option.getD_some]
    rw [stepAux_pushTrues]
    simp [TM2.stepAux]
  set S1 := Function.update S0 0 (List.replicate a true ++ S0 0) with hS1
  have e2 := halt_step (program a) QL.done rfl (none, ()) S1
  have hrun := iter_chain (one_step e1) (one_step e2)
  have hraw : rawInit (0 : Stack) QL.q1 ((none, ()) : Control) (List.replicate e true) =
      ⟨some QL.q1, (none, ()), S0⟩ := rfl
  rw [← hraw] at hrun
  refine outputsWithin_of_raw_run (0 : Stack) (0 : Stack) QL.q1 ((none, ()) : Control)
    (program a) _ _ 2 2 le_rfl (by rw [hrun]) ?_
  rw [hrun]
  simp only [hS1, Function.update_self]
  rw [Nat.add_comm e a, List.replicate_add]
  simp [S0]

end PlusK

/-- `1^m ↦ 1^(2^(e0 m + a))`. -/
def TLKMachine (a : ℕ) : BitMachine.Machine :=
  BitMachineComposition.composition WrapDup.machine
    (BitMachineComposition.composition (Paper2.Unit4Shell.PairMap.machine llogPred)
      (BitMachineComposition.composition Swap.machine
        (BitMachineComposition.composition DivFloor.machine
          (BitMachineComposition.composition (PlusK.machine a) MatrixUnaryPower.machine))))

def TLKtime (a m : ℕ) : ℕ := BT * (m + 1) ^ 2 + 20 * 2 ^ (e0 m + a)

theorem TLKMachine_outputs (a m : ℕ) :
    (TLKMachine a).OutputsWithin (List.replicate m true) (List.replicate (2 ^ (e0 m + a)) true)
      (TLKtime a m) := by
  set C1 := Nat.clog 2 m with hC1
  set Q := llog m - 1 with hQdef
  set F4 : List Bool := [false, false, false, false] with hF4
  have h2 := WrapDup.machine_outputs m
  have hout : WrapDup.out m = EncodedComplexity.pair (List.replicate m true)
      (EncodedComplexity.pair (List.replicate m true) F4) := by
    simp [WrapDup.out, EncodedComplexity.pair, hF4]
  rw [hout] at h2
  have hlp := BitMachineComposition.composition_outputsWithin loglogMachine Pred.machine
    (loglog_outputs m) (Pred.outputs (llog m))
  have h3 := Paper2.Unit4Shell.PairMap.machine_outputs (M := llogPred)
    (List.replicate m true) (List.replicate Q true)
    (EncodedComplexity.pair (List.replicate m true) F4) _ hlp
  have h4 := Swap.machine_outputs (List.replicate Q true) (List.replicate m true) F4
  rw [← DivFloor.packedInput_eq m Q] at h4
  have h5 := DivFloor.outputs m Q
  have h6 := PlusK.outputs a (m / Q)
  have h7 := MatrixUnaryPower.outputs (List.replicate (m / Q + a) true)
  rw [List.length_replicate] at h7
  have hC := BitMachineComposition.composition_outputsWithin _ _ h2
    (BitMachineComposition.composition_outputsWithin _ _ h3
      (BitMachineComposition.composition_outputsWithin _ _ h4
        (BitMachineComposition.composition_outputsWithin _ _ h5
          (BitMachineComposition.composition_outputsWithin _ _ h6 h7))))
  have hE : 2 ^ (m / Q + a) = 2 ^ (e0 m + a) := rfl
  rw [hE] at hC
  apply BitMachine.outputsWithin_mono _ hC
  have hin := DivFloor.packedInput_length m Q
  rw [hin]
  simp only [List.length_replicate, EncodedComplexity.pair_length, hF4, List.length_cons,
    List.length_nil]
  have hC1m : C1 ≤ m := Paper2.Unit4Shell.KofFront.clog_le_self m
  have hLm : llog m ≤ m := llog_le m
  have hQm : Q ≤ m := by omega
  have hqm : m / Q ≤ m := Nat.div_le_self m Q
  have hq2 : m / Q + a < 2 ^ (m / Q + a) := Nat.lt_two_pow_self
  rw [hE] at hq2
  have hsq : (C1 + 1) ^ 2 ≤ (m + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have hm1 : m + 1 ≤ (m + 1) ^ 2 := by nlinarith
  have hU := Nat.mul_le_mul_left (UnaryBinaryEncoding.coefficient + 6) hsq
  unfold TLKtime BT
  nlinarith

/-- The carrier tape length. -/
def tapeCA (c a m : ℕ) : ℕ := 2 ^ (e0 (m + c) + a)

/-- THE fixed length machine of the carrier: `1^m ↦ 1^(tapeCA c a m)`. -/
def CAMachine (c a : ℕ) : BitMachine.Machine :=
  BitMachineComposition.composition (PlusK.machine c) (TLKMachine a)

def CAtime (c a m : ℕ) : ℕ := 2 + 2 * (m + c) + 2 + TLKtime a (m + c)

theorem CAMachine_outputs (c a m : ℕ) :
    (CAMachine c a).OutputsWithin (List.replicate m true) (List.replicate (tapeCA c a m) true)
      (CAtime c a m) := by
  have h1 := PlusK.outputs c m
  have h2 := TLKMachine_outputs a (m + c)
  have hC := BitMachineComposition.composition_outputsWithin _ _ h1 h2
  simpa [CAtime, tapeCA, List.length_replicate] using hC

/-- **The R20 `lenPoly` shape.** -/
theorem CAtime_poly (c a m : ℕ) :
    CAtime c a m ≤ ((BT + 30) * (c + 1) ^ 2) * (m + tapeCA c a m + 1) ^ 2 := by
  unfold CAtime TLKtime
  set T := tapeCA c a m with hT
  have hT' : 2 ^ (e0 (m + c) + a) = T := rfl
  rw [hT']
  set Z := m + T + 1 with hZ
  have h1 : (m + c + 1) ^ 2 ≤ (c + 1) ^ 2 * Z ^ 2 := by
    have : m + c + 1 ≤ (c + 1) * Z := by nlinarith
    calc (m + c + 1) ^ 2 ≤ ((c + 1) * Z) ^ 2 := Nat.pow_le_pow_left this 2
      _ = (c + 1) ^ 2 * Z ^ 2 := mul_pow _ _ _
  have hZ1 : 1 ≤ Z := by omega
  have hZ2 : Z ≤ Z ^ 2 := Nat.le_self_pow two_ne_zero _
  have hc1 : 1 ≤ (c + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have hTZ : T ≤ (c + 1) ^ 2 * Z ^ 2 := by
    have : T ≤ Z ^ 2 := by omega
    exact this.trans (Nat.le_mul_of_pos_left _ (by omega))
  have hlin : 2 + 2 * (m + c) + 2 ≤ 6 * ((c + 1) ^ 2 * Z ^ 2) := by
    have : 2 + 2 * (m + c) + 2 ≤ 4 * (m + c + 1) := by omega
    have h2 : m + c + 1 ≤ (m + c + 1) ^ 2 := Nat.le_self_pow two_ne_zero _
    omega
  have hB := Nat.mul_le_mul_left BT h1
  nlinarith

/-- **The carrier tape length is subexponential.** -/
theorem tapeCA_subexp (c a : ℕ) : Subexp (tapeCA c a) := by
  intro ε hε
  obtain ⟨C, d, m₀, h⟩ := TL_subexp ε hε
  refine ⟨C * 2 ^ a * ⌈(2 : ℝ) ^ (ε * c)⌉₊ * (c + 1) ^ d, d, m₀, fun m hm => ?_⟩
  have hm' := h (m + c) (by omega)
  have hTL : tapeCA c a m * 2 ^ 8 = TL (m + c) * 2 ^ a := by
    unfold tapeCA TL
    rw [← pow_add, ← pow_add]
    ring_nf
  have hsplit : ⌈(2 : ℝ) ^ (ε * ((m + c : ℕ) : ℝ))⌉₊ ≤
      ⌈(2 : ℝ) ^ (ε * c)⌉₊ * ⌈(2 : ℝ) ^ (ε * m)⌉₊ := by
    have hmul : (2 : ℝ) ^ (ε * ((m + c : ℕ) : ℝ)) = (2 : ℝ) ^ (ε * c) * (2 : ℝ) ^ (ε * m) := by
      rw [← Real.rpow_add (by norm_num)]
      congr 1
      push_cast
      ring
    rw [hmul]
    have h0a : (0 : ℝ) ≤ (2 : ℝ) ^ (ε * c) := by positivity
    have h0b : (0 : ℝ) ≤ (2 : ℝ) ^ (ε * m) := by positivity
    exact Nat.ceil_le.mpr (by
      push_cast
      exact mul_le_mul (Nat.le_ceil _) (Nat.le_ceil _) h0b (by positivity))
  have hpoly : (m + c + 1) ^ d ≤ (c + 1) ^ d * (m + 1) ^ d := by
    rw [← mul_pow]
    exact Nat.pow_le_pow_left (by nlinarith) d
  have h256 : tapeCA c a m ≤ TL (m + c) * 2 ^ a := by
    have : tapeCA c a m ≤ tapeCA c a m * 2 ^ 8 := Nat.le_mul_of_pos_right _ (by positivity)
    omega
  calc tapeCA c a m ≤ TL (m + c) * 2 ^ a := h256
    _ ≤ (C * ⌈(2 : ℝ) ^ (ε * ((m + c : ℕ) : ℝ))⌉₊ * (m + c + 1) ^ d) * 2 ^ a :=
        Nat.mul_le_mul_right _ hm'
    _ ≤ (C * (⌈(2 : ℝ) ^ (ε * c)⌉₊ * ⌈(2 : ℝ) ^ (ε * m)⌉₊) * ((c + 1) ^ d * (m + 1) ^ d)) *
          2 ^ a := by
        apply Nat.mul_le_mul_right
        exact Nat.mul_le_mul (Nat.mul_le_mul_left _ hsplit) hpoly
    _ = C * 2 ^ a * ⌈(2 : ℝ) ^ (ε * c)⌉₊ * (c + 1) ^ d * ⌈(2 : ℝ) ^ (ε * m)⌉₊ * (m + 1) ^ d := by
        ring

/-- **Both blocks fit, on EVERY word.** At `c = phiLen N₁`, `a = 8 + cR`: the routed formula's cut request plus a
classifier block of `cR · expLen N'` bits is at most the carrier tape of `w`. -/
theorem blocks_fit (K : ℕ) {N₁ : ℕ} (hN₁ : 1 ≤ N₁) (cR : ℕ) (w : List Bool) :
    Paper2.AEth3.cutLen (routed4 K N₁ w) + cR * expLen (routed4 K N₁ w).variables ≤
      tapeCA (phiLen N₁) (8 + cR) w.length := by
  set m := w.length + phiLen N₁ with hm
  have h1 : Paper2.AEth3.cutLen (routed4 K N₁ w) ≤ 2 ^ (e0 m + 7) := cut4_fit K hN₁ w
  have hE := routed4_encode_length K hN₁ w
  have hNv := Paper2.AEth.encode_length_ge (routed4 K N₁ w)
  have h2 := expLen_fit (routed4 K N₁ w).variables m (by omega)
  have hc : cR ≤ 2 ^ cR := (Nat.lt_two_pow_self).le
  have h3 : cR * expLen (routed4 K N₁ w).variables ≤ 2 ^ cR * 2 ^ (e0 m + 4) :=
    Nat.mul_le_mul hc h2
  have h7 : 2 ^ (e0 m + 7) ≤ 2 ^ cR * 2 ^ (e0 m + 7) := Nat.le_mul_of_pos_left _ (by positivity)
  have h4 : 2 ^ (e0 m + 4) ≤ 2 ^ (e0 m + 7) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h5 : 2 ^ cR * 2 ^ (e0 m + 4) ≤ 2 ^ cR * 2 ^ (e0 m + 7) := Nat.mul_le_mul_left _ h4
  have hT : tapeCA (phiLen N₁) (8 + cR) w.length = 2 * (2 ^ cR * 2 ^ (e0 m + 7)) := by
    unfold tapeCA
    rw [← hm, ← pow_add, ← pow_succ']
    congr 1
    omega
  omega

end Paper2.AEth4

end

#print axioms Paper2.AEth4.PlusK.outputs
#print axioms Paper2.AEth4.TLKMachine_outputs
#print axioms Paper2.AEth4.CAMachine_outputs
#print axioms Paper2.AEth4.CAtime_poly
#print axioms Paper2.AEth4.tapeCA_subexp
#print axioms Paper2.AEth4.blocks_fit
