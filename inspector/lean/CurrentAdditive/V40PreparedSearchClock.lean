import CurrentAdditive.V40ActualPreparedSearch
import CurrentAdditive.V40SearchInitialization

set_option autoImplicit false
set_option maxHeartbeats 200000

namespace CurrentAdditive.V40ActualPreparedSearch

open V39GeneratedConstruction V38Schedule
open CurrentAdditive.MinimumRatioContext
noncomputable section

attribute [local irreducible] D22GeneratedTestMachine.testMachine
  D22GeneratedTestMachine.clockCoefficient D22GeneratedTestMachine.clockDegree

def loopCap (p : SourceConstants) (floor n m : Nat) : Nat :=
  (publicUpperLog p floor n - V40DeterministicBoundedSearch.start floor n + 1) *
    (stepCap p n m (publicUpperLog p floor n) + 1)

private theorem stepCap_eq (p : SourceConstants) (n m U : Nat) :
    stepCap p n m U =
      (8 + (tester p).stackCount) * requestCap n m U +
      (1 + (2 + (tester p).stackCount) * (tester p).pushBound) * testCap p n m U +
      (tester p).stackCount + 21 := by
  simp only [stepCap, MachineInvokeFull.uniformBound, List.length_replicate]
  ring

/-- The complete repeated actual-test bound is polynomial in the ORIGINAL
floor,n,m packet. The cutoff constants and the fixed test machine precede
all inputs; failed candidates are included. -/
theorem loopCap_polynomial (p : SourceConstants) :
    ∃ C e : Nat, ∀ floor n m, 0 < n →
      loopCap p floor n m ≤ C * ((V40SearchInitialization.input floor n m).length + 1) ^ e := by
  let K := generatedN (GeneratedCutoff.cutoffLog p.degree p.deletion)
  let A := 4 * K + 16
  let d := D22GeneratedTestMachine.clockDegree p
  let Ct := D22GeneratedTestMachine.clockCoefficient p * A ^ d
  let Cb := (8 + (tester p).stackCount) * A +
    (1 + (2 + (tester p).stackCount) * (tester p).pushBound) * Ct +
      (tester p).stackCount + 21
  refine ⟨A * (Cb + 1), d + 2, ?_⟩
  intro floor n m hn
  let U := publicUpperLog p floor n
  let Z := (V40SearchInitialization.input floor n m).length + 1
  let R := Z ^ (d + 1)
  have hZ1 : 1 ≤ Z := by dsimp [Z]; omega
  have hfn : floor + n ≤ Z := by simp only [Z, V40SearchInitialization.input_length]; omega
  have hnm : n + m ≤ Z := by simp only [Z, V40SearchInitialization.input_length]; omega
  have hKS : K ≤ K * Z := by simpa using Nat.mul_le_mul_left K hZ1
  have hmax : max floor n ≤ floor + n := max_le (by omega) (by omega)
  have hmaxK : max (max floor n) K ≤ max floor n + K := max_le (by omega) (by omega)
  have hdy := V40DeterministicBoundedSearch.every_candidate_size p floor n U hn le_rfl
  change 2 ^ U ≤ 2 * max (max floor n) K at hdy
  have hdy' : 2 ^ U ≤ 2 * (floor + n + K) := by omega
  have hUpow : U ≤ 2 ^ U := Nat.le_of_lt Nat.lt_two_pow_self
  have harg : 2 ^ U + n + m + 1 ≤ A * Z := by
    dsimp [A]
    nlinarith only [hdy', hfn, hnm, hKS, hZ1]
  have hreq : requestCap n m U ≤ A * Z := by
    dsimp [requestCap, A]
    nlinarith only [hdy', hUpow, hfn, hnm, hKS, hZ1]
  have hcount : U + 1 ≤ A * Z := by
    dsimp [A]
    nlinarith only [hdy', hUpow, hfn, hKS, hZ1]
  have hR1 : 1 ≤ R := Nat.one_le_pow _ _ hZ1
  have hZR : Z ≤ R := by simpa [R] using Nat.pow_le_pow_right hZ1 (by omega : 1 ≤ d + 1)
  have hdR : Z ^ d ≤ R := Nat.pow_le_pow_right hZ1 (by omega)
  have hT : testCap p n m U ≤ Ct * R := by
    calc
      _ ≤ D22GeneratedTestMachine.clockCoefficient p * (A * Z) ^ d := by
        change D22GeneratedTestMachine.clockCoefficient p * (2 ^ U + n + m + 1) ^ d ≤ _
        gcongr
      _ = Ct * Z ^ d := by rw [mul_pow]; dsimp [Ct]; ring
      _ ≤ Ct * R := Nat.mul_le_mul_left _ hdR
  have hreqR : requestCap n m U ≤ A * R := hreq.trans (Nat.mul_le_mul_left A hZR)
  have hstep : stepCap p n m U ≤ Cb * R := by
    rw [stepCap_eq]
    have ha := Nat.mul_le_mul_left (8 + (tester p).stackCount) hreqR
    have hb := Nat.mul_le_mul_left
      (1 + (2 + (tester p).stackCount) * (tester p).pushBound) hT
    have hc := Nat.mul_le_mul_left ((tester p).stackCount + 21) hR1
    dsimp [Cb]
    nlinarith only [ha, hb, hc]
  have hsteps : stepCap p n m U + 1 ≤ (Cb + 1) * R := by nlinarith only [hstep, hR1]
  have hnum : U - V40DeterministicBoundedSearch.start floor n + 1 ≤ A * Z := by omega
  change (U - V40DeterministicBoundedSearch.start floor n + 1) * (stepCap p n m U + 1) ≤ _
  calc
    _ ≤ (A * Z) * ((Cb + 1) * R) := Nat.mul_le_mul hnum hsteps
    _ = (A * (Cb + 1)) * Z ^ (d + 2) := by
      dsimp [R]
      rw [show d + 2 = 1 + (d + 1) by omega, pow_add, pow_one]
      ring

end
end CurrentAdditive.V40ActualPreparedSearch
