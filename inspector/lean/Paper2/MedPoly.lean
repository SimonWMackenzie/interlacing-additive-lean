import Paper2.MedFinal

/-!
# WP-U18a (ii): the clock of the median machine is linear in its parts; `medAlg` is polynomial

Lane `owner:a-median-1` (private, 27 September 2026). Paper A, lock v12, I:117 ("a constant
number of independent calls"): the composed procedure stays polynomial.

`medClock_le`: `medClock n E C |w| s TE TC ≤ (|w| + s + TE + TC + 1) · Kc n E C` with a constant
`Kc` depending only on `n` and on the stack counts and push bounds of `E` and `C`.
`medAlg_polynomial`: if the estimator is polynomial (D-A1 `Polynomial` of lane a-model) and the
comparator clock `TC` is polynomially bounded, then `medAlg` is polynomial.
-/

namespace Paper2.MedianOwner.Final

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachine
open Paper2.MedianOwner Paper2.MedianOwner.Med
open Paper2.AModel (PrefixAlgorithm)
open Paper2.Unit4Shell.Amplification (reps)

/-- The coefficient of one round. -/
def bodyCoef (E C : Machine) : ℕ :=
  39 + 2 * (E.pushBound + 2) + (1 + (E.stackCount + 2) * (E.pushBound + 2) + E.stackCount + 4) +
    (1 + (C.stackCount + 2) * (E.pushBound + C.pushBound + 4) + C.stackCount + 4)

/-- The linear coefficient of the whole clock. -/
def Kc (n : ℕ) (E C : Machine) : ℕ := 160 + (n + 1) + (n + 1) * (bodyCoef E C + 3)

theorem bodyClock_le (E C : Machine) (wl s TE TC : ℕ) :
    bodyClock E C wl s TE TC ≤ (wl + s + TE + TC + 1) * bodyCoef E C := by
  set X := wl + s + TE + TC + 1 with hX
  have hX1 : 1 ≤ X := by linarith
  have hTE : TE * E.pushBound ≤ X * E.pushBound := Nat.mul_le_mul_right E.pushBound (by linarith)
  have hTC : TC * C.pushBound ≤ X * C.pushBound := Nat.mul_le_mul_right C.pushBound (by linarith)
  -- the output bound
  have hLO : outBound E wl s TE ≤ X * (E.pushBound + 2) := by
    unfold outBound
    have : X * (E.pushBound + 2) = X * E.pushBound + 2 * X := by ring
    linarith
  -- the E call
  have hRBE : BitMachineIteration.roundBound E (2 * wl + 1 + s) TE ≤
      X * (1 + (E.stackCount + 2) * (E.pushBound + 2) + E.stackCount + 4) := by
    unfold BitMachineIteration.roundBound
    have h1 : (E.stackCount + 2) * (2 * wl + 1 + s + TE * E.pushBound) ≤ (E.stackCount + 2) * (X * (E.pushBound + 2)) := by
      apply Nat.mul_le_mul_left
      have : X * (E.pushBound + 2) = X * E.pushBound + 2 * X := by ring
      linarith
    have h2 : E.stackCount + 4 ≤ (E.stackCount + 4) * X := Nat.le_mul_of_pos_right _ hX1
    have e : X * (1 + (E.stackCount + 2) * (E.pushBound + 2) + E.stackCount + 4) = X + (E.stackCount + 2) * (X * (E.pushBound + 2)) + (E.stackCount + 4) * X := by
      ring
    rw [e]
    show TE + (E.stackCount + 2) * (2 * wl + 1 + s + TE * E.pushBound) + E.stackCount + 4 ≤ _
    linarith
  -- the C call
  have hRBC : BitMachineIteration.roundBound C (2 * wl + 1 + outBound E wl s TE) TC ≤
      X * (1 + (C.stackCount + 2) * (E.pushBound + C.pushBound + 4) + C.stackCount + 4) := by
    unfold BitMachineIteration.roundBound
    have h1 : (C.stackCount + 2) * (2 * wl + 1 + outBound E wl s TE + TC * C.pushBound) ≤
        (C.stackCount + 2) * (X * (E.pushBound + C.pushBound + 4)) := by
      apply Nat.mul_le_mul_left
      have : X * (E.pushBound + C.pushBound + 4) = X * (E.pushBound + 2) + X * C.pushBound + 2 * X := by ring
      show 2 * wl + 1 + outBound E wl s TE + TC * C.pushBound ≤ _
      linarith
    have h2 : C.stackCount + 4 ≤ (C.stackCount + 4) * X := Nat.le_mul_of_pos_right _ hX1
    have e : X * (1 + (C.stackCount + 2) * (E.pushBound + C.pushBound + 4) + C.stackCount + 4) =
        X + (C.stackCount + 2) * (X * (E.pushBound + C.pushBound + 4)) + (C.stackCount + 4) * X := by ring
    rw [e]
    show TC + (C.stackCount + 2) * (2 * wl + 1 + outBound E wl s TE + TC * C.pushBound) + C.stackCount + 4 ≤ _
    linarith
  unfold bodyClock roundClock
  have e : X * bodyCoef E C = 39 * X + 2 * (X * (E.pushBound + 2)) + X * (1 + (E.stackCount + 2) * (E.pushBound + 2) + E.stackCount + 4) +
      X * (1 + (C.stackCount + 2) * (E.pushBound + C.pushBound + 4) + C.stackCount + 4) := by
    unfold bodyCoef; ring
  rw [e]
  have h29 : 29 ≤ 29 * X := Nat.le_mul_of_pos_right _ hX1
  linarith

/-- **The clock is linear in its parts**, with a constant depending only on `n`, `E`, `C`. -/
theorem medClock_le (n : ℕ) (E C : Machine) (wl s TE TC : ℕ) :
    medClock n E C wl s TE TC ≤ (wl + s + TE + TC + 1) * Kc n E C := by
  set X := wl + s + TE + TC + 1 with hX
  have hX1 : 1 ≤ X := by omega
  have hb := bodyClock_le E C wl s TE TC
  rw [← hX] at hb
  unfold medClock
  have h1 : (n + 1) * (bodyClock E C wl s TE TC + 2) ≤ (n + 1) * (X * bodyCoef E C + 2 * X) :=
    Nat.mul_le_mul_left _ (by omega)
  have h2 : (n + 1) * s ≤ (n + 1) * X := Nat.mul_le_mul_left _ (by omega)
  have h3 : n + 2 ≤ (n + 2) * X := Nat.le_mul_of_pos_right _ hX1
  have h4 : 160 ≤ 160 * X := Nat.le_mul_of_pos_right _ hX1
  have e : X * Kc n E C = 160 * X + (n + 1) * X + (n + 1) * (X * bodyCoef E C + 2 * X) +
      (n + 1) * X := by
    unfold Kc; ring
  rw [e]
  linarith

variable (A : PrefixAlgorithm) (C : Machine) (thr : List Bool → ℝ) (TC : List Bool → ℕ)

/-- **`medAlg` is polynomial** (D-A1 `Polynomial` of lane a-model) when the estimator is polynomial
and the comparator clock is polynomially bounded. -/
theorem medAlg_polynomial (hC : CmpSpec A C thr TC) (hA : A.Polynomial)
    (hT : ∃ cT dT : ℕ, ∀ w : List Bool, TC w ≤ cT * (w.length + 1) ^ dT) :
    (medAlg A C thr TC hC).Polynomial := by
  obtain ⟨cA, dA, hA⟩ := hA
  obtain ⟨cT, dT, hT⟩ := hT
  refine ⟨(3 + 2 * cA + cT) * Kc 146 A.machine C + reps * cA, dA + dT + 1, fun w => ?_⟩
  set N := w.length + 1
  have hN : 1 ≤ N := by omega
  set D := dA + dT + 1
  have hpA : N ^ dA ≤ N ^ D := Nat.pow_le_pow_right hN (by omega)
  have hpT : N ^ dT ≤ N ^ D := Nat.pow_le_pow_right hN (by omega)
  have hp1 : N ≤ N ^ D := by
    calc N = N ^ 1 := (pow_one N).symm
      _ ≤ N ^ D := Nat.pow_le_pow_right hN (by omega)
  have hs := (hA w).1
  have ht := (hA w).2
  have hc := hT w
  have hsD : A.tapeLength w.length ≤ cA * N ^ D := hs.trans (Nat.mul_le_mul_left _ hpA)
  have htD : A.time w ≤ cA * N ^ D := ht.trans (Nat.mul_le_mul_left _ hpA)
  have hcD : TC w ≤ cT * N ^ D := hc.trans (Nat.mul_le_mul_left _ hpT)
  have hX : w.length + A.tapeLength w.length + A.time w + TC w + 1 ≤ (3 + 2 * cA + cT) * N ^ D := by
    have e : (3 + 2 * cA + cT) * N ^ D = 3 * N ^ D + cA * N ^ D + cA * N ^ D + cT * N ^ D := by ring
    omega
  constructor
  · show reps * A.tapeLength w.length ≤ _
    have : reps * A.tapeLength w.length ≤ reps * (cA * N ^ D) := Nat.mul_le_mul_left _ hsD
    have e : ((3 + 2 * cA + cT) * Kc 146 A.machine C + reps * cA) * N ^ D =
        (3 + 2 * cA + cT) * Kc 146 A.machine C * N ^ D + reps * (cA * N ^ D) := by ring
    rw [e]
    exact this.trans (Nat.le_add_left _ _)
  · show medClock 146 A.machine C w.length (A.tapeLength w.length) (A.time w) (TC w) ≤ _
    have hm := medClock_le 146 A.machine C w.length (A.tapeLength w.length) (A.time w) (TC w)
    have hm2 : (w.length + A.tapeLength w.length + A.time w + TC w + 1) * Kc 146 A.machine C ≤
        (3 + 2 * cA + cT) * N ^ D * Kc 146 A.machine C := Nat.mul_le_mul_right _ hX
    have e : ((3 + 2 * cA + cT) * Kc 146 A.machine C + reps * cA) * N ^ D =
        (3 + 2 * cA + cT) * N ^ D * Kc 146 A.machine C + reps * cA * N ^ D := by ring
    rw [e]
    exact hm.trans (hm2.trans (Nat.le_add_right _ _))

end Paper2.MedianOwner.Final
