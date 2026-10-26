import CurrentAdditive.QuarticClockB
import Paper2.A3H3ClockN

set_option maxHeartbeats 4000000
set_option maxRecDepth 16384

namespace Paper2.CurrentAdditive.QuarticClockN

open EthInapproximability.CurrentPaper
open Paper2.SourceProfileParameters Paper2.ParameterizedCanonicalSource
open Paper2.A3Assembly.Clocks
open Paper2.A3Assembly
open CurrentAdditive.RandomizedSchedule

theorem clockN_HA3_27 {n m : ℕ} [NeZero n] (Δ : ℕ) (γ : ℚ)
    (hc : CurrentAdditive.QuarticSchedule.Checks27
      (V := Fin n) (Edges := Fin m) (Nat.clog 2 n) Δ γ) (k : ℕ) :
    NoneOut.clockN n (LookupSeed.width (Nat.clog 2 n)) (width (Nat.clog 2 n))
        (width (Nat.clog 2 n) - 2) (outerWidth (Nat.clog 2 n)) (width27 (Nat.clog 2 n))
        (Q27 (V := Fin n) (E := Fin m) (Nat.clog 2 n) γ Δ) k
        (SourceRecursiveNoSampling.sourceRows (Nat.clog 2 n) ((4 * RestorationWidthScheduleScratch.ell (Nat.clog 2 n)))
          ((q27 (V := Fin n) (E := Fin m) (Nat.clog 2 n) γ Δ)) k)
        (SourceRecursiveNoSampling.sourceCols (Nat.clog 2 n) ((4 * RestorationWidthScheduleScratch.ell (Nat.clog 2 n)))
          ((q27 (V := Fin n) (E := Fin m) (Nat.clog 2 n) γ Δ)) k) ≤
      (12 * UnaryBinaryEncoding.coefficient + 229) * (n + 2) ^ (EN * (k + 1)) := by
  obtain ⟨hn, hp, hs, hq₁, hq₂, hw, hQ, hm, hL⟩ :=
    QuarticClockCaps.scalar_caps27 (n := n) (m := m) (Nat.clog 2 n) Δ γ hc
  dsimp [Paper2.GeneratorPublicCap.publicCap] at hn hp hs hq₁ hq₂ hw hQ hm
  obtain ⟨hmX, hmY⟩ := QuarticClockCaps.dims_cap27 (n := n) (m := m) (Nat.clog 2 n) Δ γ hc k
  rw [Nat.mul_assoc] at hmX hmY
  have hb := QuarticClockB.budget_cap27 (n := n) (m := m) Δ γ hc k
  have hT1 : 1 ≤ (k + 1) * Nat.clog 2 n := by nlinarith
  have hkT : k + 1 ≤ (k + 1) * Nat.clog 2 n := by nlinarith
  have hLT : Nat.clog 2 n ≤ (k + 1) * Nat.clog 2 n := by nlinarith
  obtain ⟨X, hXdef⟩ : ∃ X, X = 2 ^ ((UnaryBinaryEncoding.coefficient + 60) *
      ((k + 1) * Nat.clog 2 n)) := ⟨_, rfl⟩
  have up : ∀ e, e ≤ (UnaryBinaryEncoding.coefficient + 60) * ((k + 1) * Nat.clog 2 n) →
      2 ^ e ≤ X := fun e he => hXdef ▸ Nat.pow_le_pow_right (by norm_num) he
  have hX20 : 1048576 ≤ X := by
    have := up 20 (by nlinarith); simpa using this
  have hco : UnaryBinaryEncoding.coefficient ≤ X :=
    (Paper2.SuccessClock.pw_const (c := UnaryBinaryEncoding.coefficient) hT1).trans
      (up _ (Nat.mul_le_mul_right _ (by omega)))
  have h7 : 2 ^ (7 * Nat.clog 2 n) ≤ X := up _ (by nlinarith)
  have h29 : 2 ^ (29 * ((k + 1) * Nat.clog 2 n)) ≤ X := up _ (by nlinarith)
  have hkX : k ≤ X := by
    have h1 : k < 2 ^ k := Nat.lt_two_pow_self
    have h2 : 2 ^ k ≤ X := up _ (by nlinarith)
    omega
  -- the threshold value is the source budget
  have hthr := QuarticConstructor.threshold27_eq_budget n m Δ γ k
  dsimp only at hthr
  have hthrV : NoneOut.thrV (LookupSeed.width (Nat.clog 2 n)) (width (Nat.clog 2 n))
      (outerWidth (Nat.clog 2 n)) (width27 (Nat.clog 2 n))
      (Q27 (V := Fin n) (E := Fin m) (Nat.clog 2 n) γ Δ) k =
      SourceRecursiveNoSampling.sourceBudget (Nat.clog 2 n) ((4 * RestorationWidthScheduleScratch.ell (Nat.clog 2 n)))
        ((q27 (V := Fin n) (E := Fin m) (Nat.clog 2 n) γ Δ)) k := hthr
  -- threshold producer clock
  have hv : ∀ i, NoneOut.vv (LookupSeed.width (Nat.clog 2 n)) (width (Nat.clog 2 n))
      (outerWidth (Nat.clog 2 n)) (width27 (Nat.clog 2 n))
      (Q27 (V := Fin n) (E := Fin m) (Nat.clog 2 n) γ Δ) i ≤ X := by
    intro i; fin_cases i <;> simp [NoneOut.vv] <;> omega
  obtain ⟨hthrBd, _⟩ := Paper2.SuccessClock2Pre.thrBd_X k _ hX20 hco hv hkX
  -- sampler clock and header clock
  have hS := QuarticClockB.probe_clock_HA3_27 (n := n) (m := m) Δ γ hc k
  have hH := QuarticClockB.none_header_HA3_27 (n := n) (m := m) Δ γ hc k
  rw [← hthrV] at hH
  rw [← none_header_eq] at hH
  -- the X^3 scale in H_A3 shape
  have hX3 : X ^ 3 ≤ (n + 2) ^ ((2 * (3 * (UnaryBinaryEncoding.coefficient + 60))) * (k + 1)) := by
    have e : X ^ 3 = 2 ^ ((3 * (UnaryBinaryEncoding.coefficient + 60)) * (k + 1) * Nat.clog 2 n) := by
      rw [hXdef, ← pow_mul, show (UnaryBinaryEncoding.coefficient + 60) * ((k + 1) * Nat.clog 2 n) * 3 =
        (3 * (UnaryBinaryEncoding.coefficient + 60)) * (k + 1) * Nat.clog 2 n by ring]
    rw [e]
    exact Paper2.A3Assembly.Clock.two_pow_mul_clog_le _ k n
  have hXX : X * X ≤ X ^ 3 := by
    have : X * X * 1 ≤ X * X * X := Nat.mul_le_mul_left _ (by omega)
    simpa [pow_succ, pow_two, Nat.mul_assoc] using this
  have hX1 : X ≤ X ^ 3 := by
    have : X * 1 ≤ X * (X * X) := Nat.mul_le_mul_left _ (by nlinarith)
    simpa [pow_succ, pow_two, Nat.mul_assoc] using this
  -- LN
  have hrc := Nat.mul_le_mul (hmX.trans h29) (hmY.trans h29)
  have hLN : NoneOut.LN (LookupSeed.width (Nat.clog 2 n)) (width (Nat.clog 2 n))
      (outerWidth (Nat.clog 2 n)) (width27 (Nat.clog 2 n))
      (Q27 (V := Fin n) (E := Fin m) (Nat.clog 2 n) γ Δ) k
      (SourceRecursiveNoSampling.sourceRows (Nat.clog 2 n) ((4 * RestorationWidthScheduleScratch.ell (Nat.clog 2 n)))
        ((q27 (V := Fin n) (E := Fin m) (Nat.clog 2 n) γ Δ)) k)
      (SourceRecursiveNoSampling.sourceCols (Nat.clog 2 n) ((4 * RestorationWidthScheduleScratch.ell (Nat.clog 2 n)))
        ((q27 (V := Fin n) (E := Fin m) (Nat.clog 2 n) γ Δ)) k) ≤ 3 * X + X * X := by
    unfold NoneOut.LN NoneOut.zeroTable
    rw [MatrixMaterialization.rowMajor_length, hthrV]
    omega
  -- exponents
  have hP1 : (n + 2) ^ ((2 * (3 * (UnaryBinaryEncoding.coefficient + 60))) * (k + 1)) ≤
      (n + 2) ^ (EN * (k + 1)) :=
    Nat.pow_le_pow_right (by omega) (Nat.mul_le_mul_right _ (by
      rw [show 2 * (3 * (UnaryBinaryEncoding.coefficient + 60)) =
        6 * (UnaryBinaryEncoding.coefficient + 60) by ring]
      unfold EN; exact Nat.le_add_right_of_le (Nat.le_add_right _ _)))
  have hP2 : (n + 2) ^ ((2 * FallbackNoPreloadRun.noPreloadExponent) * (k + 1)) ≤
      (n + 2) ^ (EN * (k + 1)) :=
    Nat.pow_le_pow_right (by omega) (Nat.mul_le_mul_right _ (by
      unfold EN; exact Nat.le_add_right_of_le (Nat.le_add_left _ _)))
  have hP3 : (n + 2) ^ (116 * (k + 1)) ≤ (n + 2) ^ (EN * (k + 1)) :=
    Nat.pow_le_pow_right (by omega) (Nat.mul_le_mul_right _ (by
      unfold EN; exact Nat.le_add_left _ _))
  have hH' := hH.trans (Nat.mul_le_mul_left (12 * UnaryBinaryEncoding.coefficient + 23) hP3)
  have e : (12 * UnaryBinaryEncoding.coefficient + 229) * (n + 2) ^ (EN * (k + 1)) =
      (12 * UnaryBinaryEncoding.coefficient + 23) * (n + 2) ^ (EN * (k + 1)) +
        206 * (n + 2) ^ (EN * (k + 1)) := by ring
  rw [e]
  unfold NoneOut.clockN
  have hSP := hS.trans (Nat.mul_le_mul_left 1 hP2)
  have hXP := hX3.trans hP1
  clear hP1 hP2 hP3 hH hS hX3 e hthr hthrV up hXdef
  generalize (n + 2) ^ (EN * (k + 1)) = P at *
  generalize X ^ 3 = X3 at *
  generalize UnaryBinaryEncoding.coefficient = c at *
  omega

end Paper2.CurrentAdditive.QuarticClockN

#print axioms Paper2.CurrentAdditive.QuarticClockN.clockN_HA3_27
