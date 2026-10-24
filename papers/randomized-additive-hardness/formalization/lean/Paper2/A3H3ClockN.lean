import Paper2.A3N
import Paper2.A3H3ClockB

/-!
# Unit 3 endpoint (H_A3 closure), segment 2 addendum: the none-outcome branch clock `clockN` in H_A3 shape

Lane `owner:a-h-a3-assembly-3` (private, 26 September 2026). Pure arithmetic.

`NoneOut.clockN` is the literal clock of the frozen private lane a-h-a3-assembly-owner-2 theorems
`NoneOut.none_run` / `none_run_canonical` (count copies, the admitted threshold producer, the admitted
generator-with-fallback program `SuccessOrient.program` with clock `SamplerFallbackJoin.clock`, charged header
copies, the admitted header). At the actual schedule (`L = clog₂ n`, `Checks`) it is at most
`(12·coef + 229)·(n+2)^(EN(k+1))`, `EN = 6(coef + 60) + 2·noPreloadExponent + 116`.
-/

set_option maxHeartbeats 4000000

namespace Paper2.A3Assembly.Clocks

open EthInapproximability.CurrentPaper
open Paper2.SourceProfileParameters Paper2.ParameterizedCanonicalSource

/-- The none-outcome exponent. -/
noncomputable def EN : ℕ :=
  6 * (UnaryBinaryEncoding.coefficient + 60) + 2 * FallbackNoPreloadRun.noPreloadExponent + 116

theorem none_header_eq (p s q₂ w Q k mX mY : ℕ) :
    NoneOut.headerClockN p s q₂ w Q k mX mY = headerClock mX mY (NoneOut.thrV p s q₂ w Q k) := rfl

/-- **(S-none, whole branch)** The literal clock of `NoneOut.none_run_canonical` at the actual schedule,
in H_A3 shape. -/
theorem clockN_HA3 {n m : ℕ} [NeZero n] (Δ : ℕ) (γ : ℚ)
    (hc : Paper2.CompletePublicScheduleScratch.Checks
      (V := Fin n) (E := Fin m) (Nat.clog 2 n) Δ γ) (k : ℕ) :
    NoneOut.clockN n (LookupSeed.width (Nat.clog 2 n)) (width (Nat.clog 2 n))
        (width (Nat.clog 2 n) - 2) (outerWidth (Nat.clog 2 n)) (restorationWidth (Nat.clog 2 n))
        (coverWidth n m (Nat.clog 2 n) Δ γ) k
        (SourceRecursiveNoSampling.sourceRows (Nat.clog 2 n) (restorationDepth (Nat.clog 2 n))
          (coverDepth n m (Nat.clog 2 n) Δ γ) k)
        (SourceRecursiveNoSampling.sourceCols (Nat.clog 2 n) (restorationDepth (Nat.clog 2 n))
          (coverDepth n m (Nat.clog 2 n) Δ γ) k) ≤
      (12 * UnaryBinaryEncoding.coefficient + 229) * (n + 2) ^ (EN * (k + 1)) := by
  obtain ⟨hn, hp, hs, hq₁, hq₂, hw, hQ, hm, hL⟩ :=
    Paper2.SuccessClock.scalar_caps (n := n) (m := m) (Nat.clog 2 n) Δ γ hc
  obtain ⟨hmX, hmY⟩ := Paper2.SuccessClock.dims_cap (n := n) (m := m) (Nat.clog 2 n) Δ γ hc k
  have hb := budget_cap (n := n) (m := m) Δ γ hc k
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
  have hthr := ThrJoin.budget_eq n m Δ γ k
  dsimp only at hthr
  have hthrV : NoneOut.thrV (LookupSeed.width (Nat.clog 2 n)) (width (Nat.clog 2 n))
      (outerWidth (Nat.clog 2 n)) (restorationWidth (Nat.clog 2 n))
      (coverWidth n m (Nat.clog 2 n) Δ γ) k =
      SourceRecursiveNoSampling.sourceBudget (Nat.clog 2 n) (restorationDepth (Nat.clog 2 n))
        (coverDepth n m (Nat.clog 2 n) Δ γ) k := hthr
  -- threshold producer clock
  have hv : ∀ i, NoneOut.vv (LookupSeed.width (Nat.clog 2 n)) (width (Nat.clog 2 n))
      (outerWidth (Nat.clog 2 n)) (restorationWidth (Nat.clog 2 n))
      (coverWidth n m (Nat.clog 2 n) Δ γ) i ≤ X := by
    intro i; fin_cases i <;> simp [NoneOut.vv] <;> omega
  obtain ⟨hthrBd, _⟩ := Paper2.SuccessClock2Pre.thrBd_X k _ hX20 hco hv hkX
  -- sampler clock and header clock
  have hS := probe_clock_HA3 (n := n) (m := m) Δ γ hc k
  have hH := none_header_HA3 (n := n) (m := m) Δ γ hc k
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
      (outerWidth (Nat.clog 2 n)) (restorationWidth (Nat.clog 2 n))
      (coverWidth n m (Nat.clog 2 n) Δ γ) k
      (SourceRecursiveNoSampling.sourceRows (Nat.clog 2 n) (restorationDepth (Nat.clog 2 n))
        (coverDepth n m (Nat.clog 2 n) Δ γ) k)
      (SourceRecursiveNoSampling.sourceCols (Nat.clog 2 n) (restorationDepth (Nat.clog 2 n))
        (coverDepth n m (Nat.clog 2 n) Δ γ) k) ≤ 3 * X + X * X := by
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

end Paper2.A3Assembly.Clocks

#print axioms Paper2.A3Assembly.Clocks.none_header_eq
#print axioms Paper2.A3Assembly.Clocks.clockN_HA3
