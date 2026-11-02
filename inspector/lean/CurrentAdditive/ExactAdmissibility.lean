import CurrentAdditive.RationalCount
import CurrentAdditive.DeterministicAdmissibility

/-! The literal v35 numerical comparisons, using the rational (unrounded)
moment coefficient and an executable integer exceptional count.  This is a
separate source-facing predicate: `Admissible` in v27 strengthens its moment
comparison by replacing `sourceC128` with `sourceC128Ceil`. -/
namespace CurrentAdditive.PublicScheduleExactAdmissibility

open CurrentAdditive.DeterministicParameters
open CurrentAdditive.DeterministicAdmissibility
open CurrentAdditive.PublicScheduleRationalCount

def exX (L : ℕ) : ℕ := exactCount (16 * L) 1
def exTheta (L : ℕ) : ℕ := exactCount (9 + 6 * L) 1
def exThetaQuarter (L : ℕ) : ℕ := exactCount (11 + 6 * L) 1
def exRho (L Δ : ℕ) (γ : ℚ) : ℕ :=
  exactCount L (δU L Δ γ / 2)
def exOwner (L Δ : ℕ) (γ : ℚ) : ℕ :=
  exactCount (9 + 6 * L) (η L Δ γ / 2)
def ownerExact (L Δ : ℕ) (γ : ℚ) : ℕ :=
  Nat.ceil ((16 * (exOwner L Δ γ : ℚ)) / 7)

private theorem x_dyadic (L : ℕ) :
    (x L : ℝ) = (2 : ℝ) ^ (-(16 * (L : ℝ))) := by
  simp only [x, Rat.cast_div, Rat.cast_one, Rat.cast_pow, N,
    Nat.cast_pow, Nat.cast_ofNat]
  rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
  change 1 / ((2 : ℝ) ^ L) ^ 16 = ((2 : ℝ) ^ (16 * (L : ℝ)))⁻¹
  rw [one_div, ← pow_mul]
  congr 1
  calc
    (2 : ℝ) ^ (L * 16) = (2 : ℝ) ^ ((L * 16 : ℕ) : ℝ) :=
      (Real.rpow_natCast _ _).symm
    _ = (2 : ℝ) ^ (16 * (L : ℝ)) := by congr 1; push_cast; ring

private theorem theta_dyadic (L : ℕ) :
    (θ L : ℝ) = (2 : ℝ) ^ (-((9 + 6 * L : ℕ) : ℝ)) := by
  unfold θ
  simp only [Rat.cast_div, Rat.cast_one, Rat.cast_mul, Rat.cast_natCast]
  rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_natCast]
  rw [one_div]
  congr 1
  norm_cast
  rw [Q_eq_pow, pow_add, pow_mul]
  norm_num

private theorem theta_quarter_dyadic (L : ℕ) :
    ((θ L / 4 : ℚ) : ℝ) = (2 : ℝ) ^ (-((11 + 6 * L : ℕ) : ℝ)) := by
  rw [Rat.cast_div, Rat.cast_ofNat, theta_dyadic]
  rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2),
    Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
  rw [Real.rpow_natCast, Real.rpow_natCast]
  rw [div_eq_inv_mul, ← mul_inv_rev]
  congr 1
  rw [pow_add, pow_add]
  norm_num
  ring

private theorem rho_dyadic (L : ℕ) :
    (ρ L : ℝ) = (2 : ℝ) ^ (-(L : ℝ)) := by
  unfold ρ
  simp only [Rat.cast_div, Rat.cast_one, Rat.cast_natCast]
  rw [Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_natCast]
  rw [one_div]
  congr 1
  simp [N]

theorem exX_eq_source (L : ℕ) :
    exX L = CurrentAdditive.conditioningExceptionCount (x L : ℝ) 1 := by
  rw [exX, x_dyadic]
  simpa only [Rat.cast_one, Nat.cast_mul, Nat.cast_ofNat] using
    exactCount_eq_source (16 * L) 1 (by norm_num)

theorem exTheta_eq_source (L : ℕ) :
    exTheta L = CurrentAdditive.conditioningExceptionCount (θ L : ℝ) 1 := by
  rw [exTheta, theta_dyadic]
  simpa only [Rat.cast_one] using exactCount_eq_source (9 + 6 * L) 1 (by norm_num)

theorem exThetaQuarter_eq_source (L : ℕ) :
    exThetaQuarter L = CurrentAdditive.conditioningExceptionCount
      ((θ L / 4 : ℚ) : ℝ) 1 := by
  rw [exThetaQuarter, theta_quarter_dyadic]
  simpa only [Rat.cast_one] using exactCount_eq_source (11 + 6 * L) 1 (by norm_num)

theorem exRho_eq_source (L Δ : ℕ) (γ : ℚ)
    (hΔ : 0 < Δ) (hγ : 0 < γ) :
    exRho L Δ γ = CurrentAdditive.conditioningExceptionCount
      (ρ L : ℝ) ((δU L Δ γ / 2 : ℚ) : ℝ) := by
  have hτ : (0 : ℚ) < δU L Δ γ / 2 := by
    have hη : 0 < η L Δ γ := by
      unfold η
      exact div_pos (c_pos Δ γ hΔ hγ) (by exact_mod_cast s_pos L)
    have hδ : 0 < δU L Δ γ := by
      unfold δU
      exact div_pos hη (by positivity [w_pos L])
    positivity
  rw [exRho, rho_dyadic]
  exact exactCount_eq_source L _ hτ

theorem exOwner_eq_source (L Δ : ℕ) (γ : ℚ)
    (hΔ : 0 < Δ) (hγ : 0 < γ) :
    exOwner L Δ γ = CurrentAdditive.conditioningExceptionCount
      (θ L : ℝ) ((η L Δ γ / 2 : ℚ) : ℝ) := by
  have hτ : (0 : ℚ) < η L Δ γ / 2 := by
    have hη : 0 < η L Δ γ := by
      unfold η
      exact div_pos (c_pos Δ γ hΔ hγ) (by exact_mod_cast s_pos L)
    positivity
  rw [exOwner, theta_dyadic]
  exact exactCount_eq_source (9 + 6 * L) _ hτ

theorem ownerExact_eq_source (L Δ : ℕ) (γ : ℚ)
    (hΔ : 0 < Δ) (hγ : 0 < γ) :
    ownerExact L Δ γ = ownerException L Δ γ := by
  simp only [ownerExact, ownerException, exOwner_eq_source L Δ γ hΔ hγ]

/-- All comparisons from v35 Appendix `det:parameters`, with the public
floor `n ≤ 2^L`.  The graph promise is a separate input obligation. -/
def literalTests (L n m Δ : ℕ) (γ : ℚ) : Prop :=
  n ≤ N L ∧
  128 * exX L ≤ s L ∧
  128 * exTheta L ≤ w L ∧
  exThetaQuarter L ≤ s L * q₂ L ∧
  128 * (exRho L Δ γ + 1) ≤ Q L ∧
  sourceC128 / (s L : ℚ) ^ 128 ≤ θ L / 4 ∧
  4 * ownerExact L Δ γ ≤ w L ∧
  (Kstar L : ℚ) * ownerExact L Δ γ ≤ η L Δ γ * w L / 16 ∧
  Paper2.SourcePadding.powTwoCeil (12 * s L * m) ≤ q₂ L ∧
  2 * (n + s L - 3) ≤ q₂ L ∧
  16 ≤ s L / 4 ∧
  4 * (s L : ℚ) ^ 2 * ρ L ≤ 1 ∧
  (s L : ℚ) * ρ L ≤ 1 / 1000 ∧
  (q₂ L : ℚ) * x L ≤ 1 / 10000 ∧
  (s L : ℚ) * x L ≤ 1 / 10000 ∧
  (w L : ℚ) * x L ≤ 1 / 10000 ∧
  8 * (s L : ℚ) * q₁ L ≤ (γ / 24) * q₂ L / 16 ∧
  2 * (q₂ L : ℚ) * x L ≤ 1 / 8 ∧
  2 * (s L : ℚ) * x L ≤ 1 / 1000 ∧
  2 * (w L : ℚ) * x L + η L Δ γ / (16 * (127 / 128 : ℚ)) < 1 ∧
  2 * (w L : ℚ) ^ 2 * x L ≤ η L Δ γ / (16 * (127 / 128 : ℚ)) ∧
  x L ≤ 1 / ((w L : ℚ) ^ 2 * q₂ L) ∧
  4 * (1 / 256 : ℚ) * w L * q₂ L * x L ≤ η L Δ γ / 32 ∧
  4 * (1 / 256 : ℚ) * w L / q₂ L ≤ η L Δ γ / 32 ∧
  (3 / 5 : ℚ) * (1 - 2 / (s L : ℚ)) - (q₁ L : ℚ) * ρ L > 9 / 16 ∧
  (3 / 5 : ℚ) - (q₂ L : ℚ) * x L > 9 / 16 ∧
  ∀ j : Fin 3,
    (2 : ℚ) ^ j.val *
      (((3 / 5 : ℚ) * (1 / 2 : ℚ) ^ j.val - (1 - (255 / 256 : ℚ))) /
        (255 / 256 : ℚ)) - (s L : ℚ) * x L > 9 / 16

/-- This is a total `Bool` evaluator; its arithmetic uses natural and rational
operations, including fixed-degree integer roots. -/
instance instDecidableLiteralTests (L n m Δ : ℕ) (γ : ℚ) :
    Decidable (literalTests L n m Δ γ) := by
  unfold literalTests
  infer_instance

def literalTest (L n m Δ : ℕ) (γ : ℚ) : Bool :=
  decide (literalTests L n m Δ γ)

theorem literalTest_iff (L n m Δ : ℕ) (γ : ℚ) :
    literalTest L n m Δ γ = true ↔ literalTests L n m Δ γ := by
  simp only [literalTest, decide_eq_true_eq]

theorem production_admissible_passes_literal (L n m Δ : ℕ) (γ : ℚ)
    (hΔ : 0 < Δ) (hγ : 0 < γ) (hn : n ≤ N L)
    (h : Admissible L Δ n m sourceC128Ceil γ) :
    literalTest L n m Δ γ = true := by
  have hA : (3 / 5 : ℚ) * (1 - 2 / (s L : ℚ)) -
      (q₁ L : ℚ) * ρ L > 9 / 16 := by
    apply (Rat.cast_lt (K := ℝ)).mp
    simpa only [Rat.cast_sub, Rat.cast_mul, Rat.cast_div, Rat.cast_natCast,
      Rat.cast_ofNat, Rat.cast_one] using h.ratio_A
  have hT : (3 / 5 : ℚ) - (q₂ L : ℚ) * x L > 9 / 16 := by
    apply (Rat.cast_lt (K := ℝ)).mp
    simpa only [Rat.cast_sub, Rat.cast_mul, Rat.cast_div, Rat.cast_natCast,
      Rat.cast_ofNat, Rat.cast_one] using h.ratio_T
  have hN (j : Fin 3) :
      (2 : ℚ) ^ j.val *
        (((3 / 5 : ℚ) * (1 / 2 : ℚ) ^ j.val - (1 - (255 / 256 : ℚ))) /
          (255 / 256 : ℚ)) - (s L : ℚ) * x L > 9 / 16 := by
    apply (Rat.cast_lt (K := ℝ)).mp
    simpa only [Rat.cast_sub, Rat.cast_mul, Rat.cast_div, Rat.cast_natCast,
      Rat.cast_ofNat, Rat.cast_one, Rat.cast_pow] using h.ratio_N j
  apply (literalTest_iff L n m Δ γ).mpr
  unfold literalTests
  rw [exX_eq_source, exTheta_eq_source, exThetaQuarter_eq_source,
    exRho_eq_source L Δ γ hΔ hγ, ownerExact_eq_source L Δ γ hΔ hγ]
  exact ⟨hn, h.exception_x, h.exception_theta, h.exception_theta_quarter,
    h.exception_rho, source_moment_check L Δ n m γ h, h.owner_reserve,
    h.owner_mass, h.graph_width, h.row_width, h.rung_size,
    h.square_rho, h.s_rho, h.q₂_x, h.s_x, h.w_x, h.graph_owner,
    h.double_q₂_x, h.double_s_x, h.owner_gap, h.square_x,
    h.inverse_x, h.loss1, h.loss2, hA, hT, hN⟩

#print axioms literalTest_iff
#print axioms production_admissible_passes_literal

end CurrentAdditive.PublicScheduleExactAdmissibility
