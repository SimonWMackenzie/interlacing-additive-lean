import CurrentAdditive.SmallBiasExactListCount
import CurrentAdditive.FirstPassingTotal

/-!
# A computable public degree for the printed finite field

Source: v27 Appendix G, `yao:deterministic-materialization` and
`yao:finite-field-list`. The public input parameters determine the exact
dyadic target `n₀/ε`; its binary ceiling logarithm is a computable degree.
This module does not claim a bit-operation bound for the search or printer.
-/

namespace CurrentAdditive.SmallBias

open CurrentAdditive.FiniteFieldConstructor

/-- The exponent in the exact dyadic bias used at the source cut. -/
def publicBiasExponent (b t : ℕ) : ℕ :=
  2 ^ sourceSuffixDepth b t + t + sourceCutIndex b t + 2

/-- The integer `n₀/ε`, where `ε=2⁻ᴬ`. -/
def publicFieldTarget (b t : ℕ) : ℕ :=
  (2 ^ b * (2 ^ t * 2 ^ t + 1)) * 2 ^ publicBiasExponent b t

/-- The least degree whose field order reaches the public target. -/
def publicFieldDegree (b t : ℕ) : ℕ :=
  Nat.clog 2 (publicFieldTarget b t)

theorem public_target_eq_source (b t : ℕ) :
    (publicFieldTarget b t : ℚ) =
      ((2 ^ b * (2 ^ t * 2 ^ t + 1) : ℕ) : ℚ) / sourceBiasQ b t := by
  simp only [publicFieldTarget, publicBiasExponent, sourceBiasQ]
  push_cast
  simp [div_eq_mul_inv]

theorem public_target_gt_one (b t : ℕ) :
    1 < publicFieldTarget b t := by
  have h := source_field_target_gt_one b t
  rw [← public_target_eq_source] at h
  exact_mod_cast h

theorem public_degree_pos (b t : ℕ) : 0 < publicFieldDegree b t :=
  Nat.clog_pos (by omega) (public_target_gt_one b t)

theorem public_degree_lower (b t : ℕ) :
    publicFieldTarget b t ≤ 2 ^ publicFieldDegree b t :=
  Nat.le_pow_clog (by omega) _

theorem public_degree_upper (b t : ℕ) :
    2 ^ publicFieldDegree b t < 2 * publicFieldTarget b t := by
  have hp := Nat.pow_pred_clog_lt_self (by omega : 1 < 2)
    (public_target_gt_one b t)
  have hd := public_degree_pos b t
  have he : publicFieldDegree b t - 1 + 1 = publicFieldDegree b t := by omega
  have hpow : 2 ^ publicFieldDegree b t =
      2 * 2 ^ (publicFieldDegree b t - 1) := by
    calc
      _ = 2 ^ (publicFieldDegree b t - 1 + 1) := by rw [he]
      _ = 2 * 2 ^ (publicFieldDegree b t - 1) := by rw [pow_succ]; omega
  rw [hpow]
  exact Nat.mul_lt_mul_of_pos_left hp (by omega)

theorem public_degree_source_bounds (b t : ℕ) :
    ((2 ^ b * (2 ^ t * 2 ^ t + 1) : ℕ) : ℚ) / sourceBiasQ b t ≤
        (2 : ℚ) ^ publicFieldDegree b t ∧
      (((2 ^ publicFieldDegree b t) ^ 2 : ℕ) : ℚ) <
        4 * (((2 ^ b * (2 ^ t * 2 ^ t + 1) : ℕ) : ℚ) /
          sourceBiasQ b t) ^ 2 := by
  have hl := public_degree_lower b t
  have hu := public_degree_upper b t
  constructor
  · rw [← public_target_eq_source]
    exact_mod_cast hl
  · rw [← public_target_eq_source]
    have hs : (2 ^ publicFieldDegree b t) ^ 2 <
        4 * (publicFieldTarget b t) ^ 2 := by
      nlinarith [sq_nonneg (2 ^ publicFieldDegree b t -
        2 * publicFieldTarget b t : ℤ)]
    exact_mod_cast hs

/-- The target integer is at most a power of two with an explicit
exponent. In particular the binary ceiling logarithm has a linear-in-`b`
bound for each fixed `t`. -/
theorem public_target_power_bound (b t : ℕ) :
    publicFieldTarget b t ≤
      2 ^ (b + 2 * t + 1 + publicBiasExponent b t) := by
  have hs : 1 ≤ 2 ^ t * 2 ^ t := by
    have hp : 1 ≤ 2 ^ t := Nat.one_le_pow t 2 (by omega)
    nlinarith
  have hfactor : 2 ^ t * 2 ^ t + 1 ≤ 2 ^ (2 * t + 1) := by
    rw [show 2 * t + 1 = t + t + 1 by omega, pow_succ, pow_add]
    nlinarith
  unfold publicFieldTarget
  calc
    _ ≤ (2 ^ b * 2 ^ (2 * t + 1)) * 2 ^ publicBiasExponent b t :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hfactor)
    _ = _ := by rw [← pow_add, ← pow_add]; congr 1

theorem public_degree_le (b t : ℕ) :
    publicFieldDegree b t ≤
      b + 2 * t + 1 + publicBiasExponent b t := by
  exact (Nat.clog_le_iff_le_pow (by omega : 1 < 2)).2
    (public_target_power_bound b t)

/-- An explicit bound on the number of public field-coordinate bits. -/
theorem public_degree_cost_bound (b t : ℕ) (ht : 4 ≤ t) :
    publicFieldDegree b t ≤
      b * (4 * 2 ^ t + 2) + 12 * 2 ^ t * t + 5 * t + 2 := by
  have h := public_degree_le b t
  have ha := source_bias_exponent_bound_exact b t ht
  dsimp [publicBiasExponent] at h
  have hident : b * (4 * 2 ^ t + 2) =
      b * (4 * 2 ^ t + 1) + b := by ring
  rw [hident]
  omega

/-- The source's exact strict labelled-list bound now uses a public
computable degree rather than an existentially selected one. -/
theorem public_degree_exact_list_bound (b t : ℕ) (ht : 4 ≤ t) :
    (((2 ^ publicFieldDegree b t) ^ 2 : ℕ) : ℚ) <
      4 * ((2 ^ t * 2 ^ t + 1 : ℕ) : ℚ) ^ 2 *
        ((2 : ℚ) ^ (12 * 2 ^ t * t + 3 * t + 1)) ^ 2 *
        ((2 : ℚ) ^ b) ^ (8 * 2 ^ t + 4) :=
  source_list_count_polynomial_exact b t (publicFieldDegree b t) ht
    (public_degree_source_bounds b t).2

/-- The public modulus search has a result at the computed positive
degree, and the returned polynomial passes the proved irreducibility test. -/
theorem public_firstPassing_correct (b t : ℕ) :
    ∃ modulus,
      TrialSearch.firstPassing (publicFieldDegree b t) = some modulus ∧
      Irreducible (BitPolynomialBridge.polynomial
        (publicFieldDegree b t + 1) modulus) := by
  obtain ⟨modulus, h⟩ :=
    TrialSearch.firstPassing_total (publicFieldDegree b t)
      (public_degree_pos b t)
  exact ⟨modulus, h,
    TrialSearch.firstPassing_correct (public_degree_pos b t) h⟩

/-- The literal executable list printer terminates at the public degree. -/
theorem public_makeList_total (b t : ℕ) :
    ∃ output, TrialSearch.makeList (publicFieldDegree b t)
      (2 ^ b * (2 ^ t * 2 ^ t + 1)) = some output :=
  TrialSearch.makeList_total _ _ (public_degree_pos b t)

#print axioms CurrentAdditive.SmallBias.public_degree_source_bounds
#print axioms CurrentAdditive.SmallBias.public_degree_cost_bound
#print axioms CurrentAdditive.SmallBias.public_degree_exact_list_bound
#print axioms CurrentAdditive.SmallBias.public_firstPassing_correct
#print axioms CurrentAdditive.SmallBias.public_makeList_total

end CurrentAdditive.SmallBias
