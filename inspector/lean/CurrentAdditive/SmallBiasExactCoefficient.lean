import CurrentAdditive.SmallBiasListCount

/-!
# Exact displayed coefficient for the v27 inverse-bias bound

Source: v27 `appendices/G-small-bias.tex`,
`yao:deterministic-materialization`, lines around the displayed
`E_t=2^(12st+3t+1)`. This tightens only the numerical estimate; it does
not assert a bit-operation runtime for the physical printer.
-/

namespace CurrentAdditive.SmallBias

/-- The paper's displayed fixed-`t` exponent coefficient is sufficient.
The strict maximal-cut bound and `i<a` leave slack in the bound. -/
theorem source_bias_exponent_bound_exact (b t : ℕ) (ht : 4 ≤ t) :
    2 ^ sourceSuffixDepth b t + t + sourceCutIndex b t + 2 ≤
      b * (4 * 2 ^ t + 1) + 12 * 2 ^ t * t + 3 * t + 1 := by
  have hQ := source_suffix_size_bound b t ht
  have hi := (sourceCutIndex_spec b t ht).2.1
  dsimp [sourcePairDepth] at hQ hi
  have hA : b + 2 * t - 2 + t - 1 ≤ b + 3 * t := by omega
  have hQ' : 2 ^ sourceSuffixDepth b t <
      4 * 2 ^ t * (b + 3 * t) :=
    hQ.trans_le (Nat.mul_le_mul_left _ hA)
  have hi' : sourceCutIndex b t + 3 ≤ b + 2 * t := by omega
  nlinarith [hQ']

/-- The literal `E_t` coefficient in Appendix G's polynomial size claim.
The source proves a strict inequality, which follows here from the spare
integer slack in the preceding estimate. -/
theorem source_inverse_bias_polynomial_exact (b t : ℕ) (ht : 4 ≤ t) :
    (1 : ℚ) /
      (1 / 2 : ℚ) ^
        (2 ^ sourceSuffixDepth b t + t + sourceCutIndex b t + 2) <
      (2 : ℚ) ^ (12 * 2 ^ t * t + 3 * t + 1) *
        ((2 : ℚ) ^ b) ^ (4 * 2 ^ t + 1) := by
  have hQ := source_suffix_size_bound b t ht
  have hi := (sourceCutIndex_spec b t ht).2.1
  dsimp [sourcePairDepth] at hQ hi
  have hA : b + 2 * t - 2 + t - 1 ≤ b + 3 * t := by omega
  have hQ' : 2 ^ sourceSuffixDepth b t <
      4 * 2 ^ t * (b + 3 * t) :=
    hQ.trans_le (Nat.mul_le_mul_left _ hA)
  have hi' : sourceCutIndex b t + 3 ≤ b + 2 * t := by omega
  have he : 2 ^ sourceSuffixDepth b t + t + sourceCutIndex b t + 2 <
      b * (4 * 2 ^ t + 1) + (12 * 2 ^ t * t + 3 * t + 1) := by
    nlinarith [hQ']
  have hp : (2 : ℚ) ^
      (2 ^ sourceSuffixDepth b t + t + sourceCutIndex b t + 2) <
      (2 : ℚ) ^
        (b * (4 * 2 ^ t + 1) + (12 * 2 ^ t * t + 3 * t + 1)) :=
    (pow_lt_pow_iff_right₀ (by norm_num : (1 : ℚ) < 2)).mpr he
  have hleft : (1 : ℚ) /
      (1 / 2 : ℚ) ^
        (2 ^ sourceSuffixDepth b t + t + sourceCutIndex b t + 2) =
      (2 : ℚ) ^
        (2 ^ sourceSuffixDepth b t + t + sourceCutIndex b t + 2) := by
    simp
  rw [hleft]
  convert hp using 1
  ring

#print axioms CurrentAdditive.SmallBias.source_bias_exponent_bound_exact
#print axioms CurrentAdditive.SmallBias.source_inverse_bias_polynomial_exact

end CurrentAdditive.SmallBias
