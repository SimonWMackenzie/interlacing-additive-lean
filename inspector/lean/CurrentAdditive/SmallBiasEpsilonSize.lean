import CurrentAdditive.SmallBiasFieldSize

/-!
# A polynomial-exponent bound for the source bias parameter

Source: v27 `appendices/G-small-bias.tex`,
`yao:deterministic-materialization`. This is scalar size accounting only;
it does not produce a machine implementation or bit-operation bound.
-/

namespace CurrentAdditive.SmallBias

/-- The dyadic exponent grows linearly in `b` for fixed `t`. The additive
constant is slightly looser than the manuscript's displayed one, but
suffices for its polynomial-in-`H` size claim. -/
theorem source_bias_exponent_bound (b t : ℕ) (ht : 4 ≤ t) :
    2 ^ sourceSuffixDepth b t + t + sourceCutIndex b t + 2 ≤
      b * (4 * 2 ^ t + 1) + 12 * 2 ^ t * t + 3 * t + 2 := by
  have hQ := source_suffix_size_bound b t ht
  have hi := (sourceCutIndex_spec b t ht).2.1
  dsimp [sourcePairDepth] at hQ hi
  have hA : b + 2 * t - 2 + t - 1 ≤ b + 3 * t := by omega
  have hQ' : 2 ^ sourceSuffixDepth b t <
      4 * 2 ^ t * (b + 3 * t) :=
    hQ.trans_le (Nat.mul_le_mul_left _ hA)
  have hi' : sourceCutIndex b t ≤ b + 2 * t := by omega
  nlinarith [hQ']

/-- A direct polynomial-in-`H=2^b` bound on the inverse dyadic bias,
with a fixed-`t` coefficient. -/
theorem source_inverse_bias_polynomial (b t : ℕ) (ht : 4 ≤ t) :
    (1 : ℚ) /
      (1 / 2 : ℚ) ^
        (2 ^ sourceSuffixDepth b t + t + sourceCutIndex b t + 2) ≤
      (2 : ℚ) ^ (12 * 2 ^ t * t + 3 * t + 2) *
        ((2 : ℚ) ^ b) ^ (4 * 2 ^ t + 1) := by
  have he := source_bias_exponent_bound b t ht
  have hp : (2 : ℚ) ^
      (2 ^ sourceSuffixDepth b t + t + sourceCutIndex b t + 2) ≤
      (2 : ℚ) ^
        (b * (4 * 2 ^ t + 1) + (12 * 2 ^ t * t + 3 * t + 2)) :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  have hleft : (1 : ℚ) /
      (1 / 2 : ℚ) ^
        (2 ^ sourceSuffixDepth b t + t + sourceCutIndex b t + 2) =
      (2 : ℚ) ^
        (2 ^ sourceSuffixDepth b t + t + sourceCutIndex b t + 2) := by
    simp
  rw [hleft]
  convert hp using 1
  ring

#print axioms CurrentAdditive.SmallBias.source_bias_exponent_bound
#print axioms CurrentAdditive.SmallBias.source_inverse_bias_polynomial

end CurrentAdditive.SmallBias
