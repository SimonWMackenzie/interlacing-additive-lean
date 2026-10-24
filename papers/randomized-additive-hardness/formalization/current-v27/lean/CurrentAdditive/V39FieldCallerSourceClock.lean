import CurrentAdditive.V39ScalarClock

namespace CurrentAdditive.V39ScalarSetup

open CurrentAdditive.V38Encoded CurrentAdditive.V38Clock CurrentAdditive.SmallBias
open CurrentAdditive.V39SourceOutputSize
open Paper2.YaoSourceCodec

/-- Source-code bound for the field team's complete caller budget: copying
degree and genuine width, unary preparation, field generation, zero padding
and installation. The physical caller theorem is owned by public_field. -/
theorem complete_caller_budget_source_bound {t : ℕ} (src : YaoSource t) :
    120 * v38FieldTarget (edgeBits src.2.1) t ^ 5 ≤
      ((120 * (2 ^ (14 * t)) ^ 5) * 2 ^ 25) *
        ((encode src).length + 1) ^ 25 := by
  calc
    _ = (120 * (2 ^ (14 * t)) ^ 5) * (2 ^ edgeBits src.2.1) ^ 25 := by
      rw [target_fixed_t]
      ring
    _ ≤ (120 * (2 ^ (14 * t)) ^ 5) *
        (2 * ((encode src).length + 1)) ^ 25 :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (source_capacity_le src) _)
    _ = _ := by rw [mul_pow]; ring

#print axioms complete_caller_budget_source_bound

end CurrentAdditive.V39ScalarSetup
