import CurrentAdditive.V39SourceOutputSize

/-! Separate source-code bounds for the genuine H*K field width and the
internal H*(K+1) sentinel-padded writer width. The degree and field list stay
those of the genuine array. These are numeric resource bounds, not a claim
that the inherited old renderer has been adapted to the new array. -/

namespace CurrentAdditive.V39SourceFieldWidths

open CurrentAdditive.V38Source CurrentAdditive.V38Encoded
open CurrentAdditive.V39SourceCompiler CurrentAdditive.V39SourceRenderer
open CurrentAdditive.V39SourceAddressResource CurrentAdditive.V39SourceOutputSize
open CurrentAdditive.SmallBias CurrentAdditive.V38Clock
open Paper2.YaoSourceCodec

set_option maxHeartbeats 1000000

theorem genuine_width_le {t : ℕ} (src : YaoSource t) :
    v38PositionCount (edgeBits src.2.1) t ≤
      (2 * (2 ^ t * 2 ^ t)) * ((encode src).length + 1) := by
  unfold v38PositionCount
  calc
    _ ≤ (2 * ((encode src).length + 1)) * (2 ^ t * 2 ^ t) :=
      Nat.mul_le_mul_right _ (source_capacity_le src)
    _ = _ := by ring

theorem padded_width_le {t : ℕ} (src : YaoSource t) :
    2 ^ edgeBits src.2.1 * (2 ^ t * 2 ^ t + 1) ≤
      (2 * (2 ^ t * 2 ^ t + 1)) * ((encode src).length + 1) := by
  calc
    _ ≤ (2 * ((encode src).length + 1)) * (2 ^ t * 2 ^ t + 1) :=
      Nat.mul_le_mul_right _ (source_capacity_le src)
    _ = _ := by ring

/-- One public degree sizes both the genuine producer and the subsequent
zero-insertion adapter; the generated probability alphabet stays H*K. -/
theorem widths_and_degree {t : ℕ} (src : YaoSource t) :
    v38PositionCount (edgeBits src.2.1) t =
        2 ^ edgeBits src.2.1 * (2 ^ t * 2 ^ t) ∧
    v38FieldDegree (edgeBits src.2.1) t = 5 * edgeBits src.2.1 + 14 * t ∧
    v38PositionCount (edgeBits src.2.1) t ≤
        (2 * (2 ^ t * 2 ^ t)) * ((encode src).length + 1) ∧
    2 ^ edgeBits src.2.1 * (2 ^ t * 2 ^ t + 1) ≤
        (2 * (2 ^ t * 2 ^ t + 1)) * ((encode src).length + 1) :=
  ⟨rfl, degree_exact _ _, genuine_width_le src, padded_width_le src⟩

theorem field_label_count_le {t : ℕ} (src : YaoSource t) :
    (2 ^ v38FieldDegree (edgeBits src.2.1) t) ^ 2 ≤
      ((2 ^ (14 * t)) ^ 2 * 2 ^ 10) * ((encode src).length + 1) ^ 10 := by
  have hH := Nat.pow_le_pow_left (source_capacity_le src) 10
  calc
    _ = (2 ^ (14 * t)) ^ 2 * (2 ^ edgeBits src.2.1) ^ 10 := by
      rw [field_order_exact, target_fixed_t]
      ring
    _ ≤ (2 ^ (14 * t)) ^ 2 * (2 * ((encode src).length + 1)) ^ 10 :=
      Nat.mul_le_mul_left _ hH
    _ = _ := by rw [mul_pow]; ring

theorem genuine_array_bits_le {t : ℕ} (src : YaoSource t) :
    (2 ^ v38FieldDegree (edgeBits src.2.1) t) ^ 2 *
        v38PositionCount (edgeBits src.2.1) t ≤
      ((2 ^ (14 * t)) ^ 2 * 2 ^ 11 * (2 ^ t * 2 ^ t)) *
        ((encode src).length + 1) ^ 11 := by
  have h := Nat.mul_le_mul (field_label_count_le src) (genuine_width_le src)
  calc
    _ ≤ (((2 ^ (14 * t)) ^ 2 * 2 ^ 10) * ((encode src).length + 1) ^ 10) *
        ((2 * (2 ^ t * 2 ^ t)) * ((encode src).length + 1)) := h
    _ = _ := by simp only [pow_succ]; ring

theorem padded_array_bits_le {t : ℕ} (src : YaoSource t) :
    (2 ^ v38FieldDegree (edgeBits src.2.1) t) ^ 2 *
        (2 ^ edgeBits src.2.1 * (2 ^ t * 2 ^ t + 1)) ≤
      ((2 ^ (14 * t)) ^ 2 * 2 ^ 11 * (2 ^ t * 2 ^ t + 1)) *
        ((encode src).length + 1) ^ 11 := by
  have h := Nat.mul_le_mul (field_label_count_le src) (padded_width_le src)
  calc
    _ ≤ (((2 ^ (14 * t)) ^ 2 * 2 ^ 10) * ((encode src).length + 1) ^ 10) *
        ((2 * (2 ^ t * 2 ^ t + 1)) * ((encode src).length + 1)) := h
    _ = _ := by simp only [pow_succ]; ring

/-- The checked public field/padding transition budget, charged to the
emitted source word. This does not include the complete table printer. -/
theorem public_field_padding_budget_le {t : ℕ} (src : YaoSource t)
    (ht : 4 ≤ t) :
    paddedBudget (v38FieldDegree (edgeBits src.2.1) t)
        (v38PositionCount (edgeBits src.2.1) t) ≤
      ((88 * (2 ^ (14 * t)) ^ 5) * 2 ^ 25) *
        ((encode src).length + 1) ^ 25 := by
  calc
    _ ≤ (88 * (2 ^ (14 * t)) ^ 5) * (2 ^ edgeBits src.2.1) ^ 25 :=
      public_paddedBudget_fixed_t _ _ ht
    _ ≤ (88 * (2 ^ (14 * t)) ^ 5) * (2 * ((encode src).length + 1)) ^ 25 :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (source_capacity_le src) _)
    _ = _ := by rw [mul_pow]; ring

#print axioms genuine_width_le
#print axioms padded_width_le
#print axioms widths_and_degree
#print axioms field_label_count_le
#print axioms genuine_array_bits_le
#print axioms padded_array_bits_le
#print axioms public_field_padding_budget_le

end CurrentAdditive.V39SourceFieldWidths
