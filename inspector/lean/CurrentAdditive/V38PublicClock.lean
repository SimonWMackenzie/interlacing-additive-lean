import CurrentAdditive.V38Public
import CurrentAdditive.FieldSearchPackedCompletion

/-! Exact selected degree and transition budget. The array supplied to the
field printer has n=H*K genuine bits. Zero-padding is a subsequent physical
operation; it does not affect this field degree or its small-bias law. -/

namespace CurrentAdditive.V38Clock

open CurrentAdditive.SmallBias
open CurrentAdditive.FiniteFieldConstructor
open CurrentAdditive.FiniteFieldMachine.FieldListOutputMachine

set_option maxHeartbeats 1000000

theorem target_exact (b t : ℕ) : v38FieldTarget b t = 2 ^ (5 * b + 14 * t) := by
  simp only [v38FieldTarget, v38PositionCount, v38ErrorExponent,
    ← pow_add]
  congr 1
  omega

theorem degree_exact (b t : ℕ) : v38FieldDegree b t = 5 * b + 14 * t := by
  rw [v38FieldDegree, target_exact, Nat.clog_pow 2 _ (by decide)]

theorem field_order_exact (b t : ℕ) :
    2 ^ v38FieldDegree b t = v38FieldTarget b t := by
  rw [degree_exact, target_exact]

theorem position_le_target (b t : ℕ) :
    v38PositionCount b t ≤ v38FieldTarget b t := by
  unfold v38FieldTarget
  exact Nat.le_mul_of_pos_right _ (by positivity)

def fieldBudget (d n : ℕ) : ℕ :=
  55 * 2 ^ d * 2 ^ (d / 2) * (d + 1) ^ 2 + 2 +
    timeBound d 0 n

def paddedBudget (d n : ℕ) : ℕ :=
  fieldBudget d n + 1 + 3 * ((2 ^ d) ^ 2 * n) + 2

theorem fieldBudget_le (d n : ℕ) (hd : 0 < d) (hn : 0 < n) :
    fieldBudget d n ≤ 82 * (2 ^ d) ^ 2 * n * (d + 1) ^ 2 := by
  have hp := timeBound_le d 0 n hd hn
  have hhalf : 2 ^ (d / 2) ≤ 2 ^ d :=
    Nat.pow_le_pow_right (by decide) (Nat.div_le_self d 2)
  have hs := Nat.mul_le_mul_left (55 * 2 ^ d) hhalf
  have hs' := Nat.mul_le_mul_right ((d + 1) ^ 2) hs
  have hn' : 1 ≤ n := hn
  have hsearch : 55 * 2 ^ d * 2 ^ (d / 2) * (d + 1) ^ 2 ≤
      55 * (2 ^ d) ^ 2 * n * (d + 1) ^ 2 := by
    calc
      _ ≤ 55 * 2 ^ d * 2 ^ d * (d + 1) ^ 2 := hs'
      _ ≤ (55 * 2 ^ d * 2 ^ d * (d + 1) ^ 2) * n :=
        Nat.le_mul_of_pos_right _ hn
      _ = _ := by ring
  have hpos : 1 ≤ (2 ^ d) ^ 2 * n * (d + 1) ^ 2 := by
    have : 0 < (2 ^ d) ^ 2 * n * (d + 1) ^ 2 := by positivity
    omega
  unfold fieldBudget
  nlinarith

theorem paddedBudget_le (d n : ℕ) (hd : 0 < d) (hn : 0 < n) :
    paddedBudget d n ≤ 88 * (2 ^ d) ^ 2 * n * (d + 1) ^ 2 := by
  have hf := fieldBudget_le d n hd hn
  have hpos : 1 ≤ (2 ^ d) ^ 2 * n := by
    have : 0 < (2 ^ d) ^ 2 * n := by positivity
    omega
  have hs : (2 ^ d) ^ 2 * n ≤ (2 ^ d) ^ 2 * n * (d + 1) ^ 2 :=
    Nat.le_mul_of_pos_right _ (by positivity)
  unfold paddedBudget
  nlinarith

theorem degree_succ_le_order (d : ℕ) : d + 1 ≤ 2 ^ d :=
  Nat.succ_le_iff.mpr Nat.lt_two_pow_self

theorem public_paddedBudget_le (b t : ℕ) (ht : 4 ≤ t) :
    paddedBudget (v38FieldDegree b t) (v38PositionCount b t) ≤
      88 * (v38FieldTarget b t) ^ 5 := by
  have hb := paddedBudget_le (v38FieldDegree b t) (v38PositionCount b t)
    (v38FieldDegree_pos b t ht) (by unfold v38PositionCount; positivity)
  have hn := position_le_target b t
  have hd := degree_succ_le_order (v38FieldDegree b t)
  rw [field_order_exact] at hb hd
  calc
    _ ≤ 88 * (v38FieldTarget b t) ^ 2 * (v38PositionCount b t) *
        (v38FieldDegree b t + 1) ^ 2 := hb
    _ ≤ 88 * (v38FieldTarget b t) ^ 2 * (v38FieldTarget b t) *
        (v38FieldTarget b t) ^ 2 := by gcongr
    _ = _ := by ring

theorem target_fixed_t (b t : ℕ) :
    v38FieldTarget b t = 2 ^ (14 * t) * (2 ^ b) ^ 5 := by
  rw [target_exact, pow_add, Nat.mul_comm 5 b, pow_mul]
  ring

theorem public_paddedBudget_fixed_t (b t : ℕ) (ht : 4 ≤ t) :
    paddedBudget (v38FieldDegree b t) (v38PositionCount b t) ≤
      (88 * (2 ^ (14 * t)) ^ 5) * (2 ^ b) ^ 25 := by
  have h := public_paddedBudget_le b t ht
  rw [target_fixed_t, mul_pow] at h
  calc
    _ ≤ 88 * ((2 ^ (14 * t)) ^ 5 * ((2 ^ b) ^ 5) ^ 5) := h
    _ = _ := by ring

#print axioms degree_exact
#print axioms fieldBudget_le
#print axioms paddedBudget_le
#print axioms public_paddedBudget_fixed_t

end CurrentAdditive.V38Clock
