import Mathlib

/-!
The finite counts behind the v27 field-construction clock. This file only
counts loop iterations; it does not treat a Lean `List` operation as a
bit-machine transition. The physical divisor and printer loops must supply
their own run theorems before these bounds become an end-to-end runtime.
-/

namespace CurrentAdditive.FiniteFieldMachine.RuntimeArithmetic

def divisorCount (k : ℕ) : ℕ :=
  ∑ e ∈ Finset.range k, 2 ^ (e + 1)

theorem divisorCount_exact (k : ℕ) :
    divisorCount k + 2 = 2 ^ (k + 1) := by
  induction k with
  | zero => simp [divisorCount]
  | succ k ih =>
      simp only [divisorCount, Finset.sum_range_succ] at ih ⊢
      rw [pow_succ]
      omega

theorem divisorCount_le (k : ℕ) :
    divisorCount k ≤ 2 ^ (k + 1) := by
  have h := divisorCount_exact k
  omega

theorem half_plus_one_le (d : ℕ) (hd : 0 < d) : d / 2 + 1 ≤ d := by
  omega

theorem divisorCount_le_R (d : ℕ) (hd : 0 < d) :
    divisorCount (d / 2) ≤ 2 ^ d := by
  exact (divisorCount_le _).trans (Nat.pow_le_pow_right (by omega) (half_plus_one_le d hd))

/-- The search tries fewer than `2*2^(floor(d/2))` divisors per candidate. -/
theorem divisorCount_lt_twice_half (d : ℕ) :
    divisorCount (d / 2) < 2 * 2 ^ (d / 2) := by
  have h := divisorCount_exact (d / 2)
  rw [pow_succ] at h
  omega

def pairCount (d : ℕ) : ℕ := 2 ^ d * divisorCount (d / 2)

theorem pairCount_le (d : ℕ) (hd : 0 < d) :
    pairCount d ≤ (2 ^ d) ^ 2 := by
  unfold pairCount
  have h := divisorCount_le_R d hd
  nlinarith

theorem pairCount_lt_three_halves_envelope (d : ℕ) :
    pairCount d < 2 * 2 ^ d * 2 ^ (d / 2) := by
  unfold pairCount
  have h := divisorCount_lt_twice_half d
  have hp : 0 < 2 ^ d := by positivity
  nlinarith

/-- An `R²`-entry stream with one quadratic multiplication and one linear
dot operation per bit has this exact algebraic cost envelope. The machine
proof still has to show that each iteration meets those component clocks. -/
def tableBudget (d n : ℕ) : ℕ :=
  (2 ^ d) ^ 2 * n * ((4 * d + 5) * d + (2 * d + 3) + 10)

theorem tableBudget_quadratic (d n : ℕ) :
    tableBudget d n ≤ 24 * (2 ^ d) ^ 2 * n * (d + 1) ^ 2 := by
  unfold tableBudget
  have h : (4 * d + 5) * d + (2 * d + 3) + 10 ≤ 24 * (d + 1) ^ 2 := by
    nlinarith
  calc
    (2 ^ d) ^ 2 * n * ((4 * d + 5) * d + (2 * d + 3) + 10) ≤
        (2 ^ d) ^ 2 * n * (24 * (d + 1) ^ 2) := Nat.mul_le_mul_left _ h
    _ = 24 * (2 ^ d) ^ 2 * n * (d + 1) ^ 2 := by ring

#print axioms divisorCount_exact
#print axioms pairCount_lt_three_halves_envelope
#print axioms tableBudget_quadratic

end CurrentAdditive.FiniteFieldMachine.RuntimeArithmetic
