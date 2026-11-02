import CurrentAdditive.V39RecursiveGenerator

set_option maxHeartbeats 2000000

namespace CurrentAdditive.V39RecursiveGenerator

theorem base_column_coefficient (s : ℕ) (hs : 2 ≤ s) :
    (s + 1) + s * (s - 2 + s + 1) = 2 * s ^ 2 + 1 := by
  have hsub : s - 2 + 2 = s := Nat.sub_add_cancel hs
  nlinarith

/-- The explicit complete-label draw multiplier is cubic in a common bound
on widths. This specializes directly to the source schedule's 2^(O(E))
width bounds and leaves no k-dependent constant hidden in the recurrence. -/
theorem drawFactor_le_cubic (q₁ q₂ s w Q M : ℕ) (hM : 1 ≤ M)
    (hq₁ : q₁ ≤ M) (hq₂ : q₂ ≤ M) (hs : s ≤ M)
    (hw : w ≤ M) (hQ : Q ≤ M) :
    drawFactor q₁ q₂ s w Q ≤ 8 * M ^ 3 := by
  have hsq : s * (q₁ + s + 1) ≤ M * (M + M + 1) := by gcongr
  have hrow : Q * (2 + s + ((s + 1) + s * (q₁ + s + 1))) ≤
      M * (2 + M + ((M + 1) + M * (M + M + 1))) := by gcongr
  have hcol : w * (3 + 2 * q₂) ≤ M * (3 + 2 * M) := by gcongr
  have hpow : M ≤ M ^ 2 := by nlinarith
  have hpow' : M ^ 2 ≤ M ^ 3 := by nlinarith
  unfold drawFactor
  apply max_le <;> nlinarith

theorem drawBudget_le_cubic (p₀ q₁ q₂ s w Q M k : ℕ) (hM : 1 ≤ M)
    (hp₀ : p₀ ≤ M) (hq₁ : q₁ ≤ M) (hq₂ : q₂ ≤ M) (hs : s ≤ M)
    (hw : w ≤ M) (hQ : Q ≤ M) :
    drawBudget p₀ q₁ q₂ s w Q k ≤ (8 * M ^ 3) ^ k * (M + 1) := by
  unfold drawBudget
  exact Nat.mul_le_mul
    (Nat.pow_le_pow_left (drawFactor_le_cubic q₁ q₂ s w Q M hM hq₁ hq₂ hs hw hQ) k)
    (Nat.add_le_add_right hp₀ 1)

theorem drawBudget_le_exp (p₀ q₁ q₂ s w Q E k : ℕ)
    (hp₀ : p₀ ≤ 2 ^ E) (hq₁ : q₁ ≤ 2 ^ E) (hq₂ : q₂ ≤ 2 ^ E)
    (hs : s ≤ 2 ^ E) (hw : w ≤ 2 ^ E) (hQ : Q ≤ 2 ^ E) :
    drawBudget p₀ q₁ q₂ s w Q k ≤ 2 ^ ((3 * E + 3) * k + E + 1) := by
  have h := drawBudget_le_cubic p₀ q₁ q₂ s w Q (2 ^ E) k
    (Nat.one_le_pow E 2 (by omega)) hp₀ hq₁ hq₂ hs hw hQ
  have hbase : 2 ^ E + 1 ≤ 2 ^ (E + 1) := by
    rw [pow_succ]
    have h1 := Nat.one_le_pow E 2 (by omega)
    omega
  apply h.trans
  calc
    (8 * (2 ^ E) ^ 3) ^ k * (2 ^ E + 1)
      ≤ (8 * (2 ^ E) ^ 3) ^ k * 2 ^ (E + 1) := Nat.mul_le_mul_left _ hbase
    _ = 2 ^ ((3 * E + 3) * k + E + 1) := by
      rw [show 8 * (2 ^ E) ^ 3 = 2 ^ (3 * E + 3) by
        rw [show (8 : ℕ) = 2 ^ 3 by decide, ← pow_mul, ← pow_add]; congr 1; omega]
      rw [← pow_mul, ← pow_add]
      congr 1

#print axioms drawFactor_le_cubic
#print axioms drawBudget_le_exp

end CurrentAdditive.V39RecursiveGenerator
