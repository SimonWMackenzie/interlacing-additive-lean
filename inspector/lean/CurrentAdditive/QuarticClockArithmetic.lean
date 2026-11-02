import Mathlib

/-! Arithmetic transfer for a polynomial numeric cap and an affine cutter. -/

namespace Paper2.CurrentAdditive.QuarticClockArithmetic

theorem affine_combine
    (a c z r i o p q g k l S : ℕ)
    (hS : S = p + q + g + k + l + o + 1)
    (hz : z = 4 + 2 * (g + k + l) + a * (p + l))
    (hi : i ≤ z)
    (hr : r ≤ c * (q + l + 1)) :
    z + r + i + o + 1 ≤ (2 * (a + 10) + c + 2) * S := by
  have hp : p + l ≤ S := by omega
  have hg : g ≤ S := by omega
  have hk : k ≤ S := by omega
  have hl : l ≤ S := by omega
  have ho : o ≤ S := by omega
  have h1 : 1 ≤ S := by omega
  have hq : q + l + 1 ≤ S := by omega
  have hm := Nat.mul_le_mul_left a hp
  have hr' : r ≤ c * S := hr.trans (Nat.mul_le_mul_left c hq)
  have hz' : z ≤ (a + 10) * S := by
    calc
      z = 4 + 2 * (g + k + l) + a * (p + l) := hz
      _ ≤ 10 * S + a * S := by omega
      _ = (a + 10) * S := by ring
  have hi' : i ≤ (a + 10) * S := hi.trans hz'
  calc
    z + r + i + o + 1 ≤
        (a + 10) * S + c * S + (a + 10) * S + S + S := by omega
    _ = (2 * (a + 10) + c + 2) * S := by ring

#print axioms affine_combine

end Paper2.CurrentAdditive.QuarticClockArithmetic
