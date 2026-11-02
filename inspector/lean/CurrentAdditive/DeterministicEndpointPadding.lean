import CurrentAdditive.DeterministicEndpointNumeric
import Paper2.SquarePadding

/-! The v27 `det:reduction` square, made from the same finite Boolean
rectangle by the existing remainder-index construction. -/

namespace CurrentAdditive.DeterministicEndpointPadding

open Paper2.SquarePadding
open Workspace.Types.CommComplexity

theorem padded_entries_lt_four_square (m n : ℕ)
    (hm : 0 < m) (hn : 0 < n) :
    (side m n)^2 < 4*(m*n)^2 := by
  have hmax : max m n ≤ m*n := by
    apply max_le
    · nlinarith
    · nlinarith
  have hside := side_lt_twice_max (m := m) (n := n) (by omega : 0 < max m n)
  have hlt : side m n < 2*(m*n) := by omega
  have hspos := side_pos m n
  have hprod := Nat.mul_lt_mul_of_pos_left hlt hspos
  have hprod2 := Nat.mul_le_mul_right (2*(m*n)) hlt.le
  nlinarith

theorem padded_entries_le_public_power (m n S N A C₁ k : ℕ)
    (hm : 0 < m) (hn : 0 < n)
    (hN : 2 ≤ N) (hA : 2 ≤ A)
    (hentries : m*n ≤ S)
    (hS : S ≤ N^(C₁*A^k)) :
    (side m n)^2 ≤ N^((2*C₁+2)*A^k) := by
  have hpad := (padded_entries_lt_four_square m n hm hn).le
  have hSbound : m*n ≤ N^(C₁*A^k) := hentries.trans hS
  have hsq : (m*n)^2 ≤ (N^(C₁*A^k))^2 :=
    Nat.pow_le_pow_left hSbound _
  have hAk : 1 ≤ A^k := by
    have hp : 0 < A^k := by positivity
    omega
  have hfour : 4 ≤ N^(2*A^k) := by
    have hN2 : 4 ≤ N^2 := by nlinarith
    exact hN2.trans (Nat.pow_le_pow_right (by omega : 0 < N) (by omega))
  calc
    (side m n)^2 ≤ 4*(m*n)^2 := hpad
    _ ≤ 4*(N^(C₁*A^k))^2 := Nat.mul_le_mul_left 4 hsq
    _ = N^(2*(C₁*A^k)) * 4 := by rw [← pow_mul]; ring
    _ ≤ N^(2*(C₁*A^k)) * N^(2*A^k) :=
      Nat.mul_le_mul_left _ hfour
    _ = N^((2*C₁+2)*A^k) := by
      rw [← pow_add]
      congr 1
      ring

/-- Padding preserves deterministic complexity of the very same rectangle,
and its output has a power-of-two side at least the public `N`. -/
theorem padded_literal_table {m n N : ℕ}
    (hm : 0 < m) (hn : 0 < n)
    (hNdim : N ≤ max m n)
    (F : Fin m → Fin n → Bool) :
    D (matrix hm hn F) = D F ∧
    N ≤ side m n ∧
    ∃ e : ℕ, side m n = 2^e := by
  refine ⟨D_matrix hm hn F, ?_, ⟨exponent m n, rfl⟩⟩
  exact hNdim.trans (max_le_side m n)

#print axioms padded_entries_le_public_power
#print axioms padded_literal_table

end CurrentAdditive.DeterministicEndpointPadding
