import CurrentAdditive.GeneratedWAlignmentMass

/-! The three numerical terms in Appendix I's owner-to-owner receipt sum.
The copy count is bounded by the original index set, and the ordinary defect
sum is paid under the original row law. -/

namespace CurrentAdditive.DeterministicIndexedMatrix.Sources

open scoped BigOperators

theorem indexed_pair_receipt_scalar
    {Owners : Type*} [Fintype Owners]
    (w q₂ : ℕ) (x η : ℝ) (ε : Owners → ℝ)
    (hη : 0 ≤ η) (hx : 0 ≤ x) (hq : 0 < q₂)
    (hcard : Fintype.card Owners ≤ w)
    (hε : (Finset.univ.sum ε) ≤ η / (8 * (127/128 : ℝ)))
    (hloss1 : 4 * (1/256 : ℝ) * w * q₂ * x ≤ η/32)
    (hloss2 : 4 * (1/256 : ℝ) * w / q₂ ≤ η/32) :
    2 * (1/256 : ℝ) * w *
      (Finset.univ.sum (fun v : Owners =>
        2 * q₂ * x + 5 * ε v + 2 / q₂)) ≤
      3 * η * w / 32 := by
  let n : ℝ := Fintype.card Owners
  let S : ℝ := Finset.univ.sum ε
  have hcardR : n ≤ w := by dsimp [n]; exact_mod_cast hcard
  have hqR : (0 : ℝ) < q₂ := by exact_mod_cast hq
  have ht : 0 ≤ 2 * (q₂ : ℝ) * x + 2 / q₂ := by positivity
  have hsum :
      (Finset.univ.sum (fun v : Owners =>
        2 * q₂ * x + 5 * ε v + 2 / q₂)) =
      n * (2 * q₂ * x + 2 / q₂) + 5 * S := by
    simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul,
      ← Finset.mul_sum]
    dsimp [n, S]
    ring
  have hcountTerm : n * (2 * q₂ * x + 2 / q₂) ≤
      (w : ℝ) * (2 * q₂ * x + 2 / q₂) :=
    mul_le_mul_of_nonneg_right hcardR ht
  have hμw : 0 ≤ 2 * (1/256 : ℝ) * w := by positivity
  have hA : 4 * (1/256 : ℝ) * w * q₂ * x * w ≤ η * w / 32 := by
    have hm := mul_le_mul_of_nonneg_right hloss1
      (by exact_mod_cast Nat.zero_le w : (0 : ℝ) ≤ w)
    nlinarith
  have hB : 4 * (1/256 : ℝ) * w / q₂ * w ≤ η * w / 32 := by
    have hm := mul_le_mul_of_nonneg_right hloss2
      (by exact_mod_cast Nat.zero_le w : (0 : ℝ) ≤ w)
    nlinarith
  have hε' : 10 * (1/256 : ℝ) * w * S ≤ η * w / 32 := by
    have hm := mul_le_mul_of_nonneg_left hε hμw
    have hm5 := mul_le_mul_of_nonneg_left hm (by norm_num : (0 : ℝ) ≤ 5)
    have hwR : 0 ≤ (w : ℝ) := by positivity
    have hcoeff : 5 * (2 * (1/256 : ℝ) * w *
        (η / (8 * (127/128 : ℝ)))) = (5/1016 : ℝ) * η * w := by
      norm_num
      ring
    rw [hcoeff] at hm5
    dsimp [S] at hm5 ⊢
    nlinarith [hm5, mul_nonneg hη hwR]
  rw [hsum]
  have hmono := mul_le_mul_of_nonneg_left hcountTerm hμw
  calc
    _ ≤ 2 * (1/256 : ℝ) * w *
        ((w : ℝ) * (2 * q₂ * x + 2 / q₂) + 5 * S) := by
      nlinarith [hmono]
    _ = 4 * (1/256 : ℝ) * w * q₂ * x * w +
        4 * (1/256 : ℝ) * w / q₂ * w +
        10 * (1/256 : ℝ) * w * S := by ring
    _ ≤ η*w/32 + η*w/32 + η*w/32 := by
      exact add_le_add (add_le_add hA hB) hε'
    _ = 3 * η * w / 32 := by ring

end CurrentAdditive.DeterministicIndexedMatrix.Sources

#print axioms CurrentAdditive.DeterministicIndexedMatrix.Sources.indexed_pair_receipt_scalar
