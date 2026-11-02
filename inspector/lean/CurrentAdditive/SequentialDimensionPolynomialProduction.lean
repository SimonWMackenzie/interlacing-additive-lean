import CurrentAdditive.SequentialFeatureCount

/-! The exact literal feature count obeys Appendix H's polynomial estimate. -/

namespace CurrentAdditive.SequentialDimensionPolynomialProduction

open SequentialFeatureCount

theorem momentCount_le_polynomial (q D m : Nat) :
    (∑ k ∈ Finset.range (min D q + 1), q.choose k * m ^ k) ≤
      (1 + q * m) ^ D := by
  let x := q * m
  have hbinom : (1 + x) ^ D =
      ∑ k ∈ Finset.range (D + 1), D.choose k * x ^ k := by
    conv_lhs => rw [add_comm 1 x]
    rw [add_pow]
    apply Finset.sum_congr rfl
    intro k hk
    simp [mul_comm]
  have hsubset : Finset.range (min D q + 1) ⊆ Finset.range (D + 1) := by
    exact Finset.range_mono (by omega)
  have hterm : ∀ k ∈ Finset.range (min D q + 1),
      q.choose k * m ^ k ≤ D.choose k * x ^ k := by
    intro k hk
    have hkD : k ≤ D := by
      have := Finset.mem_range.mp hk
      omega
    have hcoef : 1 ≤ D.choose k := Nat.choose_pos hkD
    calc
      q.choose k * m ^ k ≤ q ^ k * m ^ k :=
        Nat.mul_le_mul_right _ (Nat.choose_le_pow q k)
      _ = x ^ k := by simp [x, mul_pow]
      _ = 1 * x ^ k := by simp
      _ ≤ D.choose k * x ^ k := Nat.mul_le_mul_right _ hcoef
  calc
    (∑ k ∈ Finset.range (min D q + 1), q.choose k * m ^ k) ≤
        ∑ k ∈ Finset.range (min D q + 1), D.choose k * x ^ k :=
          Finset.sum_le_sum hterm
    _ ≤ ∑ k ∈ Finset.range (D + 1), D.choose k * x ^ k := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
      intro k hk hnot
      exact Nat.zero_le _
    _ = (1 + q * m) ^ D := by simpa [x] using hbinom.symm

theorem generatedFeatures_size_le_polynomial {Y : Type*}
    (q D : Nat) (alphabet : Array Y) :
    (SequentialCode.generatedFeatures q D alphabet).size ≤
      (1 + q * alphabet.size) ^ D := by
  rw [generatedFeatures_size_min]
  exact momentCount_le_polynomial q D alphabet.size

#print axioms momentCount_le_polynomial
#print axioms generatedFeatures_size_le_polynomial

end CurrentAdditive.SequentialDimensionPolynomialProduction
