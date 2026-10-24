import CurrentAdditive.CylinderSource

/-!
Private numerical bound for v27 Appendix H, `det:code-size`.
This is arithmetic only; the executable support reducer is separate.
-/

namespace CurrentAdditive

open Finset Paper2

private theorem geometric_sum_le_one_add_pow (D x : ℕ) :
    (∑ j ∈ range (D + 1), x ^ j) ≤ (1 + x) ^ D := by
  rw [show 1 + x = x + 1 by omega, add_pow]
  simp only [one_pow, mul_one]
  apply Finset.sum_le_sum
  intro j hj
  have hjD : j ≤ D := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  calc
    x ^ j = x ^ j * 1 := by simp
    _ ≤ x ^ j * Nat.choose D j :=
      Nat.mul_le_mul_left _ (Nat.choose_pos hjD)

/-- The manuscript's binomial moment count is at most its displayed
degree-`D` polynomial envelope. The proof also covers zero parameters. -/
theorem moment_count_le_one_add_pow (q D m : ℕ) :
    (∑ j ∈ range (min D q + 1), Nat.choose q j * m ^ j) ≤
      (1 + q * m) ^ D := by
  calc
    (∑ j ∈ range (min D q + 1), Nat.choose q j * m ^ j) ≤
        ∑ j ∈ range (min D q + 1), (q * m) ^ j := by
      apply Finset.sum_le_sum
      intro j hj
      calc
        Nat.choose q j * m ^ j ≤ q ^ j * m ^ j :=
          Nat.mul_le_mul_right _ (Nat.choose_le_pow q j)
        _ = (q * m) ^ j := (mul_pow q m j).symm
    _ ≤ ∑ j ∈ range (D + 1), (q * m) ^ j := by
      exact Finset.sum_le_sum_of_subset (Finset.range_mono (by omega))
    _ ≤ (1 + q * m) ^ D := geometric_sum_le_one_add_pow D (q * m)

theorem cylinder_card_le_one_add_pow {Y : Type*} [Fintype Y]
    (q D : ℕ) :
    Fintype.card (Cylinder q D Y) ≤ (1 + q * Fintype.card Y) ^ D := by
  rw [cylinder_card_eq_moment_count]
  exact moment_count_le_one_add_pow q D (Fintype.card Y)

/-- Numerical envelope for the existing positive-rational, exactly
`D`-wise-independent existence theorem. This makes no algorithmic claim. -/
theorem exists_rational_dwise_source_le_one_add_pow
    {Y : Type*} [Fintype Y] [DecidableEq Y]
    (q D : ℕ) (μ : PositiveRationalLaw Y) :
    ∃ (t : Finset (Fin q → Y)) (ν : PositiveRationalLaw t),
      t.card ≤ (1 + q * Fintype.card Y) ^ D ∧
      IsDWise D ν.toFiniteLaw (fun x : t => x.1) μ.toFiniteLaw := by
  obtain ⟨t, ν, hcard, hwise⟩ := exists_rational_dwise_source q D μ
  exact ⟨t, ν,
    hcard.trans (moment_count_le_one_add_pow q D (Fintype.card Y)), hwise⟩

#print axioms moment_count_le_one_add_pow
#print axioms cylinder_card_le_one_add_pow
#print axioms exists_rational_dwise_source_le_one_add_pow

end CurrentAdditive
