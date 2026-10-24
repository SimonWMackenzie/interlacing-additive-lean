import CurrentAdditive.ExactCountBridge

/-! Rational-input wrapper for the exact integer exceptional count. -/
namespace CurrentAdditive.PublicScheduleRationalCount

def exactCount (b : ℕ) (τ : ℚ) : ℕ :=
  8 * CurrentAdditive.PublicScheduleIntegerPower.firstPowerWitness
    b τ.num.toNat τ.den

theorem rat_as_positive_fraction (τ : ℚ) (hτ : 0 < τ) :
    (τ : ℝ) = ((τ.num.toNat : ℕ) : ℝ) / (τ.den : ℝ) := by
  have hn : 0 ≤ τ.num := (Rat.num_pos.mpr hτ).le
  have hnum : (τ.num.toNat : ℤ) = τ.num := Int.toNat_of_nonneg hn
  rw [Rat.cast_def]
  congr 1
  exact_mod_cast hnum.symm

theorem exactCount_eq_source (b : ℕ) (τ : ℚ) (hτ : 0 < τ) :
    exactCount b τ =
      CurrentAdditive.conditioningExceptionCount
        ((2 : ℝ) ^ (-(b : ℝ))) (τ : ℝ) := by
  have hp : 0 < τ.num.toNat := by
    have hpos : 0 < τ.num := Rat.num_pos.mpr hτ
    have hn : 0 ≤ τ.num := hpos.le
    have hnum : (τ.num.toNat : ℤ) = τ.num := Int.toNat_of_nonneg hn
    omega
  have hq : 0 < τ.den := τ.den_pos
  rw [rat_as_positive_fraction τ hτ]
  exact (CurrentAdditive.PublicScheduleExactCount.source_count_eq_integer_witness
    b τ.num.toNat τ.den hp hq).symm

#print axioms rat_as_positive_fraction
#print axioms exactCount_eq_source

end CurrentAdditive.PublicScheduleRationalCount
