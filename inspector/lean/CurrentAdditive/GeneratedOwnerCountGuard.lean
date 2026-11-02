import CurrentAdditive.GeneratedNearFullAtSchedule

/-! The graph-owner count in the checked rational admissibility package
is precisely the real inequality consumed by the indexed N argument. -/

namespace CurrentAdditive.DeterministicIndexedMatrix

open Paper2.SourceSurvivingCollisions
open CurrentAdditive.DeterministicParameters

theorem current_graph_owner_count_real
    (L Δ n m C : ℕ) (γ : ℚ)
    (h : Admissible L Δ n m C γ) :
    8 * (s L : ℝ) * q₁ L ≤
      witnessDensity (γ : ℝ) * q₂ L / 16 := by
  have hh : (((8 : ℚ) * s L * q₁ L : ℚ) : ℝ) ≤
      (((γ / 24) * q₂ L / 16 : ℚ) : ℝ) :=
    Rat.cast_le.mpr h.graph_owner
  simpa [witnessDensity, Rat.cast_mul, Rat.cast_div] using hh

end CurrentAdditive.DeterministicIndexedMatrix

#print axioms CurrentAdditive.DeterministicIndexedMatrix.current_graph_owner_count_real
