import CurrentAdditive.GeneratedNearFullTotalMass
import CurrentAdditive.DeterministicParameters
import CurrentAdditive.IndexedProfileSchedule

/-! Numerical bridges from the checked current schedule to the actual
retention and collision inequalities. -/

namespace CurrentAdditive.DeterministicIndexedMatrix

open Paper2 Paper2.SourceSurvivingCollisions
open CurrentAdditive.DeterministicParameters

theorem current_retention_guards (L Δ : ℕ) (γ : ℚ)
    (hΔ : 0 < Δ) (hγ : 0 < γ) :
    (256/255 : ℝ) * (s L : ℕ) * (η L Δ γ : ℝ) ≤ 1/1000 ∧
    (256 : ℝ) * (η L Δ γ : ℝ) ≤ 1/100 := by
  have h := fixed_eta_guards L Δ γ hΔ hγ
  have hrowQ : (256/255 : ℚ) * (s L : ℚ) * η L Δ γ ≤ 1/1000 := by
    have he : η L Δ γ * s L / (255/256 : ℚ) =
        (256/255 : ℚ) * (s L : ℚ) * η L Δ γ := by ring
    rw [he] at h
    exact h.2.1.le
  have hfixedQ : (256 : ℚ) * η L Δ γ ≤ 1/100 := by
    have he : η L Δ γ / (1/256 : ℚ) = 256 * η L Δ γ := by ring
    rw [he] at h
    exact h.1.le
  constructor
  · have hh : (((256/255 : ℚ) * (s L : ℚ) * η L Δ γ : ℚ) : ℝ) ≤
        ((1/1000 : ℚ) : ℝ) := Rat.cast_le.mpr hrowQ
    simpa [Rat.cast_mul, Rat.cast_div] using hh
  · have hh : (((256 : ℚ) * η L Δ γ : ℚ) : ℝ) ≤
        ((1/100 : ℚ) : ℝ) := Rat.cast_le.mpr hfixedQ
    simpa [Rat.cast_mul, Rat.cast_div] using hh

theorem current_coordinate_budget {G E : Type*}
    [Fintype G] [Nonempty G] [Fintype E]
    (L Δ : ℕ) (γ : ℚ) (hγ : 0 < γ)
    (hηshadow : (η L Δ γ : ℝ) ≤
      deletionAllowance (V := G) (E := E) (γ : ℝ) Δ (s L))
    (hcount : 8 * (s L : ℝ) * q₁ L ≤
      witnessDensity (γ : ℝ) * q₂ L / 16) :
    8 * (s L : ℝ) * q₁ L +
      1024 * s L * (η L Δ γ : ℝ) * q₂ L <
      witnessDensity (γ : ℝ) * q₂ L / 4 := by
  have hz : 0 < witnessDensity (γ : ℝ) := by
    unfold witnessDensity
    exact div_pos (by exact_mod_cast hγ) (by norm_num)
  have hcoord := Paper2.SourceDeletionParameters.coordinate_allowance
    (s L) (q₁ L) (q₂ L) (s_pos L) (q₂_pos L)
    (vertexTolerance (V := G) (E := E) (γ : ℝ) Δ)
    (witnessDensity (γ : ℝ)) hz hcount
  change (η L Δ γ : ℝ) ≤
    Paper2.SourceDeletionParameters.eta (s L)
      (vertexTolerance (V := G) (E := E) (γ : ℝ) Δ)
      (witnessDensity (γ : ℝ)) at hηshadow
  have hfactor : 0 ≤ (1024 : ℝ) * s L * q₂ L := by positivity
  have hh := mul_le_mul_of_nonneg_left hηshadow hfactor
  nlinarith

end CurrentAdditive.DeterministicIndexedMatrix

#print axioms CurrentAdditive.DeterministicIndexedMatrix.current_retention_guards
#print axioms CurrentAdditive.DeterministicIndexedMatrix.current_coordinate_budget
