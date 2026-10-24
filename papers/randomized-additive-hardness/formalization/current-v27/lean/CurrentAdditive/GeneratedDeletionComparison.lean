import CurrentAdditive.GeneratedParameterGuards
import Paper2.SourceDensitySchedule

/-! The current rational deletion rate fits the older graph theorem's
literal real allowance when every vertex is incident to an edge. -/

namespace CurrentAdditive.DeterministicIndexedMatrix

open Paper2 Paper2.SourceSurvivingCollisions
open CurrentAdditive.DeterministicParameters

theorem current_eta_le_graph_deletion
    {G E : Type*} [Fintype G] [Nonempty G] [Fintype E]
    (L Δ : ℕ) (γ : ℚ) (hΔ : 0 < Δ) (hγ : 0 < γ)
    (edge : E → Bool → G)
    (hincident : ∀ v, ∃ e b, edge e b = v) :
    (η L Δ γ : ℝ) ≤
      deletionAllowance (V := G) (E := E) (γ : ℝ) Δ (s L) := by
  have hcard := Paper2.SourceConstruction.vertices_le_twice_edges edge hincident
  have hcardR : (Fintype.card G : ℝ) ≤ 2 * Fintype.card E := by
    exact_mod_cast hcard
  have hn : (0 : ℝ) < Fintype.card G := by exact_mod_cast Fintype.card_pos (α := G)
  have hD : (0 : ℝ) < Δ := by exact_mod_cast hΔ
  have hγR : (0 : ℝ) < (γ : ℝ) := by exact_mod_cast hγ
  have hδ : (γ : ℝ) / (4 * Δ) ≤
      vertexTolerance (V := G) (E := E) (γ : ℝ) Δ := by
    unfold vertexTolerance
    apply (div_le_div_iff₀ (by positivity) (by positivity)).2
    nlinarith [mul_nonneg hγR.le (sub_nonneg.mpr hcardR)]
  have hc1 : (c Δ γ : ℝ) ≤ 1 / 65536 := by
    have hh : ((c Δ γ : ℚ) : ℝ) ≤ ((1/65536 : ℚ) : ℝ) :=
      Rat.cast_le.mpr (c_le_one Δ γ)
    simpa [Rat.cast_div] using hh
  have hc2 : (c Δ γ : ℝ) ≤ (γ : ℝ) / (4 * Δ) / 65536 := by
    have hh : ((c Δ γ : ℚ) : ℝ) ≤
        ((γ / (4 * Δ) / 65536 : ℚ) : ℝ) :=
      Rat.cast_le.mpr (c_le_deletion Δ γ)
    simpa [Rat.cast_div, Rat.cast_mul] using hh
  have hc3 : (c Δ γ : ℝ) ≤
      (1 / 256 : ℝ) * witnessDensity (γ : ℝ) / 65536 := by
    have hh : ((c Δ γ : ℚ) : ℝ) ≤
        (((1/256 : ℚ) * (γ / 24) / 65536 : ℚ) : ℝ) :=
      Rat.cast_le.mpr (c_le_mu_zeta Δ γ)
    simpa [Rat.cast_div, Rat.cast_mul, witnessDensity] using hh
  have hcnum : (c Δ γ : ℝ) ≤
      min (min 1 (vertexTolerance (V := G) (E := E) (γ : ℝ) Δ))
        ((1/256 : ℝ) * witnessDensity (γ : ℝ)) / 65536 := by
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 65536)).2
    apply le_min
    · apply le_min
      · nlinarith [hc1]
      · nlinarith [hc2, hδ]
    · nlinarith [hc3]
  have hs : (0 : ℝ) < s L := by exact_mod_cast s_pos L
  have hmain : (c Δ γ : ℝ) / (s L : ℝ) ≤
      min (min 1 (vertexTolerance (V := G) (E := E) (γ : ℝ) Δ))
        ((1/256 : ℝ) * witnessDensity (γ : ℝ)) / (65536 * s L) := by
    calc
      (c Δ γ : ℝ) / (s L : ℝ) ≤
        (min (min 1 (vertexTolerance (V := G) (E := E) (γ : ℝ) Δ))
          ((1/256 : ℝ) * witnessDensity (γ : ℝ)) / 65536) / (s L : ℝ) :=
          div_le_div_of_nonneg_right hcnum hs.le
      _ = _ := by ring
  simpa only [η, deletionAllowance, Paper2.SourceDeletionParameters.eta,
    Rat.cast_div, Rat.cast_natCast] using hmain

end CurrentAdditive.DeterministicIndexedMatrix

#print axioms CurrentAdditive.DeterministicIndexedMatrix.current_eta_le_graph_deletion
