import CurrentAdditive.GeneratedDeletionComparison

/-! The current dyadic schedule and checked A/T profiles feed the
source-specific near-full contradiction on the literal indexed matrix. -/

namespace CurrentAdditive.DeterministicIndexedMatrix.Sources

open Paper2 Paper2.SourceMatrix Paper2.SourceSurvivingCollisions
open CurrentAdditive.DeterministicParameters
open Workspace.Types.CommComplexity

variable {G E X Y : Type*} [Fintype G] [Nonempty G] [Fintype E]
  [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
  {μX : PositiveRationalLaw X} {μY : PositiveRationalLaw Y}

theorem generated_near_full_at_schedule
    (L Δ : ℕ) (γ : ℚ) (hL : 2004 ≤ L) (hΔ : 0 < Δ) (hγ : 0 < γ)
    [NeZero (q₁ L)] [NeZero (q₂ L)] [NeZero (s L)]
    [Nonempty (Fin (4*s L))] [Nonempty (Fin (s L-3))]
    (src : Sources (D := 8192) (q₁ := q₁ L) (q₂ := q₂ L)
      (s := s L) μX μY)
    (R : X → Y → Bool)
    (order : SourceConstruction.Items (s L) G ≃
      Fin (Fintype.card (SourceConstruction.Items (s L) G)))
    (edge : E → Bool → G)
    (loopless : ∀ e, edge e false ≠ edge e true)
    (hincident : ∀ v, ∃ e b, edge e b = v)
    (r : ℕ)
    (hqSource : q₂ L = SourceItems.sourceQ0 (Fin (4*s L)) E * r)
    (hdegree : ∀ v, SourceItems.degree edge v ≤ Δ)
    (gap : ∀ colour : G → Fin 3,
      (γ : ℝ) * Fintype.card E ≤
      ((Finset.univ.filter (fun e =>
        colour (edge e false) = colour (edge e true))).card : ℝ))
    (ξ₀ : Tail (s L) Y) (d : ℕ) (hd : 3 ≤ d)
    (hD : D R = d)
    (hprofileR : RestrictionProfile R μX.toFiniteLaw μY.toFiniteLaw
      (ρ L : ℝ) (d : ℤ))
    (V : Set (Row (I := SourceConstruction.Items (s L) G) src))
    (hV : 1 - (η L Δ γ : ℝ) ≤
      (rowLaw src
        (itemLaw (G := Fin (4*s L)) (V := G) (A := Fin (s L-3)))).toFiniteLaw.prob
          (· ∈ V))
    (U : Set (Column src))
    (hU : 1 - (η L Δ γ : ℝ) ≤
      (columnLaw src).toFiniteLaw.prob (· ∈ U))
    (hcount : 8 * (s L : ℝ) * q₁ L ≤
      witnessDensity (γ : ℝ) * q₂ L / 16)
    (hshort : Paper2.Compression.restrictionD
      (N src R (SourceConstruction.activity order edge
        (by have hs := s_ge_64 L (by omega); omega : 3 ≤ s L)
        r hqSource) ξ₀) U V ≤
      d+(L+3)/4+4*L+(L+3)/4) : False := by
  have hs : 4 ≤ s L := by have hh := s_ge_64 L (by omega); omega
  letI : Nonempty (Fin (4*2^((L+3)/4))) := ⟨⟨0, by
    have hh : 4 ≤ 2^((L+3)/4) := by simpa [s] using hs
    omega⟩⟩
  letI : Nonempty (Fin (2^((L+3)/4)-3)) := ⟨⟨0, by
    have hh : 4 ≤ 2^((L+3)/4) := by simpa [s] using hs
    omega⟩⟩
  have hqHead : q₁ L + 3 = s L + 1 := by
    unfold q₁
    omega
  have hηshadow := current_eta_le_graph_deletion L Δ γ hΔ hγ edge hincident
  have hηguards := current_retention_guards L Δ γ hΔ hγ
  have hSchedule := current_coordinate_budget L Δ γ hγ hηshadow hcount
  have hsmall : Paper2.SourceSupportSchedule.floor (q₂ L) (x L : ℝ) 0 ≤
      1/8 := by
    rw [Paper2.SourceSupportSchedule.floor_zero]
    have hh := two_q₂_x_small L (by omega)
    have hr : ((2 * (q₂ L : ℚ) * x L : ℚ) : ℝ) ≤
        ((1/8 : ℚ) : ℝ) := Rat.cast_le.mpr hh
    simpa [Rat.cast_mul, Rat.cast_div] using hr
  have hscale : 4 * (s L : ℝ)^2 * (ρ L : ℝ) ≤ 1 := by
    have hh := four_s_sq_rho L (by omega)
    exact_mod_cast hh
  have hxbudget : (s L : ℝ) * (x L : ℝ) ≤ 1/10000 := by
    have hh := (scalar_x_all_small L (by omega)).2.1
    have hr : (((s L : ℚ) * x L : ℚ) : ℝ) ≤
        ((1/10000 : ℚ) : ℝ) := Rat.cast_le.mpr hh
    simpa [Rat.cast_mul, Rat.cast_div] using hr
  let activity := SourceConstruction.activity order edge
    (by omega : 3 ≤ s L) r hqSource
  obtain ⟨_, hA, _, hT, _⟩ :=
    generated_profiles_at_parameters L hL src
      (itemLaw (G := Fin (4*s L)) (V := G) (A := Fin (s L-3)))
      R activity ξ₀ d hd hD hprofileR
  have hE : 0 < Fintype.card E :=
    Paper2.SourceDensityScheduleScratch.edges_pos edge hincident
  have hη : (0 : ℝ) < (η L Δ γ : ℝ) := by
    exact_mod_cast eta_pos L Δ γ hΔ hγ
  have hρQ : (0 : ℚ) < ρ L := by
    unfold ρ
    have hN : (0 : ℚ) < DeterministicParameters.N L := by
      exact_mod_cast N_pos L
    positivity
  have hρ : (0 : ℝ) < (ρ L : ℝ) := by exact_mod_cast hρQ
  exact generated_near_full_of_total_mass (a := (L+3)/4) src R order edge loopless
    (by simpa [s] using hs) r Δ hΔ hqSource hdegree
    (γ : ℝ) (by exact_mod_cast hγ) hE gap ξ₀ d (4*L)
    (ρ L : ℝ) (x L : ℝ) (x L : ℝ) (η L Δ γ : ℝ)
    (by omega) (by omega) hρ (x_real_pos L)
    (x_real_pos L) hη
    (by simpa [s] using hqHead) (q₂_eq_pow L) (by simpa [s] using hscale)
    hsmall hprofileR hA hT V hV U hU hηshadow
    (by simpa [s] using hηguards.1) hηguards.2
    (by simpa [s] using hxbudget) (by simpa [s] using hSchedule) hshort

end CurrentAdditive.DeterministicIndexedMatrix.Sources

#print axioms CurrentAdditive.DeterministicIndexedMatrix.Sources.generated_near_full_at_schedule
