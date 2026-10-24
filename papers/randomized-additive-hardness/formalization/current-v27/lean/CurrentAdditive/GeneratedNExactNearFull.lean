import CurrentAdditive.GeneratedNUpperAtSchedule

/-! Complete `det:near-full` statement for the literal generated indexed N:
the universal upper protocol and every near-full restriction meet at C. -/

namespace CurrentAdditive.DeterministicIndexedMatrix.Sources

open Paper2 Paper2.SourceMatrix Paper2.SourceSurvivingCollisions
open Workspace.Types.CommComplexity
open CurrentAdditive.DeterministicParameters

variable {G E X Y : Type*} [Fintype G] [Nonempty G] [Fintype E]
  [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
  {μX : PositiveRationalLaw X} {μY : PositiveRationalLaw Y}

theorem generated_N_exact_near_full
    (L Δ Caux : ℕ) (γ : ℚ) (hL : 2004 ≤ L)
    (hΔ : 0 < Δ) (hγ : 0 < γ)
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
    (hadm : Admissible L Δ (Fintype.card G) (Fintype.card E) Caux γ) :
    let activity := SourceConstruction.activity order edge
      (by have hs := s_ge_64 L (by omega); omega : 3 ≤ s L) r hqSource
    let F := N src R activity ξ₀
    D F = d+(L+3)/4+4*L+(L+3)/4+1 ∧
    ∀ (U : Set (Column src))
      (V : Set (Row (I := SourceConstruction.Items (s L) G) src)),
      1 - (η L Δ γ : ℝ) ≤ (columnLaw src).toFiniteLaw.prob (· ∈ U) →
      1 - (η L Δ γ : ℝ) ≤
        (rowLaw src
          (itemLaw (G := Fin (4*s L)) (V := G) (A := Fin (s L-3)))).toFiniteLaw.prob
            (· ∈ V) →
      d+(L+3)/4+4*L+(L+3)/4+1 ≤
        Paper2.Compression.restrictionD F U V := by
  classical
  dsimp
  let activity := SourceConstruction.activity order edge
    (by have hs := s_ge_64 L (by omega); omega : 3 ≤ s L) r hqSource
  let F := N src R activity ξ₀
  let c := d+(L+3)/4+4*L+(L+3)/4+1
  have hcount := current_graph_owner_count_real L Δ
    (Fintype.card G) (Fintype.card E) Caux γ hadm
  have hnear (U : Set (Column src))
      (V : Set (Row (I := SourceConstruction.Items (s L) G) src))
      (hU : 1 - (η L Δ γ : ℝ) ≤
        (columnLaw src).toFiniteLaw.prob (· ∈ U))
      (hV : 1 - (η L Δ γ : ℝ) ≤
        (rowLaw src
          (itemLaw (G := Fin (4*s L)) (V := G) (A := Fin (s L-3)))).toFiniteLaw.prob
            (· ∈ V)) :
      c ≤ Paper2.Compression.restrictionD F U V := by
    by_contra hn
    have hshort : Paper2.Compression.restrictionD F U V ≤
        d+(L+3)/4+4*L+(L+3)/4 := by
      dsimp [c] at hn
      omega
    exact generated_near_full_at_schedule L Δ γ hL hΔ hγ src
      R order edge loopless hincident r hqSource hdegree gap ξ₀
      d hd hD hprofileR V hV U hU hcount hshort
  have hη : (0 : ℝ) ≤ (η L Δ γ : ℝ) := by
    exact_mod_cast (eta_pos L Δ γ hΔ hγ).le
  have hUfull : 1 - (η L Δ γ : ℝ) ≤
      (columnLaw src).toFiniteLaw.prob (· ∈ (Set.univ : Set (Column src))) := by
    simpa using (show 1 - (η L Δ γ : ℝ) ≤ 1 by linarith)
  have hVfull : 1 - (η L Δ γ : ℝ) ≤
      (rowLaw src
        (itemLaw (G := Fin (4*s L)) (V := G) (A := Fin (s L-3)))).toFiniteLaw.prob
          (· ∈ (Set.univ : Set (Row (I := SourceConstruction.Items (s L) G) src))) := by
    simpa using (show 1 - (η L Δ γ : ℝ) ≤ 1 by linarith)
  have hfull := hnear Set.univ Set.univ hUfull hVfull
  have huniv : Paper2.Compression.restrictionD F Set.univ Set.univ = D F := by
    have hh := pullback_D_eq_of_surjective F Subtype.val Subtype.val
      (fun z => ⟨⟨z, Set.mem_univ z⟩, rfl⟩)
      (fun z => ⟨⟨z, Set.mem_univ z⟩, rfl⟩)
    exact hh
  rw [huniv] at hfull
  have hu : D F ≤ c := by
    have hh := generated_N_upper_at_schedule L hL src activity ξ₀ R d hD
    simpa [F, c] using hh
  constructor
  · exact Nat.le_antisymm hu hfull
  · intro U V hU hV
    exact hnear U V hU hV

end CurrentAdditive.DeterministicIndexedMatrix.Sources

#print axioms CurrentAdditive.DeterministicIndexedMatrix.Sources.generated_N_exact_near_full
