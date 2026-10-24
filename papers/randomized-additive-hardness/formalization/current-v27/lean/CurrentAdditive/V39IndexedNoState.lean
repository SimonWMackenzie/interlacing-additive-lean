import CurrentAdditive.V39IndexedUsable

/-! Actual retained diagonal fibres initialize the indexed collision
recursion; neither an initial tracking state nor its support facts is an
input to this source-facing continuation. -/

namespace CurrentAdditive.V39IndexedNoState

open Paper2 Paper2.SourceMatrix Paper2.SourceProjectionDiagonal
open CurrentAdditive.DeterministicIndexedMatrix
open CurrentAdditive.DeterministicIndexedMatrix.Sources
open CurrentAdditive.V38IndexedUsable
open Workspace.Types.Protocol

variable {X Y I : Type*} [Fintype X] [Fintype Y] [Fintype I]
  [DecidableEq X] [DecidableEq Y]
  {D q₁ q₂ s : ℕ} [NeZero s] [NeZero q₁] [NeZero q₂]
  {μX : PositiveRationalLaw X} {μY : PositiveRationalLaw Y}
  (src : Sources (D := D) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY)

theorem no_short_with_usable_collision_coordinates
    (hD : 8 ≤ D) (R : X → Y → Bool)
    (activity : I → Fin q₂ → Option (Fin s)) (ξ₀ : Tail s Y)
    (d a ell : ℕ) (ρ x : ℝ) (hd : 2 ≤ d) (hρ : 0 < ρ) (hx : 0 < x)
    (hs : s = 2^a) (hq : q₁+3=s+1) (hq₂ : q₂=2^ell) (hq2 : 2 ≤ q₂)
    (hscale : 2*(s : ℝ)*ρ ≤ 1) (hsmall : 2*(q₂ : ℝ)*x ≤ 1/8)
    (hprofileR : V38RestrictionProfiles.TwoThresholdProfile R
      μX.toFiniteLaw μY.toFiniteLaw ρ (d : ℤ))
    (hprofileA : V38RestrictionProfiles.TwoThresholdProfile (Sources.A src R)
      src.gamma.law.toFiniteLaw
      ((PositiveRationalLaw.uniform (Fin q₁)).prod μX).toFiniteLaw x ((d+a : ℕ) : ℤ))
    (bin : Fin s) (K : Set src.inner.Label) (A : Set (Row (I := I) src))
    (U : Set (V38IndexedTwoTag.Column src))
    (hK : ∀ z ∈ K, Sum.inl (bin,z) ∈ A)
    (hKmass : (998/1000 : ℝ) < src.inner.law.toFiniteLaw.prob (· ∈ K))
    (Marks : Finset (Fin q₂))
    (hMarks : Marks ⊆ Finset.univ \ bad src K U (2*(s : ℝ)*ρ))
    (hexcess : (bad src K U (2*(s : ℝ)*ρ)).card < Marks.card)
    (hcollision : ∀ α ∈ Marks, ∃ (i₁ i₂ i₀ : I) (p p' : Fin s), p ≠ p' ∧
      activity i₁ α = some p ∧ activity i₂ α = some p' ∧ activity i₀ α = none ∧
      ∀ t : Fin 3, 2*(s : ℝ)*ρ ≤ μX.toFiniteLaw.prob
        (fun u => Sum.inr (collisionItem i₁ i₂ i₀ t,u) ∈ A))
    (P : Protocol A (V38IndexedTwoTag.Column src) Bool)
    (hcost : P.cost ≤ d+a+ell)
    (hcorrect : ∀ a c, c ∈ U →
      P.eval a c = V38IndexedTwoTag.matrix src R activity ξ₀ c a.val) : False := by
  classical
  let Bad := bad src K U (2*(s : ℝ)*ρ)
  let initial := initialState src P U Bad Marks
  obtain ⟨hcount,hmass,hreaches,hhead⟩ :=
    initial_facts src P K U (2*(s : ℝ)*ρ) Marks
  change initial.coordinates.card + Bad.card = q₂ at hcount
  change Bad.card < Marks.card at hexcess
  have hmarkCount : Marks.card ≤ initial.coordinates.card := Finset.card_le_card hMarks
  have hb : Bad.card < q₂ := by omega
  apply V38IndexedTwoTag.no_short_remaining_protocol src hD R activity ξ₀
    d a ell Bad.card ρ x hd hρ hx hs hq hq₂ hq2 hb hscale hsmall
    hprofileR hprofileA bin K A hK hKmass initial hcost hcorrect hcount hexcess
    hMarks hmass hreaches
  · intro α hα i
    exact hhead α (hMarks hα) i
  · exact hcollision

end CurrentAdditive.V39IndexedNoState

#print axioms CurrentAdditive.V39IndexedNoState.no_short_with_usable_collision_coordinates
