import CurrentAdditive.V38FullRemaining
import CurrentAdditive.V38FullUsable

/-! The actual retained diagonal fibres initialize collision tracking.
This removes the State/mass/reaches certificates from the source-facing
remaining-conversation theorem. Geometry of the marked coordinates and
the earlier prefix still remain separate source-proof obligations. -/

namespace CurrentAdditive.V38FullNoState

open Paper2 Paper2.SourceMatrix Paper2.SourceProjectionDiagonal
open CurrentAdditive.EdgeSourceMatrix CurrentAdditive.V38Matrix
open CurrentAdditive.V38FullUsable
open Workspace.Types.Protocol

variable {V E X Y : Type*} [Fintype V] [Fintype E]
  [Fintype X] [Fintype Y] {s q₁ q₂ : ℕ} [NeZero s] [NeZero q₁] [NeZero q₂]

theorem no_short_with_usable_collision_coordinates
    (order : Items s V ≃ Fin (Fintype.card (Items s V)))
    (edge : E → Bool → V) (hs : 3 ≤ s) (r : ℕ)
    (hsourceq : q₂ = EdgeSource.sourceQ0 (Fin (4*s)) E * r)
    (μ : PositiveRationalLaw X) (ν : PositiveRationalLaw Y)
    (R : X → Y → Bool) (ξ₀ : Tail s Y)
    (H ell : ℕ) (hq : q₂ = 2^ell) (hq2 : 2 ≤ q₂) (hH : 2 ≤ H)
    (x xcap : ℝ) (hx : 0 < x) (hsmall : 2*(q₂ : ℝ)*x ≤ 1/8)
    (hprofile : V38RestrictionProfiles.TwoThresholdProfile
      (fun (γ : Word q₁ s Y) j => M₁ R j γ)
      (ν.iid (q₁+s+1)).toFiniteLaw
      ((PositiveRationalLaw.uniform (Fin q₁)).prod μ).toFiniteLaw x (H : ℤ))
    (threeTail : ∀ (Rows : Set (Fin (q₁+3) × X))
      (Words : Set (Fin (q₁+3) → Y)),
      (∀ i, xcap ≤ μ.toFiniteLaw.prob (fun u => (i,u) ∈ Rows)) →
      (1/2 : ℝ) < (ν.iid (q₁+3)).toFiniteLaw.prob (· ∈ Words) →
      H+1 ≤ Compression.restrictionD (fullInterlace R (q₁+3)) Rows Words)
    (bin : Fin s) (K : Set (Template q₁ q₂ X))
    (A : Set (RawRow q₁ q₂ s X (Items s V)))
    (U : Set (V38Matrix.TaggedColumn q₁ q₂ s Y))
    (hK : ∀ z ∈ K, Sum.inl (bin,z) ∈ A)
    (hKmass : (998/1000 : ℝ) <
      (SourceLaws.templateLaw μ q₁ q₂).toFiniteLaw.prob (· ∈ K))
    (Marks : Finset (Fin q₂))
    (hMarks : Marks ⊆ Finset.univ \ bad μ ν K U xcap)
    (hexcess : (bad μ ν K U xcap).card < Marks.card)
    (hcollision : ∀ α ∈ Marks,
      ∃ (i₁ i₂ i₀ : Items s V) (p p' : Fin s), p ≠ p' ∧
        activity order edge hs r hsourceq i₁ α = some p ∧
        activity order edge hs r hsourceq i₂ α = some p' ∧
        activity order edge hs r hsourceq i₀ α = none ∧
        ∀ t : Fin 3, xcap ≤ μ.toFiniteLaw.prob
          (fun u => Sum.inr (collisionItem i₁ i₂ i₀ t,u) ∈ A))
    (P : Protocol A (V38Matrix.TaggedColumn q₁ q₂ s Y) Bool)
    (hcost : P.cost ≤ H+ell)
    (hcorrect : ∀ a c, c ∈ U →
      P.eval a c = V38Matrix.matrix order edge hs r hsourceq R ξ₀ c a.val) : False := by
  classical
  let Bad := bad μ ν K U xcap
  let initial := initialState P U Bad Marks
  have hcount : initial.coordinates.card + Bad.card = q₂ := initial_count P U Bad Marks
  have hmarkCount : Marks.card ≤ initial.coordinates.card := Finset.card_le_card hMarks
  have hb : Bad.card < q₂ := by omega
  apply V38FullRemaining.no_short_remaining_protocol order edge hs r hsourceq
    μ ν R ξ₀ H ell Bad.card hq hq2 hb hH x xcap hx hsmall hprofile
    threeTail bin K A hK hKmass initial hcost hcorrect hcount hexcess
    hMarks (initial_mass μ ν K U xcap P Marks) (initial_reaches P U Bad Marks)
  · intro α hα i
    have hn : α ∉ Bad := (Finset.mem_sdiff.mp (hMarks hα)).2
    exact (usable_masses μ ν K U xcap α hn).1 i
  · exact hcollision

end CurrentAdditive.V38FullNoState

#print axioms CurrentAdditive.V38FullNoState.no_short_with_usable_collision_coordinates
