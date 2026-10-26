import CurrentAdditive.V38AfterAlice
import CurrentAdditive.V38ActualWitness

/-!
The selected v39/v38 near-full proof after one actual prefix part has been
selected, robustness.tex:245--278. This constructs all three suppliers on
the literal two-family matrix and runs the admitted sharp conservation
theorem. It does not construct the preceding prefix, item assignment,
bad-coordinate count or initial state; those geometric inputs remain explicit.
-/

namespace CurrentAdditive.V38FullRemaining

open Paper2 Paper2.SourceMatrix Paper2.SourceProjection
open Paper2.SourceProjectionDiagonal Paper2.SourceSupportFrontier
open CurrentAdditive.EdgeSourceMatrix CurrentAdditive.V38Matrix
open Workspace.Types.Protocol

variable {V E X Y : Type*} [Fintype V] [Fintype E]
  [Fintype X] [Fintype Y] {s q₁ q₂ : ℕ} [NeZero s] [NeZero q₁]

theorem template_eightwise (μ : PositiveRationalLaw X) :
    IsDWise 8 (SourceLaws.templateLaw μ q₁ q₂).toFiniteLaw
      (fun z (α : Fin q₂) => z α)
      ((PositiveRationalLaw.uniform (Fin q₁)).prod μ).toFiniteLaw := by
  classical
  intro S _ E
  simp only [SourceLaws.templateLaw, PositiveRationalLaw.toFiniteLaw_iid]
  exact FiniteLaw.pi_prob_restrict
    (fun _ : Fin q₂ => ((PositiveRationalLaw.uniform (Fin q₁)).prod μ).toFiniteLaw)
    (fun α : S => α.val) Subtype.val_injective E

theorem no_short_remaining_protocol
    (order : Items s V ≃ Fin (Fintype.card (Items s V)))
    (edge : E → Bool → V) (hs : 3 ≤ s) (r : ℕ)
    (hsourceq : q₂ = EdgeSource.sourceQ0 (Fin (4 * s)) E * r)
    (μ : PositiveRationalLaw X) (ν : PositiveRationalLaw Y)
    (R : X → Y → Bool) (ξ₀ : Tail s Y)
    (H ell b : ℕ) (hq : q₂ = 2 ^ ell) (hq2 : 2 ≤ q₂)
    (hb : b < q₂) (hH : 2 ≤ H) (x xcap : ℝ) (hx : 0 < x)
    (hsmall : 2 * (q₂ : ℝ) * x ≤ 1 / 8)
    (hprofile : V38RestrictionProfiles.TwoThresholdProfile
      (fun (γ : Word q₁ s Y) j => M₁ R j γ)
      (ν.iid (q₁ + s + 1)).toFiniteLaw
      ((PositiveRationalLaw.uniform (Fin q₁)).prod μ).toFiniteLaw x (H : ℤ))
    (threeTail : ∀ (Rows : Set (Fin (q₁ + 3) × X))
      (Words : Set (Fin (q₁ + 3) → Y)),
      (∀ a : Fin (q₁ + 3), xcap ≤ μ.toFiniteLaw.prob (fun u => (a, u) ∈ Rows)) →
      (1 / 2 : ℝ) < (ν.iid (q₁ + 3)).toFiniteLaw.prob (· ∈ Words) →
      H + 1 ≤ Compression.restrictionD (fullInterlace R (q₁ + 3)) Rows Words)
    (bin : Fin s) (K : Set (Template q₁ q₂ X))
    (A : Set (RawRow q₁ q₂ s X (Items s V)))
    (hK : ∀ z ∈ K, Sum.inl (bin, z) ∈ A)
    (hKmass : (998 / 1000 : ℝ) <
      (SourceLaws.templateLaw μ q₁ q₂).toFiniteLaw.prob (· ∈ K))
    (initial : State A (V38Matrix.TaggedColumn q₁ q₂ s Y)
      (Fin q₂) (Word q₁ s Y))
    (hcost : initial.protocol.cost ≤ H + ell)
    (hcorrect : ∀ a c, c ∈ initial.columns →
      initial.protocol.eval a c = V38Matrix.matrix order edge hs r hsourceq R ξ₀ c a.val)
    (hcount : initial.coordinates.card + b = q₂)
    (hexcess : b < initial.attachments.card)
    (hmarked : initial.attachments ⊆ initial.coordinates)
    (hmass : ∀ α ∈ initial.coordinates, (3 / 4 : ℝ) ≤
      SourceSupportStep.mass (ν.iid (q₁ + s + 1)).toFiniteLaw (initial.support α))
    (hreaches : ∀ α ∈ initial.coordinates, ∀ γ ∈ initial.support α,
      Sum.inr (α, γ) ∈ initial.columns)
    (hhead : ∀ α ∈ initial.attachments, ∀ a : Fin q₁,
      xcap ≤ μ.toFiniteLaw.prob (fun u => (a, u) ∈ (fun z => z α) '' K))
    (hcollision : ∀ α ∈ initial.attachments,
      ∃ (i₁ i₂ i₀ : Items s V) (p p' : Fin s), p ≠ p' ∧
        activity order edge hs r hsourceq i₁ α = some p ∧
        activity order edge hs r hsourceq i₂ α = some p' ∧
        activity order edge hs r hsourceq i₀ α = none ∧
        ∀ t : Fin 3, xcap ≤ μ.toFiniteLaw.prob
          (fun u => Sum.inr (collisionItem i₁ i₂ i₀ t, u) ∈ A)) : False := by
  classical
  let F := fun (a : RawRow q₁ q₂ s X (Items s V))
      (c : V38Matrix.TaggedColumn q₁ q₂ s Y) =>
    V38Matrix.matrix order edge hs r hsourceq R ξ₀ c a
  let B := fun (γ : Word q₁ s Y) j => M₁ R j γ
  let row := fun z : Template q₁ q₂ X =>
    (Sum.inl (bin, z) : RawRow q₁ q₂ s X (Items s V))
  let input := fun (α : Fin q₂) (γ : Word q₁ s Y) =>
    (Sum.inr (α, γ) : V38Matrix.TaggedColumn q₁ q₂ s Y)
  have hentry : ∀ z γ α, F (row z) (input α γ) = B γ (z α) := by
    intro z γ α
    rfl
  apply V38Collision.no_short_actual_protocol
    (ν.iid (q₁ + s + 1)).toFiniteLaw input (fun (a : A) c => F a.val c)
    q₂ b ell H hq hq2 hb initial (by omega) hcount hexcess x hx hsmall hcost
    hcorrect hmarked hmass hreaches
  · intro U P hP α S hS hSmass
    exact V38LocalDiagram.before_alice_cost
      (ν.iid (q₁ + s + 1)).toFiniteLaw
      ((PositiveRationalLaw.uniform (Fin q₁)).prod μ).toFiniteLaw
      (SourceLaws.templateLaw μ q₁ q₂).toFiniteLaw F B row input
      (fun z α => z α) hentry
      (SourceLaws.template_coordinate_marginal μ q₁ q₂)
      H x hprofile K A hK (by linarith) U P hP α S hS hSmass
  · intro U query
    exact V38LocalDiagram.after_alice_cost
      (ν.iid (q₁ + s + 1)) ((PositiveRationalLaw.uniform (Fin q₁)).prod μ)
      (SourceLaws.templateLaw μ q₁ q₂).toFiniteLaw F B row input
      (fun z α => z α) hentry (template_eightwise μ)
      H x hH hx hprofile K A hK hKmass U query
  · intro U P hP α hα S _hsub hS hSmass
    obtain ⟨i₁, i₂, i₀, p, p', hpp, h₁, h₂, h₀, hbase⟩ := hcollision α hα
    let Base : Fin 3 → Set X := fun t =>
      {u | Sum.inr (collisionItem i₁ i₂ i₀ t, u) ∈ A}
    exact V38ActualWitness.marked_protocol_cost order edge hs r hsourceq μ ν R ξ₀
      H xcap bin α K Base S i₁ i₂ i₀ p p' hpp h₁ h₂ h₀ U A hK
      (fun _ _ h => h) hS (hhead α hα) hbase hSmass threeTail P hP

end CurrentAdditive.V38FullRemaining

#print axioms CurrentAdditive.V38FullRemaining.template_eightwise
#print axioms CurrentAdditive.V38FullRemaining.no_short_remaining_protocol
