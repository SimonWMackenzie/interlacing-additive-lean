import CurrentAdditive.V38AfterAlice
import CurrentAdditive.V38IndexedMarked

/-! All three source-specific local bounds for the actual indexed two-tag
matrix, joined to the literal sharp collision recursion. Original source
indices and original-law word supports are retained throughout. -/

namespace CurrentAdditive.V38IndexedTwoTag

open Paper2 Paper2.SourceMatrix Paper2.SourceProjectionDiagonal
open Paper2.SourceSupportFrontier
open CurrentAdditive.DeterministicIndexedMatrix
open CurrentAdditive.DeterministicIndexedMatrix.Sources
open Workspace.Types.Protocol

variable {X Y I : Type*} [Fintype X] [Fintype Y] [Fintype I]
  [DecidableEq X] [DecidableEq Y]
  {D q₁ q₂ s : ℕ} [NeZero s] [NeZero q₁] [NeZero q₂]
  {μX : PositiveRationalLaw X} {μY : PositiveRationalLaw Y}
  (src : Sources (D := D) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY)

theorem no_short_remaining_protocol
    (hD : 8 ≤ D) (R : X → Y → Bool)
    (activity : I → Fin q₂ → Option (Fin s)) (ξ₀ : Tail s Y)
    (d a ell b : ℕ) (ρ x : ℝ) (hd : 2 ≤ d) (hρ : 0 < ρ) (hx : 0 < x)
    (hs : s = 2^a) (hq : q₁+3=s+1) (hq₂ : q₂=2^ell) (hq2 : 2 ≤ q₂)
    (hb : b < q₂) (hscale : 2*(s : ℝ)*ρ ≤ 1)
    (hsmall : 2*(q₂ : ℝ)*x ≤ 1/8)
    (hprofileR : V38RestrictionProfiles.TwoThresholdProfile R
      μX.toFiniteLaw μY.toFiniteLaw ρ (d : ℤ))
    (hprofileA : V38RestrictionProfiles.TwoThresholdProfile (Sources.A src R)
      src.gamma.law.toFiniteLaw
      ((PositiveRationalLaw.uniform (Fin q₁)).prod μX).toFiniteLaw x ((d+a : ℕ) : ℤ))
    (bin : Fin s) (K : Set src.inner.Label) (V : Set (Row (I := I) src))
    (hK : ∀ z ∈ K, Sum.inl (bin,z) ∈ V)
    (hKmass : (998/1000 : ℝ) < src.inner.law.toFiniteLaw.prob (· ∈ K))
    (initial : State V (Column src) (Fin q₂) src.gamma.Label)
    (hcost : initial.protocol.cost ≤ d+a+ell)
    (hcorrect : ∀ v c, c ∈ initial.columns →
      initial.protocol.eval v c = matrix src R activity ξ₀ c v.val)
    (hcount : initial.coordinates.card + b = q₂)
    (hexcess : b < initial.attachments.card)
    (hmarked : initial.attachments ⊆ initial.coordinates)
    (hmass : ∀ α ∈ initial.coordinates, (3/4 : ℝ) ≤
      SourceSupportStep.mass src.gamma.law.toFiniteLaw (initial.support α))
    (hreaches : ∀ α ∈ initial.coordinates, ∀ γ ∈ initial.support α,
      Sum.inr (α,γ) ∈ initial.columns)
    (hhead : ∀ α ∈ initial.attachments, ∀ i : Fin q₁,
      2*(s : ℝ)*ρ ≤ μX.toFiniteLaw.prob
        (fun u => (i,u) ∈ (fun z => src.inner.decode z α) '' K))
    (hcollision : ∀ α ∈ initial.attachments,
      ∃ (i₁ i₂ i₀ : I) (p p' : Fin s), p ≠ p' ∧
        activity i₁ α = some p ∧ activity i₂ α = some p' ∧
        activity i₀ α = none ∧
        ∀ t : Fin 3, 2*(s : ℝ)*ρ ≤ μX.toFiniteLaw.prob
          (fun u => Sum.inr (collisionItem i₁ i₂ i₀ t,u) ∈ V)) : False := by
  classical
  let F := fun (v : Row (I := I) src) (c : Column src) => matrix src R activity ξ₀ c v
  let B := Sources.A src R
  let row := fun z : src.inner.Label => (Sum.inl (bin,z) : Row (I := I) src)
  let input := fun (α : Fin q₂) (γ : src.gamma.Label) => (Sum.inr (α,γ) : Column src)
  have hentry : ∀ z γ α, F (row z) (input α γ) = B γ (src.inner.decode z α) := by
    intro z γ α
    rfl
  have hwise : IsDWise 8 src.inner.law.toFiniteLaw src.inner.decode
      ((PositiveRationalLaw.uniform (Fin q₁)).prod μX).toFiniteLaw := by
    intro Q hQ E
    exact src.inner.exactLaw Q (hQ.trans hD) E
  apply V38Collision.no_short_actual_protocol src.gamma.law.toFiniteLaw input
    (fun (v : V) c => F v.val c) q₂ b ell (d+a) hq₂ hq2 hb initial
    (by omega) hcount hexcess x hx hsmall hcost hcorrect hmarked hmass hreaches
  · intro U P hP α S hS hSmass
    exact V38LocalDiagram.before_alice_cost src.gamma.law.toFiniteLaw
      ((PositiveRationalLaw.uniform (Fin q₁)).prod μX).toFiniteLaw
      src.inner.law.toFiniteLaw F B row input src.inner.decode hentry
      (codeSource_coordinate_pushes _ src.inner (by omega))
      (d+a) x hprofileA K V hK (by linarith) U P hP α S hS hSmass
  · intro U query
    exact V38LocalDiagram.after_alice_cost src.gamma.law
      ((PositiveRationalLaw.uniform (Fin q₁)).prod μX) src.inner.law.toFiniteLaw
      F B row input src.inner.decode hentry hwise (d+a) x (by omega) hx
      hprofileA K V hK hKmass U query
  · intro U P hP α hα S _hsub hS hSmass
    obtain ⟨i₁,i₂,i₀,p,p',hpp,h₁,h₂,h₀,hbase⟩ := hcollision α hα
    let Base : Fin 3 → Set X := fun t =>
      {u | Sum.inr (collisionItem i₁ i₂ i₀ t,u) ∈ V}
    exact marked_protocol_cost src hD R activity ξ₀ d a ρ hd hρ hs hq hscale
      hprofileR bin α K Base S i₁ i₂ i₀ p p' hpp h₁ h₂ h₀ U V hK
      (fun _ _ h => h) hS (hhead α hα) hbase hSmass P hP

end CurrentAdditive.V38IndexedTwoTag

#print axioms CurrentAdditive.V38IndexedTwoTag.no_short_remaining_protocol
