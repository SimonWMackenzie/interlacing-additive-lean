import CurrentAdditive.GeneratedCollisionExact

/-!
The attached coordinate produced by the actual indexed frontier contradicts
the original parent protocol whenever its graph witness supplies the two
active item positions, one inactive item, and their retained base-row masses.
These premises concern source entries and mass, never a desired cost bound.
-/

namespace CurrentAdditive.DeterministicIndexedMatrix.Sources

open Paper2 Paper2.SourceMatrix Paper2.SourceSupportFrontier
open Paper2.SourceProjectionDiagonal
open Workspace.Types.Protocol

variable {X Y I : Type*} [Fintype X] [Fintype Y] [Fintype I]
  [DecidableEq X] [DecidableEq Y]
  {D q₁ q₂ s : ℕ} [NeZero s] [NeZero q₁] [NeZero q₂]
  {μX : PositiveRationalLaw X} {μY : PositiveRationalLaw Y}
  (src : Sources (D := D) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY)

theorem indexed_collision_endpoint_contradiction_exact
    (hD : 8 ≤ D) (R : X → Y → Bool)
    (activity : I → Fin q₂ → Option (Fin s)) (ξ₀ : Tail s Y)
    (d a ell : ℕ) (ρ x : ℝ)
    (hd : 2 ≤ d) (ha : 1 ≤ a) (hρ : 0 < ρ) (hx : 0 < x)
    (hs : s = 2 ^ a) (hq : q₁ + 3 = s + 1)
    (hq₂ : q₂ = 2 ^ ell)
    (hscale : 2 * (s : ℝ) * ρ ≤ 1)
    (hsmall : Paper2.SourceSupportSchedule.floor q₂ x 0 ≤ 1 / 8)
    (hprofileR : RestrictionProfile R μX.toFiniteLaw μY.toFiniteLaw
      ρ (d : ℤ))
    (hprofileA : RestrictionProfile (A src R)
      src.gamma.law.toFiniteLaw
      ((PositiveRationalLaw.uniform (Fin q₁)).prod μX).toFiniteLaw
      x ((d+a : ℕ) : ℤ))
    (bin : Fin s) (K : Set src.inner.Label)
    (V : Set (Row (I := I) src))
    (hK : ∀ z ∈ K, Sum.inl (bin, z) ∈ V)
    (hKmass : (998/1000 : ℝ) < src.inner.law.toFiniteLaw.prob (· ∈ K))
    (initial : State V (Column src) (Fin q₂) src.gamma.Label)
    (hP : ∀ v : V, ∀ z ∈ initial.columns,
      initial.protocol.eval v z = N src R activity ξ₀ z v.val)
    (hcost : initial.protocol.cost ≤ d+a+ell)
    (hZ : initial.attachments ⊆ initial.coordinates)
    (b : ℕ) (hcount : initial.coordinates.card + b = q₂)
    (hexcess : 3 * b < initial.attachments.card)
    (hmass : ∀ α ∈ initial.coordinates,
      Paper2.SourceSupportSchedule.floor q₂ x 0 ≤
      Paper2.SourceSupportStep.mass src.gamma.law.toFiniteLaw (initial.support α))
    (hattachMass : ∀ α ∈ initial.attachments, (3/4 : ℝ) ≤
      Paper2.SourceSupportStep.mass src.gamma.law.toFiniteLaw (initial.support α))
    (hreaches : ∀ α ∈ initial.coordinates, ∀ γ ∈ initial.support α,
      Column.diagonal (α, γ) ∈ initial.columns)
    (hhead : ∀ α ∈ initial.attachments, ∀ r : Fin q₁,
      2 * (s : ℝ) * ρ ≤ μX.toFiniteLaw.prob
        (fun u => (r, u) ∈ (fun z => src.inner.decode z α) '' K))
    (hcollision : ∀ α ∈ initial.attachments,
      ∃ i₁ i₂ i₀ : I, ∃ p p' : Fin s,
        p ≠ p' ∧ activity i₁ α = some p ∧
        activity i₂ α = some p' ∧ activity i₀ α = none ∧
        ∀ t : Fin 3, 2 * (s : ℝ) * ρ ≤ μX.toFiniteLaw.prob
          (fun u => Sum.inr (collisionItem i₁ i₂ i₀ t, u) ∈ V)) :
    False := by
  classical
  obtain ⟨α, hα, W, hWsub, hWmass, U', hU'sub, hW, P, hPc, hPcost⟩ :=
    indexed_remaining_conversation_endpoint src hD R activity ξ₀
      (d+a) ell (by omega) hq₂ x hx hsmall hprofileA
      bin K V hK hKmass initial hP hcost hZ b hcount hexcess
      hmass hattachMass hreaches
  obtain ⟨i₁, i₂, i₀, p, p', hpp, h₁, h₂, h₀, hsource⟩ :=
    hcollision α hα
  let B : Fin 3 → Set X := fun t =>
    {u | Sum.inr (collisionItem i₁ i₂ i₀ t, u) ∈ V}
  have hB : ∀ t u, u ∈ B t →
      Sum.inr (collisionItem i₁ i₂ i₀ t, u) ∈ V := by
    intro t u hu
    exact hu
  have hsource' : ∀ t, 2 * (s : ℝ) * ρ ≤
      μX.toFiniteLaw.prob (· ∈ B t) := hsource
  have hl := indexed_collision_cost_exact src hD R activity ξ₀ d a ρ
    hd ha hρ hs hq hscale hprofileR bin α K B W i₁ i₂ i₀
    p p' hpp h₁ h₂ h₀ U' V hK hB hW (hhead α hα)
    hsource' hWmass
  have hup : Workspace.Types.CommComplexity.D
      (fun (row : V) (z : U') => N src R activity ξ₀ z.val row.val) ≤ P.cost :=
    Nat.sInf_le ⟨P, rfl, hPc⟩
  have he := Paper2.SourceProjection.restrictionD_transpose
    (N src R activity ξ₀) U' V
  have hfinal : d+a+1 ≤ P.cost := hl.trans (he ▸ hup)
  omega

end CurrentAdditive.DeterministicIndexedMatrix.Sources

#print axioms CurrentAdditive.DeterministicIndexedMatrix.Sources.indexed_collision_endpoint_contradiction_exact
