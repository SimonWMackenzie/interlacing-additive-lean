import Paper2.SourceExtraPosition

/-!
# The attached witness at a capacity-one stopping node

Frozen Paper 2 v12 Section 4, `src:near-full`, the final capacity-one case.
The actual retained template and item rows, and the retained diagonal words,
give the extra-bit lower bound on the parent protocol. In particular this
argument does not restrict the item rows to Alice's denser template child.
The support recursion must still supply the displayed row inclusions, activity
identities, and mass bounds; no communication lower bound is assumed here.
-/

namespace Paper2.SourceSupportCapacityWitness

open SourceMatrix SourceProjection
open Workspace.Types.CommComplexity Workspace.Types.Protocol

variable {X Y I : Type*} [Fintype X] [Fintype Y] [Fintype I]
variable {q₁ q₂ s : ℕ} [NeZero s]

/-- A surviving attached witness needs an extra bit in the actual parent
protocol. All three item-row families remain on this parent rectangle. -/
theorem witness_protocol_cost
    (μ : PositiveRationalLaw X) (ν : PositiveRationalLaw Y)
    (R : X → Y → Bool) (activity : I → Fin q₂ → Option (Fin s)) (ξ₀ : Tail s Y)
    (d a : ℕ) (ρ : ℝ) (hd : 2 ≤ d) (ha : 1 ≤ a) (hρ : 0 < ρ)
    (hs : s = 2 ^ a) (hq : q₁ + 3 = s + 1)
    (hscale : 2 * (s : ℝ) * ρ ≤ 1)
    (hprofile : RestrictionProfile R μ.toFiniteLaw ν.toFiniteLaw ρ (d : ℤ))
    (bin : Fin s) (α : Fin q₂) (A : Set (Template q₁ q₂ X)) (B : Fin 3 → Set X)
    (W : Set (Word q₁ s Y)) (i₁ i₂ i₀ : I) (p p' : Fin s) (hpp : p ≠ p')
    (h₁ : activity i₁ α = some p) (h₂ : activity i₂ α = some p')
    (h₀ : activity i₀ α = none)
    (U : Set (TaggedColumn q₁ q₂ s Y)) (V : Set (RawRow q₁ q₂ s X I))
    (hA : ∀ z ∈ A, Sum.inl (bin, z) ∈ V)
    (hB : ∀ k u, u ∈ B k →
      Sum.inr (SourceProjectionDiagonal.collisionItem i₁ i₂ i₀ k, u) ∈ V)
    (hwords : ∀ γ ∈ W, TaggedColumn.diagonal (α, γ) ∈ U)
    (hhead : ∀ r, 2 * (s : ℝ) * ρ ≤ μ.toFiniteLaw.prob
      (fun u => (r, u) ∈ (fun z : Template q₁ q₂ X => z α) '' A))
    (hsource : ∀ k, 2 * (s : ℝ) * ρ ≤ μ.toFiniteLaw.prob (· ∈ B k))
    (hW : (1 / 2 : ℝ) < (ν.iid (q₁ + s + 1)).toFiniteLaw.prob (· ∈ W))
    (P : Protocol V U Bool)
    (hP : P.Computes (fun v u => N R activity ξ₀ u.val v.val)) :
    d + a + 1 ≤ P.cost := by
  classical
  have hl := SourceExtraPosition.witness_source_lower μ ν R activity ξ₀ d a ρ
    hd ha hρ hs hq hscale hprofile bin α A B W i₁ i₂ i₀ p p' hpp
    h₁ h₂ h₀ U V hA hB hwords hhead hsource hW
  have hup : D (fun (v : V) (u : U) => N R activity ξ₀ u.val v.val) ≤ P.cost :=
    Nat.sInf_le ⟨P, rfl, hP⟩
  have he := restrictionD_transpose (N R activity ξ₀) U V
  exact hl.trans (he ▸ hup)

/-- The capacity-one parent cannot retain an attached witness and have only
`d+a` remaining bits. No premise identifies the attachment with a lower-bound
certificate: the theorem uses its actual rows, words and source entries. -/
theorem witness_protocol_contradiction
    (μ : PositiveRationalLaw X) (ν : PositiveRationalLaw Y)
    (R : X → Y → Bool) (activity : I → Fin q₂ → Option (Fin s)) (ξ₀ : Tail s Y)
    (d a : ℕ) (ρ : ℝ) (hd : 2 ≤ d) (ha : 1 ≤ a) (hρ : 0 < ρ)
    (hs : s = 2 ^ a) (hq : q₁ + 3 = s + 1)
    (hscale : 2 * (s : ℝ) * ρ ≤ 1)
    (hprofile : RestrictionProfile R μ.toFiniteLaw ν.toFiniteLaw ρ (d : ℤ))
    (bin : Fin s) (α : Fin q₂) (A : Set (Template q₁ q₂ X)) (B : Fin 3 → Set X)
    (W : Set (Word q₁ s Y)) (i₁ i₂ i₀ : I) (p p' : Fin s) (hpp : p ≠ p')
    (h₁ : activity i₁ α = some p) (h₂ : activity i₂ α = some p')
    (h₀ : activity i₀ α = none)
    (U : Set (TaggedColumn q₁ q₂ s Y)) (V : Set (RawRow q₁ q₂ s X I))
    (hA : ∀ z ∈ A, Sum.inl (bin, z) ∈ V)
    (hB : ∀ k u, u ∈ B k →
      Sum.inr (SourceProjectionDiagonal.collisionItem i₁ i₂ i₀ k, u) ∈ V)
    (hwords : ∀ γ ∈ W, TaggedColumn.diagonal (α, γ) ∈ U)
    (hhead : ∀ r, 2 * (s : ℝ) * ρ ≤ μ.toFiniteLaw.prob
      (fun u => (r, u) ∈ (fun z : Template q₁ q₂ X => z α) '' A))
    (hsource : ∀ k, 2 * (s : ℝ) * ρ ≤ μ.toFiniteLaw.prob (· ∈ B k))
    (hW : (1 / 2 : ℝ) < (ν.iid (q₁ + s + 1)).toFiniteLaw.prob (· ∈ W))
    (P : Protocol V U Bool)
    (hP : P.Computes (fun v u => N R activity ξ₀ u.val v.val))
    (hcost : P.cost ≤ d + a) : False := by
  have hl := witness_protocol_cost μ ν R activity ξ₀ d a ρ
    hd ha hρ hs hq hscale hprofile bin α A B W i₁ i₂ i₀ p p' hpp
    h₁ h₂ h₀ U V hA hB hwords hhead hsource hW P hP
  omega

end Paper2.SourceSupportCapacityWitness

#print axioms Paper2.SourceSupportCapacityWitness.witness_protocol_cost
#print axioms Paper2.SourceSupportCapacityWitness.witness_protocol_contradiction
