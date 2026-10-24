import Paper2.SourceProjection

/-!
# A retained support cannot stop too early

Frozen v12 Section 4, `src:near-full`, exclusion of leaves and of the final
Bob-only depth. One actual retained diagonal coordinate already requires
the first-rung cost of `M₁ᵀ`. The actual support recursion and its depth
accounting are separate obligations: this module supplies their concrete
one-coordinate lower-bound consumer, not a certificate of those invariants.
-/

namespace Paper2.SourceSupportStopping

open SourceMatrix SourceProjection Workspace.Types.CommComplexity
open Workspace.Types.Protocol

variable {X Y I : Type*} [Fintype X] [Fintype Y] [Fintype I]
variable {q₁ q₂ s : ℕ} [NeZero q₁] [NeZero s]

/-- The first profile rung applies to the genuine word support and the
coordinate image of whole retained templates. It therefore lower-bounds
the very same retained source matrix, including its tagged inputs. -/
theorem coordinate_lower
    (μ : PositiveRationalLaw X) (ν : PositiveRationalLaw Y)
    (R : X → Y → Bool) (activity : I → Fin q₂ → Option (Fin s)) (ξ₀ : Tail s Y)
    (H : ℕ) (x : ℝ)
    (hprofile : RestrictionProfile (fun (γ : Word q₁ s Y) j => M₁ R j γ)
      (ν.iid (q₁ + s + 1)).toFiniteLaw
      ((PositiveRationalLaw.uniform (Fin q₁)).prod μ).toFiniteLaw x (H : ℤ))
    (p : Fin s) (α : Fin q₂) (A : Set (Template q₁ q₂ X)) (W : Set (Word q₁ s Y))
    (U : Set (TaggedColumn q₁ q₂ s Y)) (V : Set (RawRow q₁ q₂ s X I))
    (hA : ∀ z ∈ A, Sum.inl (p, z) ∈ V)
    (hW : ∀ γ ∈ W, TaggedColumn.diagonal (α, γ) ∈ U)
    (hAmass : (3 / 5 : ℝ) ≤ (SourceLaws.templateLaw μ q₁ q₂).toFiniteLaw.prob (· ∈ A))
    (hWmass : x ≤ (ν.iid (q₁ + s + 1)).toFiniteLaw.prob (· ∈ W)) :
    H ≤ Compression.restrictionD (N R activity ξ₀) U V := by
  have hcol := hAmass.trans (template_coordinate_mass μ α A)
  have hfirst := (restrictionProfile_three_levels _ _ _ _ _).mp hprofile |>.1
  have hl := hfirst W ((fun z : Template q₁ q₂ X => z α) '' A) hWmass hcol
  rw [restrictionD_transpose (M₁ R)] at hl
  have hn : H ≤ Compression.restrictionD (M₁ R)
      ((fun z : Template q₁ q₂ X => z α) '' A) W := by exact_mod_cast hl
  exact hn.trans (diagonal_template_D_le R activity ξ₀ p α A W U V hA hW)

/-- The lower bound is on an arbitrary actual protocol for the retained
rectangle in the original raw-row orientation. Correctness is pointwise.
Combined with subtree depth accounting, this excludes both cost-zero
leaves and any stopping node with fewer than `H` remaining bits. -/
theorem coordinate_protocol_cost
    (μ : PositiveRationalLaw X) (ν : PositiveRationalLaw Y)
    (R : X → Y → Bool) (activity : I → Fin q₂ → Option (Fin s)) (ξ₀ : Tail s Y)
    (H : ℕ) (x : ℝ)
    (hprofile : RestrictionProfile (fun (γ : Word q₁ s Y) j => M₁ R j γ)
      (ν.iid (q₁ + s + 1)).toFiniteLaw
      ((PositiveRationalLaw.uniform (Fin q₁)).prod μ).toFiniteLaw x (H : ℤ))
    (p : Fin s) (α : Fin q₂) (A : Set (Template q₁ q₂ X)) (W : Set (Word q₁ s Y))
    (U : Set (TaggedColumn q₁ q₂ s Y)) (V : Set (RawRow q₁ q₂ s X I))
    (hA : ∀ z ∈ A, Sum.inl (p, z) ∈ V)
    (hW : ∀ γ ∈ W, TaggedColumn.diagonal (α, γ) ∈ U)
    (hAmass : (3 / 5 : ℝ) ≤ (SourceLaws.templateLaw μ q₁ q₂).toFiniteLaw.prob (· ∈ A))
    (hWmass : x ≤ (ν.iid (q₁ + s + 1)).toFiniteLaw.prob (· ∈ W))
    (P : Protocol V U Bool)
    (hP : P.Computes (fun v u => N R activity ξ₀ u.val v.val)) : H ≤ P.cost := by
  classical
  have hl := coordinate_lower μ ν R activity ξ₀ H x hprofile p α A W U V
    hA hW hAmass hWmass
  have hup : D (fun (v : V) (u : U) => N R activity ξ₀ u.val v.val) ≤ P.cost :=
    Nat.sInf_le ⟨P, rfl, hP⟩
  have he := restrictionD_transpose (N R activity ξ₀) U V
  exact hl.trans (he ▸ hup)

end Paper2.SourceSupportStopping

#print axioms Paper2.SourceSupportStopping.coordinate_lower
#print axioms Paper2.SourceSupportStopping.coordinate_protocol_cost
