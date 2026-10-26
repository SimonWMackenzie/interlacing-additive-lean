import CurrentAdditive.IndependentStreams
import Paper2.SourceProjection
import Paper2.PairedSelectorMatrixCore

/-!
Private source-transfer lemmas for v27 Appendix I, lines 241--475.

These lemmas retain the source indices and the complete-stream law.  A
surviving event can be correlated; only its actual projected image is used.
The protocol lower bounds `det:exact`, `det:separation`, `det:paired`, and
`det:two-stream` are separate obligations, not premises disguised here as
results.
-/

namespace CurrentAdditive.GeneratedSelectorTransfer

open Paper2 Paper2.FiniteLaw
open Workspace.Types.CommComplexity

variable {O I Seed Outer J : Type*}
  [Fintype O] [DecidableEq O] [Fintype I] [DecidableEq I]
  [Fintype Seed] [Fintype Outer] [Fintype J]

/-- A selected set of flattened coordinates has exactly the product law
under the original indexed outer source.  The restriction is selected
before the protocol rectangle; no conditioned independence is asserted. -/
theorem selected_flatten_pushes
    (D : ℕ) (σ : FiniteLaw Seed) (τ : FiniteLaw Outer)
    (μ : FiniteLaw J) (decode : Seed → I → J)
    (outerDecode : Outer → O → Seed)
    (hinner : IsDWise D σ decode μ)
    (houter : IsDWise D τ outerDecode σ)
    (s : Finset (O × I)) (hs : s.card ≤ D) :
    τ.PushesTo (FiniteLaw.pi (fun _ : s => μ))
      (fun t (a : s) => decode (outerDecode t a.val.1) a.val.2) := by
  classical
  exact flatten_dwise D σ τ μ decode outerDecode hinner houter s hs

/-- Every selected projected word comes from an actual surviving outer
index.  Duplicate decoded words remain distinct source outcomes. -/
theorem selected_flatten_image_mass
    (D : ℕ) (σ : FiniteLaw Seed) (τ : FiniteLaw Outer)
    (μ : FiniteLaw J) (decode : Seed → I → J)
    (outerDecode : Outer → O → Seed)
    (hinner : IsDWise D σ decode μ)
    (houter : IsDWise D τ outerDecode σ)
    (s : Finset (O × I)) (hs : s.card ≤ D)
    (K : Set Outer) :
    τ.prob (· ∈ K) ≤
      (FiniteLaw.pi (fun _ : s => μ)).prob
        (· ∈ (fun t (a : s) => decode (outerDecode t a.val.1) a.val.2) '' K) := by
  exact FiniteLaw.prob_le_image _ _ _
    (selected_flatten_pushes D σ τ μ decode outerDecode hinner houter s hs) K

/-- Fixing both complete metadata streams leaves the original selector
source law intact.  A later retained section `K` may be arbitrarily
correlated, but its selected image has at least its conditional mass. -/
theorem fixed_metadata_selected_image_mass
    {Meta₁ Meta₂ : Type*} [Fintype Meta₁] [Fintype Meta₂]
    (D : ℕ) (ρ₁ : FiniteLaw Meta₁) (ρ₂ : FiniteLaw Meta₂)
    (σ : FiniteLaw Seed) (τ : FiniteLaw Outer)
    (μ : FiniteLaw J) (decode : Seed → I → J)
    (outerDecode : Outer → O → Seed)
    (hinner : IsDWise D σ decode μ)
    (houter : IsDWise D τ outerDecode σ)
    (m₁ : Meta₁) (m₂ : Meta₂)
    (hm₁ : 0 < ρ₁.weight m₁) (hm₂ : 0 < ρ₂.weight m₂)
    (s : Finset (O × I)) (hs : s.card ≤ D)
    (K : Set Outer) :
    ((ρ₁.prod ρ₂).prod τ).prob
        (fun x => x.1 = (m₁, m₂) ∧ x.2 ∈ K) /
      ((ρ₁.prod ρ₂).prod τ).prob
        (fun x => x.1 = (m₁, m₂)) ≤
      (FiniteLaw.pi (fun _ : s => μ)).prob
        (· ∈ (fun t (a : s) => decode (outerDecode t a.val.1) a.val.2) '' K) := by
  rw [fixed_two_metadata_streams ρ₁ ρ₂ τ m₁ m₂ hm₁ hm₂ (· ∈ K)]
  exact selected_flatten_image_mass D σ τ μ decode outerDecode
    hinner houter s hs K

end CurrentAdditive.GeneratedSelectorTransfer

namespace CurrentAdditive.GeneratedSelectorTransfer

open Paper2 Paper2.PairedSelectorMatrix
open Workspace.Types.CommComplexity

variable {E W J : Type*} [Fintype E] [Fintype W] [Fintype J]
  {q n : ℕ}

/-- The selected interlace is a genuine restriction of the matrix with
two *indexed* selectors.  One representative of every surviving projected
selector word is used for all rows.  Tags keep the two selectors distinct
even when both decode to the same inner word. -/
theorem selected_indexed_pair_cost_le
    (R : W → J → Bool)
    (decode : E → Selector q J)
    (e : Fin n → Block q)
    (A : Set E) (C : Set (Column q W))
    (S : Set (Fin n × W))
    (hrows : ∀ a ∈ S, (e a.1, a.2) ∈ C) :
    Compression.restrictionD (fullInterlace R n) S
        ((fun t i => coordinate (decode t) (e i)) '' A) ≤
      Compression.restrictionD
        (fun c t => R c.2 (coordinate (decode t) c.1)) C A := by
  exact Paper2.SourceProjection.restrictionD_projected_le
    (fun c t => R c.2 (coordinate (decode t) c.1))
    (fullInterlace R n)
    (fun a : Fin n × W => (e a.1, a.2))
    (fun t i => coordinate (decode t) (e i))
    C A S hrows (by intro a ha t ht; rfl)

end CurrentAdditive.GeneratedSelectorTransfer

#print axioms CurrentAdditive.GeneratedSelectorTransfer.selected_flatten_pushes
#print axioms CurrentAdditive.GeneratedSelectorTransfer.selected_flatten_image_mass
#print axioms CurrentAdditive.GeneratedSelectorTransfer.fixed_metadata_selected_image_mass
#print axioms CurrentAdditive.GeneratedSelectorTransfer.selected_indexed_pair_cost_le
