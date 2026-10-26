import CurrentAdditive.V38StrongSeed

namespace Paper2.V38StrongSeed

open Workspace.Types.CommComplexity

variable {X Y : Type*} [Fintype X] [Fintype Y]

/-- Selecting any `copies a` distinct surviving blocks preserves original
product mass and realizes the same projected matrix by surviving tuples. -/
theorem rational_selected
    (μ : PositiveRationalLaw X) (ν : PositiveRationalLaw Y)
    (F : X → Y → Bool) (H a p : ℕ) (hH : 3 ≤ H) (ha : 4 ≤ a)
    (θ : ℝ) (hθ : 0 < θ) (hscale : (2 : ℝ) ^ a * θ ≤ 1)
    (hprofile : V38RestrictionProfiles.TwoThresholdProfile F
      μ.toFiniteLaw ν.toFiniteLaw θ (H : ℤ))
    (U : Set (Fin p × X)) (V : Set (Fin p → Y))
    (e : Fin (copies a) → Fin p) (he : Function.Injective e)
    (hU : ∀ i, (2 : ℝ) ^ a * θ ≤
      μ.toFiniteLaw.prob (fun x => (e i, x) ∈ U))
    (hV : (2 : ℝ) ^ (-((2 : ℝ) ^ a / 1024)) ≤
      (ν.toFiniteLaw.iid p).prob (· ∈ V)) :
    H + a ≤ Compression.restrictionD (fullInterlace F p) U V := by
  have hm := hV.trans (SourceProjection.iid_projection_mass ν.toFiniteLaw e he V)
  have hs := rational_restriction μ ν F H a hH ha θ hθ hscale hprofile
    {s : Fin (copies a) × X | (e s.1, s.2) ∈ U}
    ((fun z : Fin p → Y => fun i : Fin (copies a) => z (e i)) '' V)
    hU hm
  exact hs.trans (V38SmallBlocks.projected_blocks_cost_le F p (copies a) U V e)

/-- Full current-source `lem:many-product-blocks`: arbitrary ambient width,
at least `9*2^a/16` good blocks, and an arbitrary retained tuple set.
All masses use the original laws, including after the block selection. -/
theorem rational_many_blocks
    (μ : PositiveRationalLaw X) (ν : PositiveRationalLaw Y)
    (F : X → Y → Bool) (H a p : ℕ) (hH : 3 ≤ H) (ha : 4 ≤ a)
    (θ : ℝ) (hθ : 0 < θ) (hscale : (2 : ℝ) ^ a * θ ≤ 1)
    (hprofile : V38RestrictionProfiles.TwoThresholdProfile F
      μ.toFiniteLaw ν.toFiniteLaw θ (H : ℤ))
    (U : Set (Fin p × X)) (V : Set (Fin p → Y))
    (Good : Finset (Fin p)) (hGood : copies a ≤ Good.card)
    (hU : ∀ i ∈ Good, (2 : ℝ) ^ a * θ ≤
      μ.toFiniteLaw.prob (fun x => (i, x) ∈ U))
    (hV : (2 : ℝ) ^ (-((2 : ℝ) ^ a / 1024)) ≤
      (ν.toFiniteLaw.iid p).prob (· ∈ V)) :
    H + a ≤ Compression.restrictionD (fullInterlace F p) U V := by
  classical
  obtain ⟨J, hJsub, hJcard⟩ := Finset.exists_subset_card_eq hGood
  let e : Fin (copies a) → Fin p := J.orderEmbOfFin hJcard
  apply rational_selected μ ν F H a p hH ha θ hθ hscale hprofile U V e
    (J.orderEmbOfFin hJcard).injective
  · intro i
    exact hU (e i) (hJsub (J.orderEmbOfFin_mem hJcard i))
  · exact hV

#print axioms rational_selected
#print axioms rational_many_blocks

end Paper2.V38StrongSeed
