import Paper2.IterationUpperBounds
import Paper2.SourceConstruction
import Paper2.LookupSeed

/-!
# The public graph construction iterated from the specified lookup seed

Frozen v12, `prop:iteration`. This connects the generic recursive evaluator
and upper/rank induction to the very same ordered graph activity and selected
cube seed used by the paper. Public width/size guards are explicit. A coloring
appears only in the proof of the YES budget, not in the matrix constructor.
NO lower bounds, regenerated laws/profiles and runtime are not asserted here.
-/

namespace Paper2.SourceIteration

open RecursiveEntries SourceConstruction RankLeaves Workspace.Types.CommComplexity

variable {V E : Type} [Fintype V] [Fintype E]
  {s q₁ q₂ w Q : ℕ} [NeZero s] [NeZero q₂]

abbrev SeedRows (L : ℕ) := Fin (LookupSeed.width L) → Bool
abbrev SeedColumns (L : ℕ) := Fin (LookupSeed.width L)
abbrev FixedTails (L s q₁ q₂ w Q : ℕ) (V : Type) :=
  Tails (SeedRows L) (SeedColumns L) (Items s V) s q₁ q₂ w Q

/-- Public complete-product construction with the prescribed initial cube. -/
noncomputable def matrix (L : ℕ)
    (order : Items s V ≃ Fin (Fintype.card (Items s V)))
    (edge : E → Bool → V) (hs : 3 ≤ s) (r : ℕ)
    (hq : q₂ = SourceItems.sourceQ0 (Fin (4 * s)) E * r)
    (ξ : FixedTails L s q₁ q₂ w Q V) (k : ℕ) :=
  RecursiveEntries.matrix (LookupSeed.matrix (LookupSeed.width L))
    (activity order edge hs r hq) ξ k

/-- Universal depth, every-colorable-source YES depth, and rank, all for
the same actual graph-dependent matrix. -/
theorem selected_iteration_bounds (L : ℕ)
    (order : Items s V ≃ Fin (Fintype.card (Items s V)))
    (edge : E → Bool → V) (hs : 3 ≤ s) (r : ℕ)
    (hq : q₂ = SourceItems.sourceQ0 (Fin (4 * s)) E * r)
    (ξ : FixedTails L s q₁ q₂ w Q V) (a b c d : ℕ)
    (hq₁ : q₁ + 2 = s) (hsa : s = 2 ^ a) (hqb : q₂ = 2 ^ b)
    (hw : w = 2 ^ c) (hQ : Q = 2 ^ d)
    (hsize : 2 * (Fintype.card V + s - 3) ≤ q₂) (k : ℕ) :
    D (matrix L order edge hs r hq ξ k) ≤
        LookupSeed.exponent L + 1 + k * (a + a + b + c + d) + k ∧
    (∀ colour : V → Fin 3, (∀ e, colour (edge e false) ≠ colour (edge e true)) →
      D (matrix L order edge hs r hq ξ k) ≤
        LookupSeed.exponent L + 1 + k * (a + a + b + c + d)) ∧
    (realMatrix (matrix L order edge hs r hq ξ k)).rank ≤
      2 ^ (LookupSeed.exponent L + 1 + k * (a + a + b + c + d) - 1) := by
  have hseed := LookupSeed.selected_seed_finite L
  have hu := iteration_upper (LookupSeed.matrix (LookupSeed.width L))
    (activity order edge hs r hq) ξ a b c d hq₁ hsa hqb hw hQ k
  rw [hseed.1] at hu
  refine ⟨?_, ?_, ?_⟩
  · simpa only [matrix, Nat.mul_add, Nat.mul_one, Nat.add_assoc] using hu
  · intro colour proper
    have hy := iteration_yes_upper (LookupSeed.matrix (LookupSeed.width L))
      (activity order edge hs r hq) ξ a b c d hq₁ hsa hqb hw hQ
      (SourceItems.yesAssignment hs colour)
      (activity_collisionFree order edge hs r hq colour proper) k
    simpa only [matrix, hseed.1] using hy
  · have hr := iteration_rank (LookupSeed.matrix (LookupSeed.width L))
      (activity order edge hs r hq) ξ a b c d (actual_item_rank_guard hs hsize)
      hq₁ hsa hqb hw hQ k
    rw [hseed.2.2] at hr
    change (realMatrix (matrix L order edge hs r hq ξ k)).rank ≤ _ at hr
    apply hr.trans_eq
    unfold LookupSeed.width
    rw [← pow_add]
    congr 1
    omega

end Paper2.SourceIteration
