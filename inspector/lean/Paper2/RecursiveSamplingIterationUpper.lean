import Paper2.RecursiveSamplingReachability
import Paper2.SourceIteration

/-!
# Every-tape upper bounds for the actual sampled graph construction

Frozen v12, `prop:iteration`, `thm:uniform-reduction`, and Appendix D.
The capped sampler either returns the actual matrix on generated labels or
the zero table. Its communication bound therefore pulls back the universal
and three-colourable-source bounds of the same complete-product iteration.
The source colouring is used only in the proof, never in the sampler.

These are pointwise finite-tape theorems. They do not assert a NO bound,
encoded printing cost, source reduction, or machine-time guarantee.
-/

namespace Paper2.RecursiveSamplingExecution

open Workspace.Types.CommComplexity SourceConstruction

variable {V E : Type} [Fintype V] [Fintype E] [Nonempty V]
  {s q₁ q₂ w Q : ℕ} [NeZero s] [NeZero q₁] [NeZero q₂] [NeZero w] [NeZero Q]

/-- The public graph-dependent algorithm inherits both communication upper
bounds on every tape, including every rejection-exhaustion tape. The two
orders merely enumerate vertices and source items; neither encodes a
colouring or a choice of a communication protocol. -/
theorem run_selected_iteration_bounds (L : ℕ)
    (vertexOrder : Fin (Fintype.card V) ≃ V)
    (itemOrder : Items s V ≃ Fin (Fintype.card (Items s V)))
    (edge : E → Bool → V) (hs : 4 ≤ s) (r : ℕ)
    (hq : q₂ = SourceItems.sourceQ0 (Fin (4 * s)) E * r)
    (ξ : SourceIteration.FixedTails L s q₁ q₂ w Q V) (a b c d : ℕ)
    (hq₁ : q₁ + 2 = s) (hsa : s = 2 ^ a) (hqb : q₂ = 2 ^ b)
    (hw : w = 2 ^ c) (hQ : Q = 2 ^ d)
    (hsize : 2 * (Fintype.card V + s - 3) ≤ q₂) (k mX mY : ℕ)
    (t : Tape V s q₁ q₂ w Q (LookupSeed.width L) k mX mY) :
    D (run vertexOrder hs (LookupSeed.width L)
        (Nat.two_pow_pos (LookupSeed.exponent L))
        (activity itemOrder edge (by omega) r hq) ξ k mX mY t) ≤
        LookupSeed.exponent L + 1 + k * (a + a + b + c + d) + k ∧
    (∀ colour : V → Fin 3, (∀ e, colour (edge e false) ≠ colour (edge e true)) →
      D (run vertexOrder hs (LookupSeed.width L)
          (Nat.two_pow_pos (LookupSeed.exponent L))
          (activity itemOrder edge (by omega) r hq) ξ k mX mY t) ≤
        LookupSeed.exponent L + 1 + k * (a + a + b + c + d)) := by
  have hrun := run_D_le vertexOrder hs (LookupSeed.width L)
    (Nat.two_pow_pos (LookupSeed.exponent L))
    (activity itemOrder edge (by omega) r hq) ξ k mX mY t
  have hit := SourceIteration.selected_iteration_bounds L itemOrder edge
    (by omega) r hq ξ a b c d hq₁ hsa hqb hw hQ hsize k
  change D (run vertexOrder hs (LookupSeed.width L)
      (Nat.two_pow_pos (LookupSeed.exponent L))
      (activity itemOrder edge (by omega) r hq) ξ k mX mY t) ≤
    D (SourceIteration.matrix L itemOrder edge (by omega) r hq ξ k) at hrun
  exact ⟨hrun.trans hit.1, fun colour proper => hrun.trans (hit.2.1 colour proper)⟩

end Paper2.RecursiveSamplingExecution

#print axioms Paper2.RecursiveSamplingExecution.run_selected_iteration_bounds
