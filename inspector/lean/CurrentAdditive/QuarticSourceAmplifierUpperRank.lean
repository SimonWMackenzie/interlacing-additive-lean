import CurrentAdditive.QuarticSourceAmplifierLower
import Paper2.SourceConstruction

/-! Upper budgets and rank on the same arbitrary base matrix and complete
successor used by the current one-step NO/profile theorem. -/

namespace Paper2.SourceAmplifierUpperRank

open Paper2.SourceMatrix Paper2.SourceConstruction
  Paper2.SourceProfileParameters Workspace.Types.CommComplexity RankLeaves

set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

local instance (L : ℕ) : NeZero (width L) := ⟨by unfold width; positivity⟩
local instance (L : ℕ) : NeZero (outerWidth L) := ⟨by unfold outerWidth; positivity⟩

variable {V E X Y : Type*} [Fintype V] [Fintype E]
  [Fintype X] [Fintype Y]

private theorem width_minus_two (L : ℕ) : width L - 2 + 2 = width L := by
  have hs := SourceProfiles.width_ge_four L
  omega

theorem source_successor_upper_rank27
    (F : X → Y → Bool) (L : ℕ)
    (order : Items (width L) V ≃ Fin (Fintype.card (Items (width L) V)))
    (edge : E → Bool → V) (rep : ℕ) (hrep : 1 ≤ rep)
    (hq : outerWidth L = SourceItems.sourceQ0 (Fin (4 * width L)) E * rep)
    (hE : 0 < Fintype.card E) (hincident : ∀ v, ∃ e b, edge e b = v)
    (ξ₀ : Tail (width L) Y)
    (w r Q q : ℕ) (hw : w = 2 ^ r) (hQ : Q = 2 ^ q) :
    let h := exponent L + outerExponent L + exponent L + r + q
    let S := SourceMatrix.successor (q₁ := width L - 2) F
      (activity order edge (by have := SourceProfiles.width_ge_four L; omega) rep hq)
      ξ₀ w Q
    D S ≤ D F + h + 1 ∧
    (∀ colour : V → Fin 3,
      (∀ e, colour (edge e false) ≠ colour (edge e true)) →
      D S ≤ D F + h) ∧
    (realMatrix S).rank ≤ 2 ^ h * (realMatrix F).rank := by
  letI : NeZero (width L) := ⟨by unfold width; positivity⟩
  letI : NeZero (outerWidth L) := ⟨by unfold outerWidth; positivity⟩
  let hs : 3 ≤ width L := by
    have := SourceProfiles.width_ge_four L
    omega
  let A := activity order edge hs rep hq
  have hupper := SourceMatrix.successor_upper_budgets A F ξ₀ w Q
    (exponent L) (outerExponent L) r q (width_minus_two L)
    (by rfl) (by rfl) hw hQ
  have hrank := actual_successor_rank_bound order edge hs rep hrep hq
    hE hincident F ξ₀ w Q (exponent L) (outerExponent L) r q
    (width_minus_two L) (by rfl) (by rfl) hw hQ
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hupper.1
  · intro colour proper
    have hy := hupper.2 (SourceItems.yesAssignment hs colour)
      (activity_collisionFree order edge hs rep hq colour proper)
    simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hy
  · simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hrank

#print axioms source_successor_upper_rank27

end Paper2.SourceAmplifierUpperRank
