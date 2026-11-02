import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

/-!
# Current replacement paper: weighted counting on an outer frontier

Source: `2026-09-22-complete-replacement-v8/source/sections/`
`A-stage4-details.tex`, `lem:paper-weighted-frontier` and its immediately
following splitting rule; used in the proof of the terminal lower bound.

These are finite arithmetic statements, not protocol-control certificates.
The caller must obtain the counts, splitting identities, isolation bounds,
and capacity bound from the actual protocol. No communication-complexity
conclusion is assumed or asserted here. Natural capacities need not be
positive or dyadic for these counting statements.
-/

namespace EthInapproximability.CurrentPaper.OuterWeightCount

open scoped BigOperators

/-- Each split replaces one attached pair of weight four by two ordinary
markers of total weight six. The equality formulation avoids truncated
natural subtraction. -/
theorem split_weight {h z hL zL hR zR splits : ℕ}
    (hordinary : hL + hR = h + splits)
    (hattached : zL + zR + splits = z) :
    (3 * hL + zL) + (3 * hR + zR) = 3 * h + z + 2 * splits := by
  omega

/-- Summed marker conservation gives the total weight after all splits. -/
theorem total_weight {Node : Type*} (nodes : Finset Node)
    (h z : Node → ℕ) {h₀ z₀ splits : ℕ}
    (hordinary : ∑ v ∈ nodes, h v = h₀ + splits)
    (hattached : (∑ v ∈ nodes, z v) + splits = z₀) :
    ∑ v ∈ nodes, (3 * h v + z v) = 3 * h₀ + z₀ + 2 * splits := by
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  omega

/-- The paper's weighted counting inequality. In fact the selected node
satisfies the strict bound `3 * k v < 4 * h v`. -/
theorem weighted_count {Node : Type*} (nodes : Finset Node)
    (isolated : Node → Prop) (h z k : Node → ℕ)
    (hattached : ∀ v ∈ nodes, z v ≤ h v)
    (hisolated : ∀ v ∈ nodes, isolated v → h v + z v ≤ k v)
    (hweight : 3 * (∑ v ∈ nodes, k v) < ∑ v ∈ nodes, (3 * h v + z v)) :
    ∃ v ∈ nodes, ¬ isolated v ∧ 3 * k v < 4 * h v ∧ k v < h v + z v := by
  have hexcess : ∃ v ∈ nodes, 3 * k v < 3 * h v + z v := by
    by_contra hnone
    push Not at hnone
    have hsum := Finset.sum_le_sum hnone
    rw [← Finset.mul_sum] at hsum
    omega
  obtain ⟨v, hv, hexcess⟩ := hexcess
  have hz := hattached v hv
  refine ⟨v, hv, ?_, ?_, ?_⟩
  · intro hi
    have hsmall := hisolated v hv hi
    omega
  · omega
  · omega

/-- A total capacity bound, such as the prefix-free Kraft bound, is enough
for the weighted counting inequality. -/
theorem weighted_frontier {Node : Type*} (nodes : Finset Node)
    (isolated : Node → Prop) (h z k : Node → ℕ) {capacity : ℕ}
    (hattached : ∀ v ∈ nodes, z v ≤ h v)
    (hisolated : ∀ v ∈ nodes, isolated v → h v + z v ≤ k v)
    (hcapacity : ∑ v ∈ nodes, k v ≤ capacity)
    (hweight : 3 * capacity < ∑ v ∈ nodes, (3 * h v + z v)) :
    ∃ v ∈ nodes, ¬ isolated v ∧ 3 * k v ≤ 4 * h v ∧ k v < h v + z v := by
  obtain ⟨v, hv, hnot, hlarge, hexcess⟩ := weighted_count nodes isolated h z k
    hattached hisolated (by omega)
  exact ⟨v, hv, hnot, Nat.le_of_lt hlarge, hexcess⟩

/-- The terminal application starts with `s` ordinary markers and one
attached marker. Every split increases its initially excessive weight. -/
theorem one_attached_frontier {Node : Type*} (nodes : Finset Node)
    (isolated : Node → Prop) (h z k : Node → ℕ) {s splits : ℕ}
    (hattached : ∀ v ∈ nodes, z v ≤ h v)
    (hisolated : ∀ v ∈ nodes, isolated v → h v + z v ≤ k v)
    (hcapacity : ∑ v ∈ nodes, k v ≤ s)
    (hordinary : ∑ v ∈ nodes, h v = s + splits)
    (hconserve : (∑ v ∈ nodes, z v) + splits = 1) :
    ∃ v ∈ nodes, ¬ isolated v ∧ 3 * k v ≤ 4 * h v ∧ k v < h v + z v := by
  apply weighted_frontier nodes isolated h z k hattached hisolated hcapacity
  rw [total_weight nodes h z hordinary hconserve]
  omega

end EthInapproximability.CurrentPaper.OuterWeightCount
