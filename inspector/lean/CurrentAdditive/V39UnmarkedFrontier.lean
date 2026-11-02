import Paper2.SourceSupportFrontierActive

/-! The current paired proof runs the actual Bob-only support recursion
with no marked attachments. Every tagged support chooses a heavier child,
so the coordinate count is conserved and Kraft gives a strict overload. -/

namespace CurrentAdditive.V39UnmarkedFrontier

open Paper2 Paper2.SourceSupportFrontier
open scoped BigOperators

variable {A C I W : Type*} [Fintype W]

theorem run_count_conserved (μ : FiniteLaw W) (input : I → W → C)
    (floor : ℕ → ℝ) (d fuel : ℕ) (s : State A C I W)
    (hmarks : s.attachments = ∅) :
    (∑ v : (run μ input floor d fuel s).Leaves,
      ((run μ input floor d fuel s).state v).coordinates.card) = s.coordinates.card := by
  classical
  have hsub : s.attachments ⊆ s.coordinates := by rw [hmarks]; exact Finset.empty_subset _
  obtain ⟨hcount,hattach⟩ := run_counts μ input floor d fuel s hsub
  rw [hmarks,Finset.card_empty] at hattach
  omega

/-- This is a stopping node of the given protocol, with its actual binary
path. There is no supplied capacity or overload certificate. -/
theorem run_overload (μ : FiniteLaw W) (input : I → W → C)
    (floor : ℕ → ℝ) (d fuel : ℕ) (s : State A C I W)
    (hmarks : s.attachments = ∅) (q : ℕ) (hcount : q < s.coordinates.card) :
    let T := run μ input floor d fuel s
    ∃ v : Active T,
      (q : ℝ)/(2 : ℝ)^(T.route v.val).length <
        ((T.state v.val).coordinates.card : ℝ) := by
  classical
  let T := run μ input floor d fuel s
  have hc : (∑ v : Active T, (T.state v.val).coordinates.card) = s.coordinates.card := by
    rw [sum_active_coordinates]
    exact run_count_conserved μ input floor d fuel s hmarks
  have hk := Frontier.sum_capacity_le (activeRoute T) (active_prefixFree T)
    (q : ℝ) (Nat.cast_nonneg q)
  change ∃ v : Active T, _
  by_contra! hn
  have hsum := Finset.sum_le_sum (fun v (_ : v ∈ (Finset.univ : Finset (Active T))) => hn v)
  have hcast : (∑ v : Active T, ((T.state v.val).coordinates.card : ℝ)) =
      (s.coordinates.card : ℝ) := by exact_mod_cast hc
  change (∑ v : Active T, ((T.state v.val).coordinates.card : ℝ)) ≤
    ∑ v : Active T, (q : ℝ)/(2 : ℝ)^(T.route v.val).length at hsum
  have hstrict : (q : ℝ) < s.coordinates.card := by exact_mod_cast hcount
  change (∑ v : Active T, (q : ℝ)/(2 : ℝ)^(T.route v.val).length) ≤ q at hk
  linarith

end CurrentAdditive.V39UnmarkedFrontier

#print axioms CurrentAdditive.V39UnmarkedFrontier.run_count_conserved
#print axioms CurrentAdditive.V39UnmarkedFrontier.run_overload
