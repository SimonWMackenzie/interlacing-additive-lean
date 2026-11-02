import Paper2.SourceSupportFrontierActive

/-!
# Excess on the actual nonempty stopping frontier

Frozen v12, Section 4, `src:near-full` and `src:frontier`.
The frontier below is the nonempty-coordinate subtype of the concrete
Bob-only run. Its conservation identities and prefix-freeness are proved
from the construction, not accepted as premises. The only input counts
refer to the initial coordinate and attachment sets.
-/

namespace Paper2.SourceSupportFrontier

open scoped BigOperators

variable {A C I W : Type*} [Fintype W]

/-- The generated nonempty frontier has an overloaded physical node.
The capacity at depth `r` is exactly `q / 2^r`. -/
theorem run_active_overload (μ : FiniteLaw W) (input : I → W → C)
    (floor : ℕ → ℝ) (fuel : ℕ) (s : State A C I W)
    (hZ : s.attachments ⊆ s.coordinates) (q b : ℕ)
    (hcount : s.coordinates.card + b = q)
    (hexcess : 3 * b < s.attachments.card) :
    ∃ v : Active (run μ input floor 0 fuel s),
      3 * ((q : ℝ) / 2 ^ ((run μ input floor 0 fuel s).route v.val).length) / 4 ≤
        (((run μ input floor 0 fuel s).state v.val).coordinates.card : ℝ) ∧
      (q : ℝ) / 2 ^ ((run μ input floor 0 fuel s).route v.val).length <
        (((run μ input floor 0 fuel s).state v.val).coordinates.card : ℝ) +
          (((run μ input floor 0 fuel s).state v.val).attachments.card : ℝ) := by
  classical
  let T := run μ input floor 0 fuel s
  have hz : ∀ v : T.Leaves, (T.state v).attachments ⊆ (T.state v).coordinates :=
    run_attachments_subset μ input floor 0 fuel s hZ
  have hc := run_counts μ input floor 0 fuel s hZ
  have hQnat : (∑ v : Active T, (T.state v.val).coordinates.card) =
      s.coordinates.card + T.totalSplits := by
    rw [sum_active_coordinates T]
    exact hc.1
  have hZnat : (∑ v : Active T, (T.state v.val).attachments.card) +
      T.totalSplits = s.attachments.card := by
    rw [sum_active_attachments T hz]
    exact hc.2
  have hQreal : (∑ v : Active T, ((T.state v.val).coordinates.card : ℝ)) =
      (q : ℝ) - b + T.totalSplits := by
    have hc' : (∑ v : Active T, ((T.state v.val).coordinates.card : ℝ)) =
        (s.coordinates.card : ℝ) + T.totalSplits := by exact_mod_cast hQnat
    have hi : (s.coordinates.card : ℝ) + b = q := by exact_mod_cast hcount
    linarith
  have hZreal : (∑ v : Active T, ((T.state v.val).attachments.card : ℝ)) =
      (s.attachments.card : ℝ) - T.totalSplits := by
    have hc' : (∑ v : Active T, ((T.state v.val).attachments.card : ℝ)) +
        (T.totalSplits : ℝ) = s.attachments.card := by exact_mod_cast hZnat
    linarith
  exact Frontier.frontier_overload (fun v : Active T => T.route v.val)
    (active_prefixFree T)
    (fun v => ((T.state v.val).coordinates.card : ℝ))
    (fun v => ((T.state v.val).attachments.card : ℝ))
    (q : ℝ) (b : ℝ) (T.totalSplits : ℝ) (s.attachments.card : ℝ)
    (Nat.cast_nonneg q) (fun _ => Nat.cast_nonneg _)
    (fun v => by
      change ((T.state v.val).attachments.card : ℝ) ≤
        ((T.state v.val).coordinates.card : ℝ)
      exact_mod_cast Finset.card_le_card (hz v.val))
    hQreal hZreal (Nat.cast_nonneg _) (by exact_mod_cast hexcess)

/-- Only active leaves need a depth bound. Empty-coordinate leaves are
excluded by the proved active-subtype construction, not assumed absent. -/
theorem run_active_overload_bounded (μ : FiniteLaw W) (input : I → W → C)
    (floor : ℕ → ℝ) (fuel : ℕ) (s : State A C I W)
    (hZ : s.attachments ⊆ s.coordinates) (q b ell : ℕ)
    (hcount : s.coordinates.card + b = q)
    (hexcess : 3 * b < s.attachments.card)
    (hdepth : ∀ v : Active (run μ input floor 0 fuel s),
      ((run μ input floor 0 fuel s).route v.val).length ≤ ell) :
    ∃ v : Active (run μ input floor 0 fuel s),
      ((run μ input floor 0 fuel s).route v.val).length ≤ ell ∧
      3 * ((q : ℝ) / 2 ^ ((run μ input floor 0 fuel s).route v.val).length) / 4 ≤
        (((run μ input floor 0 fuel s).state v.val).coordinates.card : ℝ) ∧
      (q : ℝ) / 2 ^ ((run μ input floor 0 fuel s).route v.val).length <
        (((run μ input floor 0 fuel s).state v.val).coordinates.card : ℝ) +
          (((run μ input floor 0 fuel s).state v.val).attachments.card : ℝ) := by
  obtain ⟨v, hbig, hexc⟩ := run_active_overload μ input floor fuel s hZ q b hcount hexcess
  exact ⟨v, hdepth v, hbig, hexc⟩

end Paper2.SourceSupportFrontier
