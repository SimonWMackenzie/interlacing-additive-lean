import Paper2.PairedSupportFrontierActive
import Paper2.PairedSupportFrontierCounts

/-!
# Excess on the generated paired-support frontier

Frozen v12, Section 5, `res:paired`, with the count inequality `src:frontier`.
Prefix-freeness and conservation follow from the actual Bob-only recursion.
The count `h` includes separated singletons of both tags. Only the initial
count and excess conditions are hypotheses; no global frontier certificate
or conclusion of the communication lower-bound argument is assumed.
-/

namespace Paper2.PairedSupportFrontier

open SourceSupportFrontier
open scoped BigOperators

variable {A C I W : Type*} [Fintype W]

/-- The actual nonempty paired-support frontier has an overloaded node. -/
theorem run_active_overload (μ : FiniteLaw W) (input : Bool × I → W → C)
    (fuel : ℕ) (s : State A C I W) (hs : s.Valid) (q b : ℕ)
    (hcount : s.h + b = q) (hexcess : 3 * b < s.z) :
    ∃ v : Active (run μ input fuel s),
      3 * ((q : ℝ) / 2 ^ ((run μ input fuel s).route v.val).length) / 4 ≤
        (((run μ input fuel s).state v.val).h : ℝ) ∧
      (q : ℝ) / 2 ^ ((run μ input fuel s).route v.val).length <
        (((run μ input fuel s).state v.val).h : ℝ) +
          (((run μ input fuel s).state v.val).z : ℝ) := by
  classical
  let T := run μ input fuel s
  have hc := run_counts μ input fuel s hs
  have hHnat : (∑ v : Active T, (T.state v.val).h) = s.h + T.totalSplits := by
    rw [sum_active_h T]
    exact hc.1
  have hZnat : (∑ v : Active T, (T.state v.val).z) + T.totalSplits = s.z := by
    rw [sum_active_z T]
    exact hc.2
  have hHreal : (∑ v : Active T, ((T.state v.val).h : ℝ)) =
      (q : ℝ) - b + T.totalSplits := by
    have hc' : (∑ v : Active T, ((T.state v.val).h : ℝ)) =
        (s.h : ℝ) + T.totalSplits := by exact_mod_cast hHnat
    have hi : (s.h : ℝ) + b = q := by exact_mod_cast hcount
    linarith
  have hZreal : (∑ v : Active T, ((T.state v.val).z : ℝ)) =
      (s.z : ℝ) - T.totalSplits := by
    have hc' : (∑ v : Active T, ((T.state v.val).z : ℝ)) +
        (T.totalSplits : ℝ) = s.z := by exact_mod_cast hZnat
    linarith
  have hzh (v : Active T) : (T.state v.val).z ≤ (T.state v.val).h := by
    simp only [State.h, State.z]
    omega
  exact Frontier.frontier_overload (fun v : Active T => T.route v.val)
    (active_prefixFree T)
    (fun v => ((T.state v.val).h : ℝ))
    (fun v => ((T.state v.val).z : ℝ))
    (q : ℝ) (b : ℝ) (T.totalSplits : ℝ) (s.z : ℝ)
    (Nat.cast_nonneg q) (fun _ => Nat.cast_nonneg _)
    (fun v => by
      change ((T.state v.val).z : ℝ) ≤ ((T.state v.val).h : ℝ)
      exact_mod_cast hzh v)
    hHreal hZreal (Nat.cast_nonneg _) (by exact_mod_cast hexcess)

/-- Depth control is needed only for active leaves. The actual communication
profile argument must establish this premise in the final application. -/
theorem run_active_overload_bounded (μ : FiniteLaw W) (input : Bool × I → W → C)
    (fuel : ℕ) (s : State A C I W) (hs : s.Valid) (q b ell : ℕ)
    (hcount : s.h + b = q) (hexcess : 3 * b < s.z)
    (hdepth : ∀ v : Active (run μ input fuel s),
      ((run μ input fuel s).route v.val).length ≤ ell) :
    ∃ v : Active (run μ input fuel s),
      ((run μ input fuel s).route v.val).length ≤ ell ∧
      3 * ((q : ℝ) / 2 ^ ((run μ input fuel s).route v.val).length) / 4 ≤
        (((run μ input fuel s).state v.val).h : ℝ) ∧
      (q : ℝ) / 2 ^ ((run μ input fuel s).route v.val).length <
        (((run μ input fuel s).state v.val).h : ℝ) +
          (((run μ input fuel s).state v.val).z : ℝ) := by
  obtain ⟨v, hbig, hexc⟩ := run_active_overload μ input fuel s hs q b hcount hexcess
  exact ⟨v, hdepth v, hbig, hexc⟩

end Paper2.PairedSupportFrontier
