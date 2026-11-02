import Paper2.PairedSupportFrontier

/-!
# Nonempty paired-support stopping nodes

Frozen v12, Section 5, `res:paired`, the stopping-frontier count argument.
The primary count includes every singleton, of either tag, and one unit for
each unseparated pair. In particular a foreign singleton created by a split
does not disappear from the count. Removing only zero-count leaves preserves
both sums and the same physical binary paths.
-/

namespace Paper2.PairedSupportFrontier

open SourceSupportFrontier
open scoped BigOperators

variable {A C I W : Type*}

/-- Actual leaf positions carrying at least one singleton or unseparated pair. -/
abbrev Active (T : SourceSupportFrontier.Tree (State A C I W)) :=
  {v : T.Leaves // 0 < (T.state v).h}

noncomputable instance activeFintype (T : SourceSupportFrontier.Tree (State A C I W)) : Fintype (Active T) := by
  classical
  exact inferInstanceAs (Fintype {v : T.Leaves // 0 < (T.state v).h})

noncomputable instance activeDecidableEq (T : SourceSupportFrontier.Tree (State A C I W)) :
    DecidableEq (Active T) := Classical.decEq _

/-- The original physical path, restricted to active stopping positions. -/
def activeRoute (T : SourceSupportFrontier.Tree (State A C I W)) (v : Active T) : List Bool :=
  T.route v.val

theorem active_prefixFree (T : SourceSupportFrontier.Tree (State A C I W)) :
    Frontier.PrefixFree (activeRoute T) := by
  intro v w hne hp
  exact T.prefixFree v.val w.val (fun h => hne (Subtype.ext h)) hp

/-- A summand vanishing on zero-count leaves has the same active-frontier sum. -/
theorem sum_active_eq (T : SourceSupportFrontier.Tree (State A C I W)) (f : T.Leaves → ℕ)
    (hzero : ∀ v, ¬ 0 < (T.state v).h → f v = 0) :
    (∑ v : Active T, f v.val) = ∑ v : T.Leaves, f v := by
  classical
  exact (Finset.sum_congr_set {v | 0 < (T.state v).h}
    f (fun v => f v.val) (fun _ _ => rfl) hzero).symm

theorem sum_active_h (T : SourceSupportFrontier.Tree (State A C I W)) :
    (∑ v : Active T, (T.state v.val).h) = ∑ v : T.Leaves, (T.state v).h := by
  apply sum_active_eq T (fun v => (T.state v).h)
  intro v hv
  omega

/-- Every pair contributes one unit to the primary count, so a zero primary
count also has zero pair count. No validity assumption is needed here. -/
theorem sum_active_z (T : SourceSupportFrontier.Tree (State A C I W)) :
    (∑ v : Active T, (T.state v.val).z) = ∑ v : T.Leaves, (T.state v).z := by
  apply sum_active_eq T (fun v => (T.state v).z)
  intro v hv
  simp only [State.h, State.z] at hv ⊢
  omega

end Paper2.PairedSupportFrontier
