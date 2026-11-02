import Paper2.SourceSupportFrontier

/-!
# The nonempty-support part of the actual stopping frontier

Frozen v12, Section 4, `src:near-full`, the stopping-frontier count argument.
The generated tree retains branches carrying no coordinates. This module
removes precisely those zero-contribution leaves. It proves that the actual
binary paths remain prefix-free and both count sums are unchanged.
-/

namespace Paper2.SourceSupportFrontier

open scoped BigOperators

variable {A C I W : Type*}

/-- Actual leaf positions with at least one surviving coordinate support. -/
abbrev Active (T : Tree (State A C I W)) :=
  {v : T.Leaves // (T.state v).coordinates.Nonempty}

noncomputable instance activeFintype (T : Tree (State A C I W)) : Fintype (Active T) := by
  classical
  exact inferInstanceAs (Fintype {v : T.Leaves // (T.state v).coordinates.Nonempty})

noncomputable instance activeDecidableEq (T : Tree (State A C I W)) :
    DecidableEq (Active T) := Classical.decEq _

/-- Restrict the same physical binary path; no new paths are chosen. -/
def activeRoute (T : Tree (State A C I W)) (v : Active T) : List Bool :=
  T.route v.val

theorem active_prefixFree (T : Tree (State A C I W)) :
    Frontier.PrefixFree (activeRoute T) := by
  intro v w hne hp
  exact T.prefixFree v.val w.val (fun h => hne (Subtype.ext h)) hp

/-- Removing inactive leaves preserves every summand that vanishes there. -/
theorem sum_active_eq (T : Tree (State A C I W)) (f : T.Leaves → ℕ)
    (hzero : ∀ v, ¬ (T.state v).coordinates.Nonempty → f v = 0) :
    (∑ v : Active T, f v.val) = ∑ v : T.Leaves, f v := by
  classical
  exact (Finset.sum_congr_set {v | (T.state v).coordinates.Nonempty}
    f (fun v => f v.val) (fun _ _ => rfl) hzero).symm

/-- Inactive leaves have coordinate count zero. -/
theorem sum_active_coordinates (T : Tree (State A C I W)) :
    (∑ v : Active T, (T.state v.val).coordinates.card) =
      ∑ v : T.Leaves, (T.state v).coordinates.card := by
  apply sum_active_eq T (fun v => (T.state v).coordinates.card)
  intro v hv
  rw [Finset.not_nonempty_iff_eq_empty.mp hv]
  rfl

/-- An inactive leaf cannot retain an attachment when attachments are
contained in its counted coordinate set. -/
theorem sum_active_attachments (T : Tree (State A C I W))
    (hZ : ∀ v, (T.state v).attachments ⊆ (T.state v).coordinates) :
    (∑ v : Active T, (T.state v.val).attachments.card) =
      ∑ v : T.Leaves, (T.state v).attachments.card := by
  apply sum_active_eq T (fun v => (T.state v).attachments.card)
  intro v hv
  have he : (T.state v).attachments = ∅ := by
    apply Finset.not_nonempty_iff_eq_empty.mp
    rintro ⟨i, hi⟩
    exact hv ⟨i, hZ v hi⟩
  rw [he]
  rfl

end Paper2.SourceSupportFrontier
