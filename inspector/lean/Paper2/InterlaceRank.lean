import Paper2.IndexedMatrices
import Workspace.Types.Interlace

/-!
# Real rank under full and indexed interlacing

Source: Paper 2, frozen `2026-09-22-protocol-labels-v12`, Section 2,
Definition `def:interlace` and equation `eq:interlace-rank`.

The proof maps a tuple of original row-space vectors to the sum of their
coordinate pullbacks. Every interlaced row is in this map's range, whose
dimension is at most the sum of the original row-space dimensions. It does
not assume a rank-growth contract or a communication lower bound.
-/

namespace Paper2

open scoped BigOperators
open RankLeaves

variable {X Y Z : Type*}

/-- The full interlace, using the inherited concrete entry rule. -/
def fullInterlace (F : X → Y → Bool) (q : ℕ) :
    (Fin q × X) → (Fin q → Y) → Bool :=
  Workspace.Types.Interlace.interlaceFun F q

@[simp] theorem fullInterlace_apply (F : X → Y → Bool) (q : ℕ)
    (a : Fin q × X) (ys : Fin q → Y) :
    fullInterlace F q a ys = F a.2 (ys a.1) := rfl

/-- Restrict full-product columns along an indexed tuple family. Different
labels in `Z` remain distinct even if they name equal tuples. -/
def indexedInterlace (F : X → Y → Bool) {q : ℕ}
    (S : Z → Fin q → Y) : (Fin q × X) → Z → Bool :=
  fun a z => F a.2 (S z a.1)

@[simp] theorem indexedInterlace_apply (F : X → Y → Bool) {q : ℕ}
    (S : Z → Fin q → Y) (a : Fin q × X) (z : Z) :
    indexedInterlace F S a z = F a.2 (S z a.1) := rfl

/-- Equation `eq:interlace-rank`. The zero-width case is included: it has
no rows and rank zero. No positivity or distinctness assumption is needed. -/
theorem fullInterlace_rank_le [Finite X] [Fintype Y]
    (F : X → Y → Bool) (q : ℕ) :
    (realMatrix (fullInterlace F q)).rank ≤ q * (realMatrix F).rank := by
  classical
  let V : Submodule ℝ (Y → ℝ) :=
    Submodule.span ℝ (Set.range (realMatrix F).row)
  let L : (Fin q → V) →ₗ[ℝ] ((Fin q → Y) → ℝ) :=
    { toFun := fun vs ys => ∑ i, (vs i).val (ys i)
      map_add' := by
        intro a b
        funext ys
        simp [Finset.sum_add_distrib]
      map_smul' := by
        intro c a
        funext ys
        simp [Finset.mul_sum] }
  have hrows : Submodule.span ℝ (Set.range (realMatrix (fullInterlace F q)).row)
      ≤ LinearMap.range L := by
    rw [Submodule.span_le]
    rintro v ⟨⟨i, x⟩, rfl⟩
    let row : V := ⟨(realMatrix F).row x, Submodule.subset_span ⟨x, rfl⟩⟩
    refine ⟨fun j => if j = i then row else 0, ?_⟩
    funext ys
    change (∑ j, ((if j = i then row else 0) : V).val (ys j)) =
      (realMatrix F) x (ys i)
    rw [Finset.sum_eq_single i]
    · simp [row, Matrix.row]
    · intro j _ hji
      simp [hji]
    · simp
  calc
    (realMatrix (fullInterlace F q)).rank =
        Module.finrank ℝ (Submodule.span ℝ
          (Set.range (realMatrix (fullInterlace F q)).row)) :=
      Matrix.rank_eq_finrank_span_row _
    _ ≤ Module.finrank ℝ (LinearMap.range L) := Submodule.finrank_mono hrows
    _ ≤ Module.finrank ℝ (Fin q → V) := LinearMap.finrank_range_le L
    _ = q * Module.finrank ℝ V := by
      rw [Module.finrank_pi_fintype]
      simp
    _ = q * (realMatrix F).rank := by
      rw [Matrix.rank_eq_finrank_span_row]

/-- Indexed relaxed interlacing is an input pullback of the full product. -/
theorem indexedInterlace_eq_pullback (F : X → Y → Bool) {q : ℕ}
    (S : Z → Fin q → Y) :
    indexedInterlace F S = fun a z => fullInterlace F q a (S z) := rfl

/-- The same rank bound holds for every indexed column family, including
repeated columns, without balancedness or randomness assumptions. -/
theorem indexedInterlace_rank_le [Finite X] [Fintype Y] [Fintype Z]
    (F : X → Y → Bool) {q : ℕ} (S : Z → Fin q → Y) :
    (realMatrix (indexedInterlace F S)).rank ≤ q * (realMatrix F).rank := by
  calc
    (realMatrix (indexedInterlace F S)).rank ≤
        (realMatrix (fullInterlace F q)).rank :=
      pullback_rank_le (fullInterlace F q) id S
    _ ≤ q * (realMatrix F).rank := fullInterlace_rank_le F q

theorem indexedInterlace_rank_le_of_le [Finite X] [Fintype Y] [Fintype Z]
    (F : X → Y → Bool) {q r : ℕ} (S : Z → Fin q → Y)
    (hF : (realMatrix F).rank ≤ r) :
    (realMatrix (indexedInterlace F S)).rank ≤ q * r :=
  (indexedInterlace_rank_le F S).trans (Nat.mul_le_mul_left q hF)

end Paper2
