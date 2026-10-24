import CurrentAdditive.IndexedOwnerRunClosure
import Paper2.SourceProjectionRetention

/-! Initial ordinary reference supports from a retained rectangle of the
actual indexed W matrix.  All probabilities use original row labels. -/

namespace CurrentAdditive.DeterministicIndexedMatrix.Sources

open Paper2
open scoped BigOperators

variable {X Y : Type*} [Fintype X] [Fintype Y]
  [DecidableEq X] [DecidableEq Y]
  {q₁ q₂ s : ℕ} [NeZero s] [NeZero q₁] [NeZero q₂]
  {μX : PositiveRationalLaw X} {μY : PositiveRationalLaw Y}
  (src : Sources (D := 8192) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY)
  {w : ℕ}

/-- The actual W-row law, uniform in the original outer coordinate. -/
noncomputable def indexedFirstRowLaw (hw : 0 < w) :
    FiniteLaw (Fin w × Column src) := by
  letI : Nonempty (Fin w) := Fin.pos_iff_nonempty.mp hw
  exact ((PositiveRationalLaw.uniform (Fin w)).prod (columnLaw src)).toFiniteLaw

theorem indexedFirstRowLaw_prob (hw : 0 < w)
    (E : Fin w → Column src → Prop) :
    (indexedFirstRowLaw src hw).prob (fun p => E p.1 p.2) =
      (∑ i : Fin w, (columnLaw src).toFiniteLaw.prob (E i)) / w := by
  letI : Nonempty (Fin w) := Fin.pos_iff_nonempty.mp hw
  rw [indexedFirstRowLaw, PositiveRationalLaw.toFiniteLaw_prod,
    FiniteLaw.prod_prob]
  simp only [PositiveRationalLaw.toFiniteLaw, PositiveRationalLaw.uniform,
    Fintype.card_fin, Rat.cast_inv, Rat.cast_natCast]
  rw [← Finset.mul_sum]
  ring

/-- The normalized original ordinary labels retained in one original copy. -/
def indexedReferenceSupport (R : Set (Fin w × Column src)) (i : Fin w) :
    Set (src.outer.Label × src.gamma.Label) :=
  {Z | (i, .ordinary Z) ∈ R}

/-- A global near-full row event charges at most the total deletion budget
to any single original copy. -/
theorem indexed_copy_column_defect_le (hw : 0 < w)
    (R : Set (Fin w × Column src)) (η : ℝ)
    (hR : 1 - η / (16 * w) ≤ (indexedFirstRowLaw src hw).prob (· ∈ R))
    (i : Fin w) :
    1 - (columnLaw src).toFiniteLaw.prob (fun Z => (i,Z) ∈ R) ≤ η/16 := by
  have hwR : (0 : ℝ) < w := by exact_mod_cast hw
  have hcomp : (indexedFirstRowLaw src hw).prob (fun p => p ∉ R) ≤
      η / (16 * w) := by
    rw [Paper2.SourceProjectionRetention.probability_complement]
    linarith
  rw [indexedFirstRowLaw_prob src hw (fun i Z => (i,Z) ∉ R)] at hcomp
  have hsum : (∑ j : Fin w,
      (columnLaw src).toFiniteLaw.prob (fun Z => (j,Z) ∉ R)) ≤ η/16 := by
    rw [show η / (16 * (w : ℝ)) = (η/16) / w by ring] at hcomp
    have hd := (div_le_div_iff₀ hwR hwR).mp hcomp
    nlinarith
  have hi : (columnLaw src).toFiniteLaw.prob (fun Z => (i,Z) ∉ R) ≤
      ∑ j : Fin w, (columnLaw src).toFiniteLaw.prob (fun Z => (j,Z) ∉ R) := by
    exact Finset.single_le_sum
      (f := fun j : Fin w => (columnLaw src).toFiniteLaw.prob
        (fun Z => (j,Z) ∉ R))
      (fun j _ => (columnLaw src).toFiniteLaw.prob_nonneg _)
      (Finset.mem_univ i)
  have hcompl := Paper2.SourceProjectionRetention.probability_complement
    (columnLaw src).toFiniteLaw (fun Z => (i,Z) ∈ R)
  rw [← hcompl]
  exact hi.trans hsum

/-- Per-copy ordinary mass in the original selected row family. -/
theorem indexed_reference_mass_ge (hw : 0 < w)
    (R : Set (Fin w × Column src)) (η : ℝ)
    (hR : 1 - η / (16 * w) ≤ (indexedFirstRowLaw src hw).prob (· ∈ R))
    (i : Fin w) :
    1 - η / (16 * (127 / 128 : ℝ)) ≤
      (ordinaryLaw src).toFiniteLaw.prob
        (· ∈ indexedReferenceSupport src R i) := by
  have hdef := indexed_copy_column_defect_le src hw R η hR i
  have hcol : 1 - η/16 ≤
      (columnLaw src).toFiniteLaw.prob (fun Z => (i,Z) ∈ R) := by
    linarith
  have hord := ordinary_retained src (fun Z => (i,Z) ∈ R) (1-η/16) hcol
  change (1 - η/16 - (1-127/128)) / (127/128 : ℝ) ≤
    (ordinaryLaw src).toFiniteLaw.prob
      (· ∈ indexedReferenceSupport src R i) at hord
  convert hord using 1; ring

/-- The paper's strict margin supplies the initial certificate floor at
every original copy, before exceptional coordinates are deleted. -/
theorem indexed_reference_floor (hw : 0 < w)
    (R : Set (Fin w × Column src)) (η x : ℝ)
    (hR : 1 - η / (16 * w) ≤ (indexedFirstRowLaw src hw).prob (· ∈ R))
    (hmargin : 2*w*x + η / (16 * (127 / 128 : ℝ)) < 1)
    (i : Fin w) :
    Paper2.ReferenceSchedule.floor w x 0 ≤
      (ordinaryLaw src).toFiniteLaw.prob
        (· ∈ indexedReferenceSupport src R i) := by
  rw [Paper2.ReferenceSchedule.floor_zero]
  have hm := indexed_reference_mass_ge src hw R η hR i
  linarith

#print axioms indexed_copy_column_defect_le
#print axioms indexed_reference_mass_ge
#print axioms indexed_reference_floor

end CurrentAdditive.DeterministicIndexedMatrix.Sources
