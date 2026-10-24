import CurrentAdditive.IndexedOwnerProfileSchedule

/-! The full original indexed retained-row event pays the aggregate initial
ordinary-reference loss across all physical copies. -/

namespace CurrentAdditive.DeterministicIndexedMatrix.Sources

open Paper2
open scoped BigOperators

variable {X Y : Type*} [Fintype X] [Fintype Y]
  [DecidableEq X] [DecidableEq Y]
  {q₁ q₂ s : ℕ} [NeZero s] [NeZero q₁] [NeZero q₂]
  {μX : PositiveRationalLaw X} {μY : PositiveRationalLaw Y}
  (src : Sources (D := 8192) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY)
  {w : ℕ}

theorem indexed_initial_ordinary_loss_sum
    (hw : 0 < w) (R : Set (Fin w × Column src))
    (E : Finset (Fin w)) (η : ℝ)
    (hR : 1 - η / (16*w) ≤
      (indexedFirstRowLaw src hw).prob (· ∈ R)) :
    (∑ i : Fin w, (1 - (ordinaryLaw src).toFiniteLaw.prob
      (fun Z => Z ∈ (indexedInitialFamily src R E).support i))) ≤
      η / (16 * (127/128 : ℝ)) := by
  classical
  have hwR : (0 : ℝ) < w := by exact_mod_cast hw
  have hcomp : (indexedFirstRowLaw src hw).prob (fun p => p ∉ R) ≤
      η / (16 * w) := by
    rw [Paper2.SourceProjectionRetention.probability_complement]
    linarith
  rw [indexedFirstRowLaw_prob src hw (fun i Z => (i,Z) ∉ R)] at hcomp
  have hsum : (∑ i : Fin w,
      (columnLaw src).toFiniteLaw.prob (fun Z => (i,Z) ∉ R)) ≤ η/16 := by
    have hh := (div_le_iff₀ hwR).mp hcomp
    have heq : (η / (16 * (w : ℝ))) * w = η/16 := by
      field_simp
    rw [heq] at hh
    exact hh
  have hpoint (i : Fin w) :
      (127/128 : ℝ) *
        (1 - (ordinaryLaw src).toFiniteLaw.prob
          (fun Z => Z ∈ (indexedInitialFamily src R E).support i)) ≤
      (columnLaw src).toFiniteLaw.prob (fun Z => (i,Z) ∉ R) := by
    have hs := column_prob_split src (fun Z => (i,Z) ∉ R)
    have hf := src.outer.law.toFiniteLaw.prob_nonneg
      (fun Z => (i,Column.fixedTail Z) ∉ R)
    have hd := (diagonalLaw src).toFiniteLaw.prob_nonneg
      (fun Z => (i,Column.diagonal Z) ∉ R)
    have hc := Paper2.SourceProjectionRetention.probability_complement
      (ordinaryLaw src).toFiniteLaw
      (fun Z => (i,Column.ordinary Z) ∈ R)
    change (ordinaryLaw src).toFiniteLaw.prob
      (fun Z => (i,Column.ordinary Z) ∉ R) = _ at hc
    change (columnLaw src).toFiniteLaw.prob (fun Z => (i,Z) ∉ R) =
      (127/128 : ℝ) * (ordinaryLaw src).toFiniteLaw.prob
        (fun Z => (i,Column.ordinary Z) ∉ R) +
      (1/256 : ℝ) * src.outer.law.toFiniteLaw.prob
        (fun Z => (i,Column.fixedTail Z) ∉ R) +
      (1/256 : ℝ) * (diagonalLaw src).toFiniteLaw.prob
        (fun Z => (i,Column.diagonal Z) ∉ R) at hs
    rw [indexedInitialFamily_support_event src R E i]
    linarith
  have hpointsum := Finset.sum_le_sum
    (s := (Finset.univ : Finset (Fin w)))
    (fun i _ => hpoint i)
  rw [← Finset.mul_sum] at hpointsum
  have hg : (0 : ℝ) < 127/128 := by norm_num
  have hh := hpointsum.trans hsum
  have hh2 : (127/128 : ℝ) *
      (∑ i : Fin w, (1 - (ordinaryLaw src).toFiniteLaw.prob
        (fun Z => Z ∈ (indexedInitialFamily src R E).support i))) ≤ η/16 := by
    exact hh
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < 16 * (127/128 : ℝ))).2
  calc
    (∑ i : Fin w, (1 - (ordinaryLaw src).toFiniteLaw.prob
      (fun Z => Z ∈ (indexedInitialFamily src R E).support i))) *
        (16 * (127/128 : ℝ)) =
      ((127/128 : ℝ) *
        (∑ i : Fin w, (1 - (ordinaryLaw src).toFiniteLaw.prob
          (fun Z => Z ∈ (indexedInitialFamily src R E).support i)))) * 16 := by ring
    _ ≤ (η/16)*16 :=
      mul_le_mul_of_nonneg_right hh2 (by norm_num)
    _ = η := by ring

#print axioms indexed_initial_ordinary_loss_sum

end CurrentAdditive.DeterministicIndexedMatrix.Sources
