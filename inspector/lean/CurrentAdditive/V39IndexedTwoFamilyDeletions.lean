import CurrentAdditive.V39IndexedTwoFamilyRun
import Paper2.SourceProjectionRetention

/-! Distinct owner origins charge each initially deleted protected (input src)
at most once. Current two-family masses are in complete-copy units. -/

namespace CurrentAdditive.V39IndexedTwoFamilyDeletions

open Paper2 Paper2.SourceMatrix CurrentAdditive.V39IndexedTwoFamilyRun
open CurrentAdditive.V39IndexedProtectedAccounting
open scoped BigOperators Classical

variable {X Y I T : Type*} [Fintype X] [Fintype Y] [Fintype I]
  [DecidableEq X] [DecidableEq Y] [DecidableEq I]
  {q₁ q₂ s w : ℕ} [NeZero q₁] [NeZero s] [NeZero q₂]
  {μX : PositiveRationalLaw X} {μY : PositiveRationalLaw Y}
  (src : CurrentAdditive.DeterministicIndexedMatrix.Sources
    (D := 8192) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY)
theorem sum_injective_le {I J : Type*} [Fintype I] [Fintype J]
    (f : I → ℝ) (g : J → I) (hinj : Function.Injective g)
    (hnonneg : ∀ i, 0 ≤ f i) : (∑ j : J, f (g j)) ≤ ∑ i : I, f i := by
  classical
  calc
    _ = ∑ i ∈ Finset.univ.image g, f i := by
      rw [Finset.sum_image]
      intro a _ b _ he
      exact hinj he
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun i _ _ => hnonneg i)

theorem deleted_owner_origins_le {J : Type*} [Fintype J]
    (hw : 0 < w)
    (R : Set (Rows src (w := w)))
    (η : ℝ) (hR : 1-η/(16*w) ≤ (firstRowLaw src hw).prob (· ∈ R))
    (origin : J → Fin w) (hinj : Function.Injective origin) :
    (∑ j : J, protectedDeleted src (fun c => (origin j,c) ∈ R)) ≤ η/16 := by
  have htotal := total_initial_defect src hw R η hR
  have hpoint (i : Fin w) : protectedDeleted src (fun c => (i,c) ∈ R) ≤
      1-(V38IndexedTwoTag.law src).toFiniteLaw.prob (fun c => (i,c) ∈ R) := by
    rw [V38IndexedTwoTag.prob_split]
    unfold protectedDeleted
    rw [Paper2.SourceProjectionRetention.probability_complement]
    have hr := (CurrentAdditive.DeterministicIndexedMatrix.Sources.ordinaryLaw src).toFiniteLaw.prob_le_one
      (fun c => (i,.inl c) ∈ R)
    simp only [CurrentAdditive.DeterministicIndexedMatrix.Sources.ordinaryLaw, CurrentAdditive.DeterministicIndexedMatrix.Sources.diagonalLaw] at *
    nlinarith
  calc
    _ ≤ ∑ i : Fin w, protectedDeleted src (fun c => (i,c) ∈ R) :=
      sum_injective_le _ origin hinj (fun i => mul_nonneg (by norm_num)
        ((CurrentAdditive.DeterministicIndexedMatrix.Sources.diagonalLaw src).toFiniteLaw.prob_nonneg _))
    _ ≤ ∑ i : Fin w, (1-(V38IndexedTwoTag.law src).toFiniteLaw.prob (fun c => (i,c) ∈ R)) :=
      Finset.sum_le_sum (fun i _ => hpoint i)
    _ ≤ _ := htotal

end CurrentAdditive.V39IndexedTwoFamilyDeletions

#print axioms CurrentAdditive.V39IndexedTwoFamilyDeletions.sum_injective_le
#print axioms CurrentAdditive.V39IndexedTwoFamilyDeletions.deleted_owner_origins_le
