import CurrentAdditive.GeneratedWOwnerEscapeV2
import Paper2.ReferenceOwnerLoss
import Paper2.RestorationSourceMargins

/-! Ordinary reference loss on the physical actual-indexed W owner run. -/

namespace CurrentAdditive.DeterministicIndexedMatrix.Sources

open Paper2 Paper2.ReferenceCertificateTree Paper2.ReferenceOwners
  Paper2.SourceSupportStep
open scoped BigOperators

private def indexedReferenceInputLocal
    {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y]
    {D q₁ q₂ s w : ℕ} [NeZero s] [NeZero q₁] [NeZero q₂]
    {μX : PositiveRationalLaw X} {μY : PositiveRationalLaw Y}
    (src : Sources (D := D) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY)
    (i : Fin w) (z : src.outer.Label × src.gamma.Label) :
    Fin w × Column src := (i,Column.ordinary z)

variable {X Y : Type*} [Fintype X] [Fintype Y]
  [DecidableEq X] [DecidableEq Y]
  {D q₁ q₂ s w : ℕ} [NeZero s] [NeZero q₁] [NeZero q₂]
  {μX : PositiveRationalLaw X} {μY : PositiveRationalLaw Y}
  (src : Sources (D := D) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY)

theorem indexed_run_owner_ordinary_loss
    {B : Type*} (state : State (Fin w × Column src) B
      (Fin w) (src.outer.Label × src.gamma.Label))
    (r : ℕ) (x η : ℝ)
    (hw : w = 2^r) (hx : 0 ≤ x)
    (hsmall : 2 * (w : ℝ)^2 * x ≤
      η / (16 * (127/128 : ℝ)))
    (hvalid : state.family.unsplit ⊆ state.family.active)
    (hreach : ∀ i ∈ state.family.active,
      ∀ z ∈ state.family.support i,
        (i,Column.ordinary z) ∈ state.rows)
    (hinit : (Finset.univ.sum (fun i : Fin w =>
      1 - (ordinaryLaw src).toFiniteLaw.prob
        (fun z => z ∈ state.family.support i))) ≤
      η / (16 * (127/128 : ℝ))) :
    let T := run (ordinaryLaw src).toFiniteLaw (indexedReferenceInputLocal src)
      (Paper2.ReferenceSchedule.floor w x) 0 r state
    let F := fun v : T.Leaves => (T.state v).family
    let final := fun v : T.Leaves => (T.route v).length = r
    let Owners := {v : T.Leaves // v ∈ ownerNodes F final}
    let defect : Owners → ℝ := fun v =>
      1 - (ordinaryLaw src).toFiniteLaw.prob
        (fun z => (origin F final v,Column.ordinary z) ∈
          (T.state v.val).rows)
    (Finset.univ.sum (fun v : Owners => defect v)) ≤
      η / (8 * (127/128 : ℝ)) := by
  classical
  dsimp only
  let μ := (ordinaryLaw src).toFiniteLaw
  let T := run μ (indexedReferenceInputLocal src)
    (Paper2.ReferenceSchedule.floor w x) 0 r state
  let F := fun v : T.Leaves => (T.state v).family
  let final := fun v : T.Leaves => (T.route v).length = r
  let Owners := {v : T.Leaves // v ∈ ownerNodes F final}
  have hrun := Paper2.ReferenceOwnerLoss.run_owner_defects μ
    (indexedReferenceInputLocal src) w r x hw state
  have hreach' := run_reaches μ (indexedReferenceInputLocal src)
    (Paper2.ReferenceSchedule.floor w x) 0 r state hreach
  have hvalid' := run_valid μ (indexedReferenceInputLocal src)
    (Paper2.ReferenceSchedule.floor w x) 0 r state hvalid
  have hactual : (Finset.univ.sum (fun v : Owners =>
      1 - μ.prob (fun z => (origin F final v,Column.ordinary z) ∈
        (T.state v.val).rows))) ≤
      Finset.univ.sum (fun v : Owners =>
        (1 - mass μ ((T.state v.val).family.support (origin F final v)))) := by
    apply Finset.sum_le_sum
    intro v _
    have hi := hvalid' v.val (origin_mem F final v)
    have hm : mass μ ((T.state v.val).family.support (origin F final v)) ≤
        μ.prob (fun z => (origin F final v,Column.ordinary z) ∈
          (T.state v.val).rows) := by
      apply μ.prob_mono
      intro z hz
      exact hreach' v.val (origin F final v) hi z hz
    linarith
  have hcard : Fintype.card Owners ≤ w := by
    have hc := Fintype.card_le_of_injective (origin F final)
      (run_origin_injective μ (indexedReferenceInputLocal src)
        (Paper2.ReferenceSchedule.floor w x) r state)
    simpa [Owners] using hc
  have hcardR : (Fintype.card Owners : ℝ) ≤ (w : ℝ) := by
    exact_mod_cast hcard
  have hnonneg : 0 ≤ 2 * ((w : ℝ) - 1) * x := by
    have hwpos : 0 < w := by rw [hw]; positivity
    have hwR : (1 : ℝ) ≤ w := by exact_mod_cast hwpos
    positivity
  have hmul := mul_le_mul_of_nonneg_right hcardR hnonneg
  have hpre : (Finset.univ.sum (fun v : Owners =>
      1 - μ.prob (fun z => (origin F final v,Column.ordinary z) ∈
        (T.state v.val).rows))) ≤
      η / (16 * (127/128 : ℝ)) +
        2 * w * ((w : ℝ)-1) * x := by
    have hinit' : (Finset.univ.sum (fun i : Fin w =>
        1 - mass μ (state.family.support i))) ≤
        η / (16 * (127/128 : ℝ)) := hinit
    have hrun' : (Finset.univ.sum (fun v : Owners =>
        1 - mass μ ((T.state v.val).family.support (origin F final v)))) ≤
        (Finset.univ.sum (fun i : Fin w =>
          1 - mass μ (state.family.support i))) +
          (Fintype.card Owners : ℝ) *
            (2 * ((w : ℝ)-1) * x) := by
      convert hrun using 1
    nlinarith [hrun']
  exact hpre.trans
    (Paper2.RestorationSourceMargins.reference_loss_margin w η x hx hsmall)

end CurrentAdditive.DeterministicIndexedMatrix.Sources

#print axioms CurrentAdditive.DeterministicIndexedMatrix.Sources.indexed_run_owner_ordinary_loss
