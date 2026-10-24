import Paper2.ReferencePublicDestinations
import Paper2.ReferenceOwnerLoss

/-!
# Reference loss on the actual Items-column owner run

Frozen v12 `eq:reference-loss`, lines 388--399. This uses the identical
`actualPaddedState` and literal original `Items` column carrier as
`ReferencePublicDestinations.actual_items_destinations`; no protocol or
column relabelling is performed. The theorem does not use an owner-count or
source-profile premise.
-/

namespace Paper2.ReferenceActualOwnerLoss

open Workspace.Types.Protocol SourceMatrix SourceLaws SourceSupportStep
open ReferenceCertificateTree ReferenceOwners ReferencePublicDestinations
open scoped BigOperators

variable {X Y V : Type*} [Fintype X] [Fintype Y] [Fintype V]
  {q₁ q₂ s w : ℕ} [NeZero q₁] [NeZero q₂] [NeZero s]

/-- Actual original unrestricted-row loss summed over physical owners,
with the displayed initial-deletion and quadratic schedule check. -/
theorem total_reference_loss (ν : PositiveRationalLaw Y)
    (r : ℕ) (hw : w = 2 ^ r)
    (R0 : Set (ActualRows (Y := Y) q₁ q₂ s w))
    (Y' : Set (ActualColumns (X := X) (V := V) q₁ q₂ s w))
    (row0 : R0) (col0 : Y') (P : Protocol R0 Y' Bool)
    (E0 : Finset (Fin w)) (η x : ℝ) (hx : 0 ≤ x)
    (hR0 : 1 - η / (16 * w) ≤
      (ReferenceInitial.firstRowLaw ν (by rw [hw]; positivity)).prob (· ∈ R0))
    (hsmall : 2 * (w : ℝ) ^ 2 * x ≤ η / (16 * (127 / 128 : ℝ))) :
    let μ := (rawLaw ν q₁ q₂ s).toFiniteLaw
    let st := actualPaddedState R0 Y' row0 col0 P E0 r
    let T := run μ ReferenceSourceInitial.input
      (ReferenceSchedule.floor w x) 0 r st
    let F := fun v : T.Leaves => (T.state v).family
    let final := fun v : T.Leaves => (T.route v).length = r
    let Owners := {v : T.Leaves // v ∈ ownerNodes F final}
    (∑ v : Owners, (1 - μ.prob
      (fun Z => ReferenceSourceInitial.input (origin F final v) Z ∈
        (T.state v.val).rows))) ≤ η / (8 * (127 / 128 : ℝ)) := by
  classical
  dsimp only
  let μ := (rawLaw ν q₁ q₂ s).toFiniteLaw
  let st := actualPaddedState R0 Y' row0 col0 P E0 r
  let T := run μ ReferenceSourceInitial.input (ReferenceSchedule.floor w x) 0 r st
  let F := fun v : T.Leaves => (T.state v).family
  let final := fun v : T.Leaves => (T.route v).length = r
  let Owners := {v : T.Leaves // v ∈ ownerNodes F final}
  have hwpos : 0 < w := by rw [hw]; positivity
  have hrun := ReferenceOwnerLoss.run_owner_defects μ
    ReferenceSourceInitial.input w r x hw st
  have hreach := run_reaches μ ReferenceSourceInitial.input
    (ReferenceSchedule.floor w x) 0 r st
    (ReferenceSourceInitial.initialFamily_reaches R0 E0)
  have hvalid := run_valid μ ReferenceSourceInitial.input
    (ReferenceSchedule.floor w x) 0 r st
    (ReferenceSourceInitial.initialFamily_valid R0 E0)
  have hactual : (∑ v : Owners, (1 - μ.prob
      (fun Z => ReferenceSourceInitial.input (origin F final v) Z ∈
        (T.state v.val).rows))) ≤
      ∑ v : Owners, (1 - mass μ
        ((T.state v.val).family.support (origin F final v))) := by
    apply Finset.sum_le_sum
    intro v _
    have hi := hvalid v.val (origin_mem F final v)
    have hm : mass μ ((T.state v.val).family.support (origin F final v)) ≤
        μ.prob (fun Z => ReferenceSourceInitial.input (origin F final v) Z ∈
          (T.state v.val).rows) := by
      apply μ.prob_mono
      intro Z hZ
      exact hreach v.val (origin F final v) hi Z hZ
    linarith
  have hinit : (∑ i : Fin w, (1 - mass μ (st.family.support i))) ≤
      η / (16 * (127 / 128 : ℝ)) := by
    simpa [st, actualPaddedState, actualOriginalState,
      ReferenceSourceInitial.initialFamily, mass, μ] using
      ReferenceInitial.reference_defect_sum_le ν hwpos R0 η hR0
  have hcard : Fintype.card Owners ≤ w := by
    have hc := Fintype.card_le_of_injective (origin F final)
      (run_origin_injective μ ReferenceSourceInitial.input
        (ReferenceSchedule.floor w x) r st)
    simpa [Owners] using hc
  have hcardR : (Fintype.card Owners : ℝ) ≤ (w : ℝ) := by
    exact_mod_cast hcard
  have hwR : (1 : ℝ) ≤ w := by exact_mod_cast hwpos
  have hnonneg : 0 ≤ 2 * ((w : ℝ) - 1) * x := by positivity
  have hmul := mul_le_mul_of_nonneg_right hcardR hnonneg
  have hpre : (∑ v : Owners, (1 - μ.prob
      (fun Z => ReferenceSourceInitial.input (origin F final v) Z ∈
        (T.state v.val).rows))) ≤
      η / (16 * (127 / 128 : ℝ)) +
        2 * w * ((w : ℝ) - 1) * x := by
    change (∑ v : Owners, (1 - mass μ
      ((T.state v.val).family.support (origin F final v)))) ≤
      (∑ i : Fin w, (1 - mass μ (st.family.support i))) +
        (Fintype.card Owners : ℝ) *
          (2 * ((w : ℝ) - 1) * x) at hrun
    nlinarith
  exact hpre.trans
    (RestorationSourceMargins.reference_loss_margin w η x hx hsmall)

end Paper2.ReferenceActualOwnerLoss

#print axioms Paper2.ReferenceActualOwnerLoss.total_reference_loss
