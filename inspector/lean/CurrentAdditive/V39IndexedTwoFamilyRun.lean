import CurrentAdditive.V39ReferenceOwnersSharp
import CurrentAdditive.V39IndexedTwoFamilySummation
import Paper2.ReferenceOwnerLoss
import Paper2.RestorationRowPartition

/-! Current two-family laws on the actual annotated Alice-only frontier.
The initial supports retain original ordinary labels; the destination map
is computed from the protocol. Source lower bounds and receipt estimates
are applied to these same physical nodes. -/

namespace CurrentAdditive.V39IndexedTwoFamilyRun

open Paper2 Paper2.SourceMatrix Paper2.SourceSupportStep
open Paper2.ReferenceCertificates Paper2.ReferenceCertificateTree
open Paper2.ReferenceCertificateProtocol Paper2.ReferenceOwners
open scoped BigOperators Classical

variable {X Y I T : Type*} [Fintype X] [Fintype Y] [Fintype I]
  [DecidableEq X] [DecidableEq Y] [DecidableEq I]
  {q₁ q₂ s w : ℕ} [NeZero q₁] [NeZero s] [NeZero q₂]
  {μX : PositiveRationalLaw X} {μY : PositiveRationalLaw Y}
  (src : CurrentAdditive.DeterministicIndexedMatrix.Sources
    (D := 8192) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY)


abbrev Columns := V38IndexedTwoTag.Column src
abbrev Rows := Fin w × Columns src

def input (i : Fin w) (Z : (src.outer.Label × src.gamma.Label)) :
    Rows src (w := w) := (i,.inl Z)

noncomputable def initialFamily (R : Set (Rows src (w := w)))
    (E : Finset (Fin w)) : Family (Fin w) ((src.outer.Label × src.gamma.Label)) where
  active := Finset.univ \ E
  unsplit := Finset.univ \ E
  support i := Finset.univ.filter (fun Z => input src i Z ∈ R)

noncomputable def initialState
    (R : Set (Rows src (w := w)))
    (P : Workspace.Types.Protocol.Protocol (Rows src (w := w)) T Bool)
    (E : Finset (Fin w)) (r : ℕ) :
    State (Rows src (w := w)) T
      (Fin w) ((src.outer.Label × src.gamma.Label)) :=
  ⟨Paper2.ReferencePrefix.padAlicePrefix r P, R, initialFamily src R E⟩

theorem initial_valid
    (R : Set (Rows src (w := w)))
    (E : Finset (Fin w)) :
    (initialFamily src R E).unsplit ⊆ (initialFamily src R E).active := by rfl

theorem initial_reaches
    (R : Set (Rows src (w := w)))
    (E : Finset (Fin w)) :
    ∀ i ∈ (initialFamily src R E).active, ∀ Z ∈ (initialFamily src R E).support i,
      input src i Z ∈ R := by
  intro i _ Z hZ
  simpa [initialFamily] using hZ

theorem initial_units
    (R : Set (Rows src (w := w)))
    (E : Finset (Fin w)) : units (initialFamily src R E) = 2*(w-E.card) := by
  simp [units, initialFamily, Finset.card_sdiff]
  omega

noncomputable def firstRowLaw  (hw : 0 < w) :
    FiniteLaw (Rows src (w := w)) := by
  letI : Nonempty (Fin w) := Fin.pos_iff_nonempty.mp hw
  exact ((PositiveRationalLaw.uniform (Fin w)).prod (V38IndexedTwoTag.law src)).toFiniteLaw

theorem firstRowLaw_prob  (hw : 0 < w)
    (E : Fin w → Columns src → Prop) :
    (firstRowLaw src hw).prob (fun p => E p.1 p.2) =
      (∑ i : Fin w, (V38IndexedTwoTag.law src).toFiniteLaw.prob (E i))/w := by
  letI : Nonempty (Fin w) := Fin.pos_iff_nonempty.mp hw
  rw [firstRowLaw, PositiveRationalLaw.toFiniteLaw_prod, FiniteLaw.prod_prob]
  simp only [PositiveRationalLaw.toFiniteLaw, PositiveRationalLaw.uniform,
    Fintype.card_fin, Rat.cast_inv, Rat.cast_natCast]
  rw [← Finset.mul_sum]
  ring

theorem total_initial_defect  (hw : 0 < w)
    (R : Set (Rows src (w := w)))
    (η : ℝ) (hR : 1-η/(16*w) ≤ (firstRowLaw src hw).prob (· ∈ R)) :
    (∑ i : Fin w, (1-(V38IndexedTwoTag.law src).toFiniteLaw.prob (fun c => (i,c) ∈ R))) ≤ η/16 := by
  have hwR : (0 : ℝ) < w := by exact_mod_cast hw
  have hprob : (firstRowLaw src hw).prob (· ∈ R) =
      (∑ i : Fin w, (V38IndexedTwoTag.law src).toFiniteLaw.prob (fun c => (i,c) ∈ R))/w :=
    firstRowLaw_prob src hw (fun i c => (i,c) ∈ R)
  rw [hprob] at hR
  have hmul := (le_div_iff₀ hwR).mp hR
  simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one]
  have heq : (1-η/(16*(w : ℝ)))*w = w-η/16 := by field_simp
  rw [heq] at hmul
  simp only [CurrentAdditive.DeterministicIndexedMatrix.Sources.ordinaryLaw, CurrentAdditive.DeterministicIndexedMatrix.Sources.diagonalLaw] at *
  linarith

theorem reference_initial_defect  (hw : 0 < w)
    (R : Set (Rows src (w := w)))
    (E : Finset (Fin w)) (η : ℝ)
    (hR : 1-η/(16*w) ≤ (firstRowLaw src hw).prob (· ∈ R)) :
    (∑ i : Fin w, (1-mass (CurrentAdditive.DeterministicIndexedMatrix.Sources.ordinaryLaw src).toFiniteLaw
      ((initialFamily src R E).support i))) ≤ η/(16*(255/256 : ℝ)) := by
  have htotal := total_initial_defect src hw R η hR
  have hpoint (i : Fin w) : (255/256 : ℝ) *
      (1-mass (CurrentAdditive.DeterministicIndexedMatrix.Sources.ordinaryLaw src).toFiniteLaw ((initialFamily src R E).support i)) ≤
      1-(V38IndexedTwoTag.law src).toFiniteLaw.prob (fun c => (i,c) ∈ R) := by
    rw [V38IndexedTwoTag.prob_split]
    have hd := (CurrentAdditive.DeterministicIndexedMatrix.Sources.diagonalLaw src).toFiniteLaw.prob_le_one (fun c => (i,.inr c) ∈ R)
    simp only [mass, initialFamily, Finset.mem_filter, Finset.mem_univ, true_and, input]
    simp only [CurrentAdditive.DeterministicIndexedMatrix.Sources.ordinaryLaw, CurrentAdditive.DeterministicIndexedMatrix.Sources.diagonalLaw] at *
    nlinarith
  have hsum := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin w))) => hpoint i)
  rw [← Finset.mul_sum] at hsum
  have hh := hsum.trans htotal
  norm_num at hh ⊢
  simp only [CurrentAdditive.DeterministicIndexedMatrix.Sources.ordinaryLaw, CurrentAdditive.DeterministicIndexedMatrix.Sources.diagonalLaw] at *
  linarith

/-- The actual row set at an owner contains its unsplit support. The
original-law missing mass is therefore bounded by the geometric unsplit
loss, summed over distinct original origins. -/
theorem run_reference_loss  (hw : 0 < w)
    (r : ℕ) (hwr : w=2^r)
    (R : Set (Rows src (w := w)))
    (P : Workspace.Types.Protocol.Protocol (Rows src (w := w)) T Bool)
    (E : Finset (Fin w)) (η x : ℝ) (hx : 0 ≤ x)
    (hR : 1-η/(16*w) ≤ (firstRowLaw src hw).prob (· ∈ R))
    (hsmall : 2*(w : ℝ)^2*x ≤ η/(16*(255/256 : ℝ))) :
    let st := initialState src R P E r
    let μ := (CurrentAdditive.DeterministicIndexedMatrix.Sources.ordinaryLaw src).toFiniteLaw
    let tr := run μ (input src) (Paper2.ReferenceSchedule.floor w x) 0 r st
    let F := fun v : tr.Leaves => (tr.state v).family
    let final := fun v : tr.Leaves => (tr.route v).length=r
    let Owners := {v : tr.Leaves // v ∈ ownerNodes F final}
    (∑ v : Owners, (1-μ.prob (fun Z => input src (origin F final v) Z ∈ (tr.state v.val).rows))) ≤
      η/(8*(255/256 : ℝ)) := by
  classical
  dsimp only
  let st := initialState src R P E r
  let μ := (CurrentAdditive.DeterministicIndexedMatrix.Sources.ordinaryLaw src).toFiniteLaw
  let tr := run μ (input src) (Paper2.ReferenceSchedule.floor w x) 0 r st
  let F := fun v : tr.Leaves => (tr.state v).family
  let final := fun v : tr.Leaves => (tr.route v).length=r
  let Owners := {v : tr.Leaves // v ∈ ownerNodes F final}
  have hrun := Paper2.ReferenceOwnerLoss.run_owner_defects μ (input src) w r x hwr st
  have hreach := run_reaches μ (input src) (Paper2.ReferenceSchedule.floor w x) 0 r st
    (initial_reaches src R E)
  have hvalid := run_valid μ (input src) (Paper2.ReferenceSchedule.floor w x) 0 r st (initial_valid src R E)
  have hactual : (∑ v : Owners, (1-μ.prob
      (fun Z => input src (origin F final v) Z ∈ (tr.state v.val).rows))) ≤
      ∑ v : Owners, (1-mass μ ((tr.state v.val).family.support (origin F final v))) := by
    apply Finset.sum_le_sum
    intro v _
    have hi := hvalid v.val (origin_mem F final v)
    have hm : mass μ ((tr.state v.val).family.support (origin F final v)) ≤
        μ.prob (fun Z => input src (origin F final v) Z ∈ (tr.state v.val).rows) := by
      apply μ.prob_mono
      intro Z hZ
      exact hreach v.val (origin F final v) hi Z hZ
    simp only [CurrentAdditive.DeterministicIndexedMatrix.Sources.ordinaryLaw, CurrentAdditive.DeterministicIndexedMatrix.Sources.diagonalLaw] at *
    linarith
  have hinit := reference_initial_defect src hw R E η hR
  have hcard : Fintype.card Owners ≤ w := by
    simpa [Owners] using Fintype.card_le_of_injective (origin F final)
      (run_origin_injective μ (input src) (Paper2.ReferenceSchedule.floor w x) r st)
  have hcR : (Fintype.card Owners : ℝ) ≤ w := by exact_mod_cast hcard
  have hwR : (1 : ℝ) ≤ w := by exact_mod_cast hw
  have hn : 0 ≤ 2*((w : ℝ)-1)*x := by positivity
  have hm := mul_le_mul_of_nonneg_right hcR hn
  change (∑ v : Owners, (1-mass μ ((tr.state v.val).family.support (origin F final v)))) ≤
    (∑ i : Fin w, (1-mass μ (st.family.support i))) +
      (Fintype.card Owners : ℝ)*(2*((w : ℝ)-1)*x) at hrun
  have hpre : (∑ v : Owners, (1-μ.prob
      (fun Z => input src (origin F final v) Z ∈ (tr.state v.val).rows))) ≤
      η/(16*(255/256 : ℝ))+2*w*((w : ℝ)-1)*x := by
    have hh := hactual.trans hrun
    change (∑ i : Fin w, (1-mass μ (st.family.support i))) ≤
      η/(16*(255/256 : ℝ)) at hinit
    simp only [CurrentAdditive.DeterministicIndexedMatrix.Sources.ordinaryLaw, CurrentAdditive.DeterministicIndexedMatrix.Sources.diagonalLaw] at *
    nlinarith only [hh,hinit,hm]
  apply hpre.trans
  have hn2 : 0 ≤ 2*(w : ℝ)*x := by positivity
  ring_nf at hsmall ⊢
  simp only [CurrentAdditive.DeterministicIndexedMatrix.Sources.ordinaryLaw, CurrentAdditive.DeterministicIndexedMatrix.Sources.diagonalLaw] at *
  nlinarith only [hsmall,hn2]

end CurrentAdditive.V39IndexedTwoFamilyRun

#print axioms CurrentAdditive.V39IndexedTwoFamilyRun.initialFamily
#print axioms CurrentAdditive.V39IndexedTwoFamilyRun.initialState
#print axioms CurrentAdditive.V39IndexedTwoFamilyRun.initial_valid
#print axioms CurrentAdditive.V39IndexedTwoFamilyRun.initial_reaches
#print axioms CurrentAdditive.V39IndexedTwoFamilyRun.initial_units
#print axioms CurrentAdditive.V39IndexedTwoFamilyRun.firstRowLaw_prob
#print axioms CurrentAdditive.V39IndexedTwoFamilyRun.total_initial_defect
#print axioms CurrentAdditive.V39IndexedTwoFamilyRun.reference_initial_defect
#print axioms CurrentAdditive.V39IndexedTwoFamilyRun.run_reference_loss
