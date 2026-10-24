import CurrentAdditive.V39IndexedTwoFamilyDeletions

/-! Exact receiving events at the computed physical frontier. This joins
the current two-family summation to actual protocol node row sets; the
destination partition is derived from the protocol, never assumed. -/

namespace CurrentAdditive.V39IndexedTwoFamilyRunConservation

open Paper2 Paper2.SourceMatrix Paper2.ReferenceCertificateTree
open Paper2.ReferenceCertificateProtocol CurrentAdditive.V39IndexedTwoFamilyRun
open CurrentAdditive.V39IndexedProtectedAccounting
open scoped BigOperators Classical

variable {X Y I T : Type*} [Fintype X] [Fintype Y] [Fintype I]
  [DecidableEq X] [DecidableEq Y] [DecidableEq I]
  {q₁ q₂ s w : ℕ} [NeZero q₁] [NeZero s] [NeZero q₂]
  {μX : PositiveRationalLaw X} {μY : PositiveRationalLaw Y}
  (src : CurrentAdditive.DeterministicIndexedMatrix.Sources
    (D := 8192) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY)


theorem contradiction
    (state : State (Rows src (w := w)) T
      (Fin w) ((src.outer.Label × src.gamma.Label))) (r : ℕ) (η x K q : ℝ)
    (hw : 2 ≤ w) (hη : 0 < η) (hK : 0 ≤ K)
    (hR : 1-η/(16*w) ≤ (firstRowLaw src (by omega : 0 < w)).prob (· ∈ state.rows))
    (owners : Finset (run (CurrentAdditive.DeterministicIndexedMatrix.Sources.ordinaryLaw src).toFiniteLaw (input src)
      (Paper2.ReferenceSchedule.floor w x) 0 r state).Leaves)
    (origin : (run (CurrentAdditive.DeterministicIndexedMatrix.Sources.ordinaryLaw src).toFiniteLaw (input src)
      (Paper2.ReferenceSchedule.floor w x) 0 r state).Leaves → Fin w)
    (hinj : Function.Injective (fun v : owners => origin v.val))
    (hcount : (3/4 : ℝ)*w ≤ owners.card) (hcountle : owners.card ≤ w)
    (hmiss : ∀ v ∈ owners, η < 1-(V38IndexedTwoTag.law src).toFiniteLaw.prob
      (fun c => (origin v,c) ∈ ((run (CurrentAdditive.DeterministicIndexedMatrix.Sources.ordinaryLaw src).toFiniteLaw (input src)
        (Paper2.ReferenceSchedule.floor w x) 0 r state).state v).rows))
    (hloss : (∑ v ∈ owners, (1-(CurrentAdditive.DeterministicIndexedMatrix.Sources.ordinaryLaw src).toFiniteLaw.prob
      (fun Z => input src (origin v) Z ∈ ((run (CurrentAdditive.DeterministicIndexedMatrix.Sources.ordinaryLaw src).toFiniteLaw (input src)
        (Paper2.ReferenceSchedule.floor w x) 0 r state).state v).rows))) ≤ η/(8*(255/256 : ℝ)))
    (hincoming : ∀ v ∉ owners,
      (∑ d ∈ owners, (1/256 : ℝ)*(CurrentAdditive.DeterministicIndexedMatrix.Sources.diagonalLaw src).toFiniteLaw.prob
        (fun j => (origin d,.inr j) ∈ ((run (CurrentAdditive.DeterministicIndexedMatrix.Sources.ordinaryLaw src).toFiniteLaw (input src)
          (Paper2.ReferenceSchedule.floor w x) 0 r state).state v).rows)) ≤
        K * (2^(r-((run (CurrentAdditive.DeterministicIndexedMatrix.Sources.ordinaryLaw src).toFiniteLaw (input src)
          (Paper2.ReferenceSchedule.floor w x) 0 r state).route v).length) : ℕ))
    (hexceptional : K * (∑ v ∈ Finset.univ \ owners,
      ((2^(r-((run (CurrentAdditive.DeterministicIndexedMatrix.Sources.ordinaryLaw src).toFiniteLaw (input src)
        (Paper2.ReferenceSchedule.floor w x) 0 r state).route v).length) : ℕ) : ℝ)) ≤ η*w/16)
    (hforeign : ∀ d ∈ owners, ∀ v ∈ owners, d ≠ v →
      (1/256 : ℝ)*(CurrentAdditive.DeterministicIndexedMatrix.Sources.diagonalLaw src).toFiniteLaw.prob
        (fun j => (origin d,.inr j) ∈ ((run (CurrentAdditive.DeterministicIndexedMatrix.Sources.ordinaryLaw src).toFiniteLaw (input src)
          (Paper2.ReferenceSchedule.floor w x) 0 r state).state v).rows) ≤
      (1/256 : ℝ)*(2*q*x+4*(1-(CurrentAdditive.DeterministicIndexedMatrix.Sources.ordinaryLaw src).toFiniteLaw.prob
        (fun Z => input src (origin v) Z ∈ ((run (CurrentAdditive.DeterministicIndexedMatrix.Sources.ordinaryLaw src).toFiniteLaw (input src)
          (Paper2.ReferenceSchedule.floor w x) 0 r state).state v).rows))))
    (hqx : 0 ≤ q*x) (hwidth : 4*(1/256 : ℝ)*w*q*x ≤ η/32) : False := by
  classical
  let μ := (CurrentAdditive.DeterministicIndexedMatrix.Sources.ordinaryLaw src).toFiniteLaw
  let floor := Paper2.ReferenceSchedule.floor w x
  let tr := run μ (input src) floor 0 r state
  let keep := fun i c => (i,c) ∈ state.rows
  let dest := fun i c => destination μ (input src) floor 0 r state (i,c)
  have hnode (i : Fin w) (v : tr.Leaves) :
      (fun c => keep i c ∧ dest i c=v) = (fun c => (i,c) ∈ (tr.state v).rows) := by
    funext c
    apply propext
    by_cases hk : (i,c) ∈ state.rows
    · have hh := rows_iff_destination μ (input src) floor 0 r state (i,c) hk v
      dsimp only [keep,dest]
      exact ⟨fun h => hh.mpr h.2.symm, fun h => ⟨hk,(hh.mp h).symm⟩⟩
    · have hn : (i,c) ∉ (tr.state v).rows := fun h => hk
        (Paper2.ReferenceRunCorrectness.rows_subset μ (input src) floor 0 r state v h)
      simp [keep,hk,hn]
  have hordinary (i : Fin w) (v : tr.Leaves) :
      (fun Z => keep i (.inl Z) ∧ dest i (.inl Z)=v) =
      (fun Z => input src i Z ∈ (tr.state v).rows) := by
    funext Z
    exact congrFun (hnode i v) (.inl Z)
  have hdeleted := V39IndexedTwoFamilyDeletions.deleted_owner_origins_le src (by omega : 0 < w)
    state.rows η hR (fun v : owners => origin v.val) hinj
  change (∑ v : owners, protectedDeleted src (fun c => (origin v.val,c) ∈ state.rows)) ≤ η/16 at hdeleted
  rw [Finset.sum_coe_sort owners (fun v => protectedDeleted src (fun c => (origin v,c) ∈ state.rows))] at hdeleted
  apply V39IndexedTwoFamilySummation.conservation_contradiction src keep dest owners origin
    (fun v => 2^(r-(tr.route v).length)) η K q x hw hη hK hcount hcountle
  · intro v hv
    rw [hnode]
    exact hmiss v hv
  · exact hdeleted
  · unfold referenceLoss
    simp_rw [hordinary]
    exact hloss
  · intro v hv
    have heq (d : tr.Leaves) :
        (fun j => keep (origin d) (.inr j) ∧ dest (origin d) (.inr j)=v) =
        (fun j => (origin d,.inr j) ∈ (tr.state v).rows) := by
      funext j
      exact congrFun (hnode (origin d) v) (.inr j)
    simp_rw [heq]
    exact hincoming v hv
  · exact hexceptional
  · intro d hd v hv hne
    have heq : (fun j => keep (origin d) (.inr j) ∧ dest (origin d) (.inr j)=v) =
        (fun j => (origin d,.inr j) ∈ (tr.state v).rows) := by
      funext j
      exact congrFun (hnode (origin d) v) (.inr j)
    rw [heq]
    unfold referenceLoss
    rw [hordinary]
    exact hforeign d hd v hv hne
  · exact hqx
  · exact hwidth

end CurrentAdditive.V39IndexedTwoFamilyRunConservation

#print axioms CurrentAdditive.V39IndexedTwoFamilyRunConservation.contradiction
