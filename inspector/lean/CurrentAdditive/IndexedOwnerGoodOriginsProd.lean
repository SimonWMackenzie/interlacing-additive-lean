import CurrentAdditive.IndexedOwnerScheduleProd

/-! Every original unsplit owner is one of the coordinates retained outside
the single conditioning exception set used by the owner initializer. -/

namespace CurrentAdditive.DeterministicIndexedMatrix.Sources

open Paper2 Paper2.ReferenceCertificates Paper2.ReferenceCertificateTree
  Paper2.ReferenceOwners Workspace.Types.Protocol

variable {I X Y : Type*} [Fintype I] [Fintype X] [Fintype Y]
  [DecidableEq I] [DecidableEq X] [DecidableEq Y]
  {q₁ q₂ s : ℕ} [NeZero s] [NeZero q₁] [NeZero q₂]
  {μX : PositiveRationalLaw X} {μY : PositiveRationalLaw Y}
  (src : Sources (D := 8192) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY)
  {μI : PositiveRationalLaw I} {w : ℕ}
  (streams : InternalStreams src μI w)

theorem indexed_initial_owner_origin_not_exception
    (R : Set (Fin w × Column src))
    (Yevent : Set (streams.metadataStream.Label ×
      (streams.baseStream.Label × streams.selectorStream.Label)))
    (row0 : R) (col0 : Yevent) (P : Protocol Yevent R Bool)
    (E : Finset (Fin w)) (r : ℕ) (x : ℝ)
    (st : State (Fin w × Column src)
      (streams.metadataStream.Label ×
        (streams.baseStream.Label × streams.selectorStream.Label))
      (Fin w) (src.outer.Label × src.gamma.Label))
    (hst : st = indexedInitialState src streams R Yevent row0 col0 P E r) :
    let T := run (ordinaryLaw src).toFiniteLaw
      (referenceInput src) (Paper2.ReferenceSchedule.floor w x) 0 r st
    let F := fun z : T.Leaves => (T.state z).family
    let final := fun z : T.Leaves => (T.route z).length = r
    ∀ u : {z // z ∈ ownerNodes F final}, origin F final u ∉ E := by
  classical
  intro T F final u
  have hmem : origin F final u ∈ (T.state u.val).family.unsplit :=
    origin_mem F final u
  have hsubset := (run_sets_subset (ordinaryLaw src).toFiniteLaw
    (referenceInput src) (Paper2.ReferenceSchedule.floor w x)
    0 r st u.val).2.1 hmem
  rw [hst] at hsubset
  change origin F final u ∈ Finset.univ \ E at hsubset
  exact (Finset.mem_sdiff.mp hsubset).2

theorem indexed_initial_owner_singletonTV
    (ν : PositiveRationalLaw (Row (I := I) src))
    (R : Set (Fin w × Column src))
    (Yevent : Set (streams.metadataStream.Label ×
      (streams.baseStream.Label × streams.selectorStream.Label)))
    (row0 : R) (col0 : Yevent) (P : Protocol Yevent R Bool)
    (E : Finset (Fin w)) (r : ℕ) (x ε : ℝ)
    (hYpos : 0 < streams.law.toFiniteLaw.prob (· ∈ Yevent))
    (hTV : ∀ J : Finset (Fin w),
      J ⊆ Finset.univ \ E → J.card ≤ 8 →
      projectionTV
        (condition streams.law.toFiniteLaw (· ∈ Yevent) hYpos)
        ν.toFiniteLaw (InternalStreams.decode src streams) J ≤ ε)
    (st : State (Fin w × Column src)
      (streams.metadataStream.Label ×
        (streams.baseStream.Label × streams.selectorStream.Label))
      (Fin w) (src.outer.Label × src.gamma.Label))
    (hst : st = indexedInitialState src streams R Yevent row0 col0 P E r) :
    let T := run (ordinaryLaw src).toFiniteLaw
      (referenceInput src) (Paper2.ReferenceSchedule.floor w x) 0 r st
    let F := fun z : T.Leaves => (T.state z).family
    let final := fun z : T.Leaves => (T.route z).length = r
    ∀ u : {z // z ∈ ownerNodes F final},
      projectionTV
        (condition streams.law.toFiniteLaw (· ∈ Yevent) hYpos)
        ν.toFiniteLaw (InternalStreams.decode src streams)
        {origin F final u} ≤ ε := by
  classical
  intro T F final u
  have hgood := indexed_initial_owner_origin_not_exception src streams
    R Yevent row0 col0 P E r x st hst u
  change origin F final u ∉ E at hgood
  have hsub : ({origin F final u} : Finset (Fin w)) ⊆ Finset.univ \ E := by
    simp [hgood]
  exact hTV _ hsub (by simp)

#print axioms indexed_initial_owner_origin_not_exception
#print axioms indexed_initial_owner_singletonTV

end CurrentAdditive.DeterministicIndexedMatrix.Sources
