import CurrentAdditive.IndexedIncomingDensity
import Paper2.ReferenceOwners
import Paper2.ReferenceSchedule

/-!
Appendix I `det:owners`: the conservation and distinct-origin part for the
actual indexed internal transpose.  The local first-Bob and final-node cost
contradictions are separate source-specific obligations.
-/

namespace CurrentAdditive.DeterministicIndexedMatrix.Sources

open Paper2 Paper2.ReferenceCertificates Paper2.ReferenceCertificateTree
  Paper2.ReferenceOwners Paper2.SourceSupportFrontier Paper2.SourceMatrix

variable {I X Y : Type*} [Fintype I] [Fintype X] [Fintype Y]
  [DecidableEq I] [DecidableEq X] [DecidableEq Y]
  {D q₁ q₂ s : ℕ} [NeZero s] [NeZero q₁] [NeZero q₂]
  {μX : PositiveRationalLaw X} {μY : PositiveRationalLaw Y}
  (src : Sources (D := D) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY)

variable {μI : PositiveRationalLaw I} {w : ℕ}
  (streams : InternalStreams src μI w)

/-- One original reference row at a physical outer position. -/
def referenceInput (i : Fin w) (Z : src.outer.Label × src.gamma.Label) :
    Fin w × Column src := (i, .ordinary Z)

/-- Entry alignment on the exact generated tuple index, retaining duplicate
source labels as distinct Bob inputs. -/
theorem indexed_reference_entry (R : X → Y → Bool)
    (activity : I → Fin q₂ → Option (Fin s)) (ξ₀ : Tail s Y)
    (t : streams.metadataStream.Label ×
      (streams.baseStream.Label × streams.selectorStream.Label))
    (i : Fin w) (Z : src.outer.Label × src.gamma.Label) :
    W src streams R activity ξ₀ t (referenceInput src i Z) =
      Nref src R activity ξ₀ Z (InternalStreams.decode src streams t i) := rfl

/-- The actual annotated Alice-only prefix carries original reference
supports from distinct origins to distinct final owners. -/
theorem indexed_owner_origins_injective
    (R : X → Y → Bool) (activity : I → Fin q₂ → Option (Fin s))
    (ξ₀ : Tail s Y) (x : ℝ) (r : ℕ)
    (state : State (Fin w × Column src)
      (streams.metadataStream.Label ×
        (streams.baseStream.Label × streams.selectorStream.Label))
      (Fin w) (src.outer.Label × src.gamma.Label)) :
    Function.Injective (origin
      (fun v : (run (ordinaryLaw src).toFiniteLaw
        (referenceInput src) (ReferenceSchedule.floor w x) 0 r state).Leaves =>
          ((run (ordinaryLaw src).toFiniteLaw
            (referenceInput src) (ReferenceSchedule.floor w x) 0 r state).state v).family)
      (fun v => ((run (ordinaryLaw src).toFiniteLaw
        (referenceInput src) (ReferenceSchedule.floor w x) 0 r state).route v).length = r)) :=
  run_origin_injective (ordinaryLaw src).toFiniteLaw (referenceInput src)
    (ReferenceSchedule.floor w x) r state

/-- The checked tree arithmetic for the indexed source.  Its two local
communication contradictions remain explicit hypotheses here, so this is
not yet the full `det:owners` theorem. -/
theorem indexed_owner_capacity_of_local_bounds
    (R : X → Y → Bool) (activity : I → Fin q₂ → Option (Fin s))
    (ξ₀ : Tail s Y) (x : ℝ) (r n e₀ : ℕ)
    (state : State (Fin w × Column src)
      (streams.metadataStream.Label ×
        (streams.baseStream.Label × streams.selectorStream.Label))
      (Fin w) (src.outer.Label × src.gamma.Label))
    (hvalid : state.family.unsplit ⊆ state.family.active)
    (hprefix : ReferencePrefix.NoEarlyLeaf r state.protocol)
    (hinitial : 2 ^ r ≤ n + e₀) (hunits : 2 * n ≤ units state.family)
    (hfinal : ∀ v : (run (ordinaryLaw src).toFiniteLaw
      (referenceInput src) (ReferenceSchedule.floor w x) 0 r state).Leaves,
      ((run (ordinaryLaw src).toFiniteLaw
        (referenceInput src) (ReferenceSchedule.floor w x) 0 r state).route v).length = r →
      ((run (ordinaryLaw src).toFiniteLaw
        (referenceInput src) (ReferenceSchedule.floor w x) 0 r state).state v).family.active.card ≤ 1)
    (hbob : ∀ v : (run (ordinaryLaw src).toFiniteLaw
      (referenceInput src) (ReferenceSchedule.floor w x) 0 r state).Leaves,
      ((run (ordinaryLaw src).toFiniteLaw
        (referenceInput src) (ReferenceSchedule.floor w x) 0 r state).route v).length ≠ r →
      (units ((run (ordinaryLaw src).toFiniteLaw
        (referenceInput src) (ReferenceSchedule.floor w x) 0 r state).state v).family : ℝ) <
        9 * ((2 ^ (r - ((run (ordinaryLaw src).toFiniteLaw
          (referenceInput src) (ReferenceSchedule.floor w x) 0 r state).route v).length) : ℕ) : ℝ) / 8) :
    let T := run (ordinaryLaw src).toFiniteLaw
      (referenceInput src) (ReferenceSchedule.floor w x) 0 r state
    let F := fun v : T.Leaves => (T.state v).family
    let final := fun v : T.Leaves => (T.route v).length = r
    2 ^ r - exceptionBudget e₀ ≤ (ownerNodes F final).card ∧
      exceptionalCapacity F final (fun v => 2 ^ (r - (T.route v).length)) ≤
        exceptionBudget e₀ := by
  exact run_owner_count (ordinaryLaw src).toFiniteLaw
    (referenceInput src) (ReferenceSchedule.floor w x) r state n e₀
    hvalid hprefix hinitial hunits hfinal hbob

#print axioms indexed_reference_entry
#print axioms indexed_owner_origins_injective
#print axioms indexed_owner_capacity_of_local_bounds

end CurrentAdditive.DeterministicIndexedMatrix.Sources
