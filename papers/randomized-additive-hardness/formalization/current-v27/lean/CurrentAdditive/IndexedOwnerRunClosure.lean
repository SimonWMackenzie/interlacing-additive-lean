import CurrentAdditive.IndexedOwnerLocalCost
import CurrentAdditive.IndexedOwnerRun

/-! The local actual-W reference contradictions close both cost premises of
the annotated original owner run.  All conditioned-law and initial-family
facts remain explicit global inputs. -/

namespace CurrentAdditive.DeterministicIndexedMatrix.Sources

open Paper2 Paper2.ReferenceCertificates Paper2.ReferenceCertificateTree
  Paper2.ReferenceCertificateProtocol Paper2.ReferenceOwners

variable {I X Y : Type*} [Fintype I] [Fintype X] [Fintype Y]
  [DecidableEq I] [DecidableEq X] [DecidableEq Y]
  {q₁ q₂ s : ℕ} [NeZero s] [NeZero q₁] [NeZero q₂]
  {μX : PositiveRationalLaw X} {μY : PositiveRationalLaw Y}
  (src : Sources (D := 8192) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY)
  {μI : PositiveRationalLaw I} {w : ℕ}
  (streams : InternalStreams src μI w)

theorem indexed_owner_capacity_of_source_bounds
    (ν : PositiveRationalLaw (Row (I := I) src))
    (R₀ : X → Y → Bool) (activity : I → Fin q₂ → Option (Fin s))
    (ξ₀ : Paper2.SourceMatrix.Tail s Y)
    (state : State (Fin w × Column src)
      (streams.metadataStream.Label ×
        (streams.baseStream.Label × streams.selectorStream.Label))
      (Fin w) (src.outer.Label × src.gamma.Label))
    (Yevent : Set (streams.metadataStream.Label ×
      (streams.baseStream.Label × streams.selectorStream.Label)))
    (E : Finset (Fin w)) (r n e₀ H : ℕ) (x v ε : ℝ)
    (hw : w = 2^r) (hrpos : 1 ≤ r)
    (hd : 2 ≤ H) (hx : 0 < x)
    (hscale : ∀ a ≤ r, (2 : ℝ)^a * x ≤ 1)
    (hprofile : RestrictionProfile
      (Nref src R₀ activity ξ₀)
      (ordinaryLaw src).toFiniteLaw ν.toFiniteLaw x (H : ℤ))
    (hwise : IsDWise 8192 streams.law.toFiniteLaw
      (InternalStreams.decode src streams) ν.toFiniteLaw)
    (hvalid : state.family.unsplit ⊆ state.family.active)
    (hprefix : Paper2.ReferencePrefix.NoEarlyLeaf r state.protocol)
    (hinitial : 2 ^ r ≤ n + e₀) (hunits : 2 * n ≤ units state.family)
    (houtside : ∀ i ∈ state.family.active, i ∉ E)
    (hfloor : ∀ i ∈ state.family.active,
      Paper2.ReferenceSchedule.floor w x 0 ≤
        (ordinaryLaw src).toFiniteLaw.prob
          (fun Z => Z ∈ state.family.support i))
    (hreach : ∀ i ∈ state.family.active,
      ∀ Z ∈ state.family.support i,
        (i, Column.ordinary Z) ∈ state.rows)
    (hv : 0 < v) (hv1 : v ≤ 1)
    (hY : v ≤ streams.law.toFiniteLaw.prob (· ∈ Yevent))
    (hεpos : 0 < ε)
    (hεcap : ε ≤ (2 : ℝ)^(-20 : ℤ) / 1024 *
      v^((1 : ℝ)/256))
    (hTV : ∀ J : Finset (Fin w),
      J ⊆ Finset.univ \ E → J.card ≤ 8 →
      projectionTV
        (condition streams.law.toFiniteLaw (· ∈ Yevent)
          (hv.trans_le hY)) ν.toFiniteLaw
        (InternalStreams.decode src streams) J ≤ ε)
    (hcompute : ∀ row ∈ state.rows, ∀ t ∈ Yevent,
      state.protocol.eval row t = W src streams R₀ activity ξ₀ t row)
    (hcost : state.protocol.cost ≤ H+r) :
    let T := run (ordinaryLaw src).toFiniteLaw
      (referenceInput src) (Paper2.ReferenceSchedule.floor w x) 0 r state
    let F := fun z : T.Leaves => (T.state z).family
    let final := fun z : T.Leaves => (T.route z).length = r
    2 ^ r - exceptionBudget e₀ ≤ (ownerNodes F final).card ∧
      exceptionalCapacity F final (fun z => 2 ^ (r - (T.route z).length)) ≤
        exceptionBudget e₀ := by
  classical
  let T := run (ordinaryLaw src).toFiniteLaw
    (referenceInput src) (Paper2.ReferenceSchedule.floor w x) 0 r state
  have hvalid' : ∀ z : T.Leaves,
      (T.state z).family.unsplit ⊆ (T.state z).family.active :=
    run_valid (ordinaryLaw src).toFiniteLaw (referenceInput src)
      (Paper2.ReferenceSchedule.floor w x) 0 r state hvalid
  have hfloor' : ∀ z : T.Leaves,
      ∀ i ∈ (T.state z).family.active,
        Paper2.ReferenceSchedule.floor w x ((T.route z).length) ≤
          (ordinaryLaw src).toFiniteLaw.prob
            (fun Z => Z ∈ (T.state z).family.support i) := by
    simpa [T, Paper2.SourceSupportStep.mass] using
      run_floor (ordinaryLaw src).toFiniteLaw (referenceInput src)
        (Paper2.ReferenceSchedule.floor w x)
        (Paper2.ReferenceSchedule.floor_half w x) 0 r state hfloor
  have hreach' : ∀ z : T.Leaves,
      ∀ i ∈ (T.state z).family.active,
        ∀ Z ∈ (T.state z).family.support i,
          (i, Column.ordinary Z) ∈ (T.state z).rows := by
    simpa [T, referenceInput] using
      run_reaches (ordinaryLaw src).toFiniteLaw (referenceInput src)
        (Paper2.ReferenceSchedule.floor w x) 0 r state hreach
  have houtside' : ∀ z : T.Leaves,
      ∀ i ∈ (T.state z).family.active, i ∉ E := by
    intro z i hi
    exact houtside i ((run_sets_subset (ordinaryLaw src).toFiniteLaw
      (referenceInput src) (Paper2.ReferenceSchedule.floor w x)
      0 r state z).1 hi)
  have hdepth : ∀ z : T.Leaves, (T.route z).length ≤ r := by
    intro z
    have h := Paper2.ReferencePrefix.runPrefix_depth_le r state.protocol
      (leavesEquiv (ordinaryLaw src).toFiniteLaw (referenceInput src)
        (Paper2.ReferenceSchedule.floor w x) 0 r state z)
    rwa [← leavesEquiv_route] at h
  have hcost' : ∀ z : T.Leaves,
      (T.state z).protocol.cost + (T.route z).length ≤ H+r := by
    intro z
    exact (run_cost_add_length (ordinaryLaw src).toFiniteLaw
      (referenceInput src) (Paper2.ReferenceSchedule.floor w x)
      0 r state z).trans hcost
  have hcompute' : ∀ z : T.Leaves,
      ∀ row ∈ (T.state z).rows, ∀ t ∈ Yevent,
        (T.state z).protocol.eval row t =
          W src streams R₀ activity ξ₀ t row := by
    intro z row hr t ht
    have hrf := (rows_iff_follows (ordinaryLaw src).toFiniteLaw
      (referenceInput src) (Paper2.ReferenceSchedule.floor w x)
      0 r state z row).mp hr
    have hroute := leavesEquiv_route (ordinaryLaw src).toFiniteLaw
      (referenceInput src) (Paper2.ReferenceSchedule.floor w x)
      0 r state z
    have heval := Paper2.ReferencePrefix.runPrefix_eval_of_follows
      r state.protocol
      (leavesEquiv (ordinaryLaw src).toFiniteLaw (referenceInput src)
        (Paper2.ReferenceSchedule.floor w x) 0 r state z)
      row t (by rw [← hroute]; exact hrf.2)
    rw [← leavesEquiv_protocol (ordinaryLaw src).toFiniteLaw
      (referenceInput src) (Paper2.ReferenceSchedule.floor w x)
      0 r state z] at heval
    exact heval.trans (hcompute row hrf.1 t ht)
  have hfinal : ∀ z : T.Leaves,
      (T.route z).length = r → (T.state z).family.active.card ≤ 1 := by
    intro z hz
    have hfloorNode : ∀ i ∈ (T.state z).family.active,
        2*x ≤ (ordinaryLaw src).toFiniteLaw.prob
          (fun Z => Z ∈ (T.state z).family.support i) := by
      intro i hi
      have hf := hfloor' z i hi
      rw [hz, Paper2.ReferenceSchedule.floor_dyadic x hw (by omega)] at hf
      simpa using hf
    have hscaleNode : 2*x ≤ 1 := by
      simpa only [pow_one] using hscale 1 hrpos
    apply owner_reference_final_active_le_one src streams ν R₀ activity ξ₀
      (T.state z).rows Yevent (T.state z).family E H x v ε
      (T.state z).protocol hd hx hscaleNode hprofile hwise
      (houtside' z) hfloorNode (hreach' z) hv hv1 hY
      hεpos hεcap hTV (hcompute' z)
    have hc := hcost' z
    omega
  have hbob : ∀ z : T.Leaves,
      (T.route z).length ≠ r →
      (units (T.state z).family : ℝ) <
        9 * ((2 ^ (r - (T.route z).length) : ℕ) : ℝ) / 8 := by
    intro z hne
    obtain hz | ⟨query, left, right, hnode⟩ :=
      run_stop_or_depth (ordinaryLaw src).toFiniteLaw
        (referenceInput src) (Paper2.ReferenceSchedule.floor w x)
        0 r state hprefix z
    · exact False.elim (hne hz)
    let a := r - (T.route z).length
    let κ := 2^a
    have ha : 1 ≤ a := by have := hdepth z; omega
    have hκ : κ = 2 * 2^(a-1) := by
      have heq : a = (a-1)+1 := by omega
      calc
        κ = 2^((a-1)+1) := congrArg (fun t : ℕ => 2^t) heq
        _ = 2*2^(a-1) := by rw [pow_succ]; omega
    have hfloorNode : ∀ i ∈ (T.state z).family.active,
        (2 : ℝ)^a*x ≤ (ordinaryLaw src).toFiniteLaw.prob
          (fun Z => Z ∈ (T.state z).family.support i) := by
      intro i hi
      have hf := hfloor' z i hi
      rw [Paper2.ReferenceSchedule.floor_dyadic x hw (hdepth z)] at hf
      have hp : 0 ≤ (2 : ℝ)^a*x := by positivity
      change 2 * (2 : ℝ)^a*x ≤ _ at hf
      nlinarith
    have hcostNode :
        (Workspace.Types.Protocol.Protocol.bNode query left right).cost ≤ H+a := by
      have hc := hcost' z
      rw [hnode] at hc
      dsimp [a]
      omega
    have hcomputeNode : ∀ row ∈ (T.state z).rows, ∀ t ∈ Yevent,
        (Workspace.Types.Protocol.Protocol.bNode query left right).eval row t =
          W src streams R₀ activity ξ₀ t row := by
      intro row hr t ht
      rw [← hnode]
      exact hcompute' z row hr t ht
    have hres := owner_reference_first_bob_units_lt src streams ν
      R₀ activity ξ₀ (T.state z).rows Yevent (T.state z).family E
      H a κ x v ε query left right ha hd hx hκ (hvalid' z)
      (hscale a (by omega)) hprofile hwise (houtside' z)
      hfloorNode (hreach' z) hv hv1 hY hεpos hεcap hTV
      hcomputeNode hcostNode
    simpa [a, κ] using hres
  exact indexed_owner_capacity_of_local_bounds src streams R₀ activity ξ₀
    x r n e₀ state hvalid hprefix hinitial hunits hfinal hbob

#print axioms indexed_owner_capacity_of_source_bounds

end CurrentAdditive.DeterministicIndexedMatrix.Sources
