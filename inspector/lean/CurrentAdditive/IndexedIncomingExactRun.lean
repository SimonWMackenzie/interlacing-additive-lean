import CurrentAdditive.IndexedOwnerInitializedRun
import CurrentAdditive.IndexedIncomingBobClosure
import Paper2.PairedSelectorCapacityFibre

/-! The incoming protected receipt bound on each genuine node of the
initialized physical W run.  The only external premises are the base A
profile and the global numerical tests; node correctness, cost and the
first-Bob/final dichotomy are derived from the original protocol. -/

namespace CurrentAdditive.DeterministicIndexedMatrix.Sources

open Paper2 Paper2.ReferenceCertificates Paper2.ReferenceCertificateTree
  Paper2.ReferenceCertificateProtocol Paper2.ReferenceOwners
  Workspace.Types.Protocol
open scoped BigOperators

variable {I X Y : Type*} [Fintype I] [Fintype X] [Fintype Y]
  [DecidableEq I] [DecidableEq X] [DecidableEq Y]
  {q₁ q₂ s : ℕ} [NeZero s] [NeZero q₁] [NeZero q₂]
  {μX : PositiveRationalLaw X} {μY : PositiveRationalLaw Y}
  (src : Sources (D := 8192) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY)
  {μI : PositiveRationalLaw I} {w : ℕ}
  (streams : InternalStreams src μI w)

theorem indexed_incoming_each_initialised_node
    (R₀ : X → Y → Bool) (activity : I → Fin q₂ → Option (Fin s))
    (ξ₀ : Paper2.SourceMatrix.Tail s Y)
    (R : Set (Fin w × Column src))
    (Yevent : Set (streams.metadataStream.Label ×
      (streams.baseStream.Label × streams.selectorStream.Label)))
    (row0 : R) (col0 : Yevent) (P : Protocol Yevent R Bool)
    (E : Finset (Fin w)) (r H H₁ a₀ : ℕ) (x θ : ℝ)
    (hw : w = 2^r) (hs : 0 < s) (ha₀ : 1 ≤ a₀)
    (hd : 2 ≤ H₁) (hx : 0 < x)
    (hcostlink : H+1 = H₁+a₀)
    (hprofile : RestrictionProfile (A src R₀)
      src.gamma.law.toFiniteLaw
      (((PositiveRationalLaw.uniform (Fin q₁)).prod μX).toFiniteLaw)
      x (H₁ : ℤ))
    (hscale : ∀ k ≤ r, (2 : ℝ)^(a₀+k) * x ≤ 1)
    (hblocks : ∀ k ≤ r, 2^(a₀+k-1) ≤ s * 2^k * q₂)
    (hδscale : ∀ k ≤ r, ∀ j : Fin (r+2),
      (2 : ℝ)^(a₀+k) * x ≤ ((1/2 : ℝ)^j.val)/4)
    (hθ : 0 < θ)
    (hYevent : θ ≤ streams.law.toFiniteLaw.prob (· ∈ Yevent))
    (hguard : ∀ k ≤ r, ∀ m : ℕ,
      256 * (s : ℝ) * (2^k : ℕ) ≤ m →
      2 * ((64 : ℝ) * m) ^ 128 /
        (((255 / 256 : ℝ) - 1/2) * m) ^ 256 ≤ θ/4)
    (hException : ∀ j : Fin (r+2),
      conditioningExceptionCountR 1024 (θ/4)
        (((1/2 : ℝ)^j.val)/2) ≤ s*q₂)
    (hP : P.Computes (fun t row => W src streams R₀ activity ξ₀ t.val row.val))
    (hPcost : P.cost ≤ H+r) :
    let st := indexedInitialState src streams R Yevent row0 col0 P E r
    let T := run (ordinaryLaw src).toFiniteLaw
      (referenceInput src) (Paper2.ReferenceSchedule.floor w x) 0 r st
    ∀ v : T.Leaves,
      (∑ i : Fin w, protectedReceipt src w (T.state v).rows i) <
        (1024 * (1/256 : ℝ) * (r+2) * s) *
          (2^(r-(T.route v).length) : ℕ) := by
  classical
  let st := indexedInitialState src streams R Yevent row0 col0 P E r
  let T := run (ordinaryLaw src).toFiniteLaw
    (referenceInput src) (Paper2.ReferenceSchedule.floor w x) 0 r st
  have hprefix : Paper2.ReferencePrefix.NoEarlyLeaf r st.protocol :=
    indexedInitialState_noEarlyLeaf src streams R Yevent row0 col0 P E r
  have hcost : st.protocol.cost ≤ H+r :=
    indexedInitialState_cost src streams R Yevent row0 col0 P E r H hPcost
  have hdepth : ∀ v : T.Leaves, (T.route v).length ≤ r := by
    intro v
    have h := Paper2.ReferencePrefix.runPrefix_depth_le r st.protocol
      (leavesEquiv (ordinaryLaw src).toFiniteLaw (referenceInput src)
        (Paper2.ReferenceSchedule.floor w x) 0 r st v)
    rwa [← leavesEquiv_route] at h
  have hcost' : ∀ v : T.Leaves,
      (T.state v).protocol.cost + (T.route v).length ≤ H+r := by
    intro v
    exact (run_cost_add_length (ordinaryLaw src).toFiniteLaw
      (referenceInput src) (Paper2.ReferenceSchedule.floor w x)
      0 r st v).trans hcost
  have hcompute' : ∀ v : T.Leaves,
      ∀ row ∈ (T.state v).rows, ∀ t ∈ Yevent,
        (T.state v).protocol.eval row t =
          W src streams R₀ activity ξ₀ t row := by
    intro v row hr t ht
    have hrf := (rows_iff_follows (ordinaryLaw src).toFiniteLaw
      (referenceInput src) (Paper2.ReferenceSchedule.floor w x)
      0 r st v row).mp hr
    have hroute := leavesEquiv_route (ordinaryLaw src).toFiniteLaw
      (referenceInput src) (Paper2.ReferenceSchedule.floor w x)
      0 r st v
    have heval := Paper2.ReferencePrefix.runPrefix_eval_of_follows
      r st.protocol
      (leavesEquiv (ordinaryLaw src).toFiniteLaw (referenceInput src)
        (Paper2.ReferenceSchedule.floor w x) 0 r st v)
      row t (by rw [← hroute]; exact hrf.2)
    rw [← leavesEquiv_protocol (ordinaryLaw src).toFiniteLaw
      (referenceInput src) (Paper2.ReferenceSchedule.floor w x)
      0 r st v] at heval
    exact heval.trans (indexedInitialState_correct src streams R₀
      activity ξ₀ R Yevent row0 col0 P hP E r
      ⟨row, hrf.1⟩ ⟨t, ht⟩)
  change ∀ v : T.Leaves,
    (∑ i : Fin w, protectedReceipt src w (T.state v).rows i) <
      (1024 * (1/256 : ℝ) * (r+2) * s) *
        (2^(r-(T.route v).length) : ℕ)
  intro v
  let k := r - (T.route v).length
  let κ := 2^k
  let a := a₀+k
  have hk : k ≤ r := Nat.sub_le _ _
  have hκ : 1 ≤ κ := by
    have hp : 0 < κ := by dsimp [κ]; positivity
    omega
  have ha : 1 ≤ a := by dsimp [a]; omega
  have hbudget : (T.state v).protocol.cost ≤ H + k := by
    have hc := hcost' v
    dsimp [k]
    omega
  have hlink : H₁+a = H+1+k := by dsimp [a]; omega
  have hθhalf : θ/2 ≤ streams.law.toFiniteLaw.prob (· ∈ Yevent) := by
    linarith
  by_cases hfinal : (T.route v).length = r
  · have hkzero : k = 0 := by dsimp [k]; omega
    have hκone : κ = 1 := by simp [κ, hkzero]
    have haone : a = a₀ := by simp [a, hkzero]
    let Q := Workspace.UpperBound.Protocol.comap
      (fun row : (T.state v).rows => row.val)
      (fun t : Yevent => t.val) (T.state v).protocol
    have hQ : Q.Computes (fun row t =>
        W src streams R₀ activity ξ₀ t.val row.val) := by
      intro row t
      rw [Workspace.UpperBound.Protocol.comap_eval]
      exact hcompute' v row.val row.property t.val t.property
    have hrestrict : Paper2.Compression.restrictionD
        (fun row t => W src streams R₀ activity ξ₀ t row)
        (T.state v).rows Yevent ≤ (T.state v).protocol.cost := by
      have hh := Paper2.PairedSelectorCapacityFibre.restrictionD_le_protocol
        (fun row t => W src streams R₀ activity ξ₀ t row)
        (T.state v).rows Yevent Q hQ
      simpa [Q, Workspace.UpperBound.Protocol.comap_cost] using hh
    have hnode : Paper2.Compression.restrictionD
        (fun row t => W src streams R₀ activity ξ₀ t row)
        (T.state v).rows Yevent < H₁+a₀ := by
      have hc := hbudget
      rw [hkzero] at hc
      omega
    have hres := incoming_protected_mass_lt src streams
      r 1 H₁ a₀ x θ (T.state v).rows Finset.univ
      Yevent R₀ activity ξ₀ hw hs (by omega) ha₀ hd hx
      (by simpa using hscale 0 (by omega)) hprofile
      (by simpa using hblocks 0 (by omega))
      (by intro j; simpa using hδscale 0 (by omega) j)
      hθ hθhalf (by simpa using hguard 0 (by omega))
      hException hnode
    simpa [k, κ, hκone, hfinal] using hres
  · obtain ⟨query, left, right, hnode⟩ :=
      (run_stop_or_depth (ordinaryLaw src).toFiniteLaw
        (referenceInput src) (Paper2.ReferenceSchedule.floor w x)
        0 r st hprefix v).resolve_left hfinal
    have hcostNode :
        (Protocol.bNode query left right).cost ≤ H₁+a := by
      have hc := hbudget
      rw [hnode] at hc
      omega
    have hcomputeNode : ∀ row ∈ (T.state v).rows, ∀ t ∈ Yevent,
        (Protocol.bNode query left right).eval row t =
          W src streams R₀ activity ξ₀ t row := by
      intro row hr t ht
      rw [← hnode]
      exact hcompute' v row hr t ht
    have hres := incoming_protected_mass_first_bob_lt src streams
      r κ H₁ a x θ (T.state v).rows Finset.univ
      Yevent R₀ activity ξ₀ query left right hw hs hκ ha hd hx
      (by simpa [a] using hscale k hk) hprofile
      (by simpa [a, κ] using hblocks k hk)
      (by intro j; simpa [a] using hδscale k hk j)
      hθ hYevent (by simpa [κ] using hguard k hk)
      hException hcomputeNode hcostNode
    simpa [k, κ] using hres

#print axioms indexed_incoming_each_initialised_node

/-- Distinct physical owners retain distinct original outer labels, so their
incoming receipts are a sub-sum of the all-origin receipt just bounded. -/
theorem indexed_incoming_owner_origins_le_all
    (R₀ : X → Y → Bool) (activity : I → Fin q₂ → Option (Fin s))
    (ξ₀ : Paper2.SourceMatrix.Tail s Y) (x : ℝ) (r : ℕ)
    (st : State (Fin w × Column src)
      (streams.metadataStream.Label ×
        (streams.baseStream.Label × streams.selectorStream.Label))
      (Fin w) (src.outer.Label × src.gamma.Label)) :
    let T := run (ordinaryLaw src).toFiniteLaw
      (referenceInput src) (Paper2.ReferenceSchedule.floor w x) 0 r st
    let F := fun u : T.Leaves => (T.state u).family
    let final := fun u : T.Leaves => (T.route u).length = r
    let O := ownerNodes F final
    ∀ v : T.Leaves,
      (∑ u : {u : T.Leaves // u ∈ O},
        protectedReceipt src w (T.state v).rows (origin F final u)) ≤
      ∑ i : Fin w, protectedReceipt src w (T.state v).rows i := by
  classical
  let T := run (ordinaryLaw src).toFiniteLaw
    (referenceInput src) (Paper2.ReferenceSchedule.floor w x) 0 r st
  let F := fun u : T.Leaves => (T.state u).family
  let final := fun u : T.Leaves => (T.route u).length = r
  let O := ownerNodes F final
  let Owners := {u : T.Leaves // u ∈ O}
  change ∀ v : T.Leaves,
    (∑ u : Owners,
      protectedReceipt src w (T.state v).rows (origin F final u)) ≤
    ∑ i : Fin w, protectedReceipt src w (T.state v).rows i
  intro v
  let f : Fin w → ℝ := protectedReceipt src w (T.state v).rows
  have hinj : Function.Injective (origin F final) :=
    indexed_owner_origins_injective src streams R₀ activity ξ₀ x r st
  let image : Finset (Fin w) :=
    (Finset.univ : Finset Owners).image (origin F final)
  have heq : (∑ u : Owners, f (origin F final u)) =
      ∑ i ∈ image, f i := by
    have hh := Finset.sum_image
      (s := (Finset.univ : Finset Owners))
      (g := origin F final) (f := f)
      (fun u _ u' _ heq => hinj heq)
    simpa [image] using hh.symm
  rw [heq]
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ image)
  intro i _ _
  dsimp [f, protectedReceipt]
  have hf := src.outer.law.toFiniteLaw.prob_nonneg
    (fun z => (i, Column.fixedTail z) ∈ (T.state v).rows)
  have hd := (diagonalLaw src).toFiniteLaw.prob_nonneg
    (fun z => (i, Column.diagonal z) ∈ (T.state v).rows)
  positivity

#print axioms indexed_incoming_owner_origins_le_all

end CurrentAdditive.DeterministicIndexedMatrix.Sources
