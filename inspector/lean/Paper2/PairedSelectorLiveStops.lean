import Paper2.PairedSupportFrontier
import Paper2.PairedSelectorMatrix
import Paper2.SourceSupportSchedule

/-!
# Live stops of the actual paired-selector protocol

Frozen v12 Section 5, `res:paired`, the scalar-profile exclusion of leaves
and of the last Bob-only depth. Both tagged supports follow their own
heavy paths. A surviving tagged coordinate and the unchanged joint selector
row set lower-bound the actual stopping protocol. No stopping or frontier
certificate is a premise, and empty counting states remain explicit.
-/

namespace Paper2.PairedSelectorLiveStops

open PairedSelectorMatrix PairedSupportFrontier Workspace.Types.Protocol

/-- A positive counting unit contains an actual tagged block, including
a foreign singleton created by separating a pair. This does not require
the no-overlap invariant needed for exact cardinality bookkeeping. -/
theorem blocks_nonempty_of_h_pos {A C I W : Type*}
    (s : PairedSupportFrontier.State A C I W) (hh : 0 < s.h) :
    s.blocks.Nonempty := by
  classical
  by_cases hs : 0 < s.singles.card
  · obtain ⟨a, ha⟩ := Finset.card_pos.mp hs
    exact ⟨a, (PairedSupportStep.mem_active s.singles s.pairs a).mpr (Or.inl ha)⟩
  · have hp : 0 < s.pairs.card := by
      simp only [State.h] at hh
      omega
    obtain ⟨i, hi⟩ := Finset.card_pos.mp hp
    exact ⟨(false, i),
      (PairedSupportStep.mem_active s.singles s.pairs (false, i)).mpr (Or.inr hi)⟩

variable {W J : Type*} [Fintype W] [Fintype J] {q : ℕ}

/-- Every generated stop with a positive counting unit is an actual
first-Alice node at depth at most `ell`, with at least `H` bits required.
The protocol keeps the original selector-pair row carrier throughout.
Validity of single/pair disjointness is not needed for this scalar bound;
the separate count and overload lemmas retain that hypothesis. -/
theorem run_live_stops
    (μ : PositiveRationalLaw W) (ν : PositiveRationalLaw J)
    (R : W → J → Bool) (H ell : ℕ) (hH : 2 ≤ H)
    (hq : q = 2 ^ ell) (x : ℝ) (hx : 0 ≤ x)
    (hprofile : RestrictionProfile R μ.toFiniteLaw ν.toFiniteLaw x (H : ℤ))
    (A : Set (Selector q J))
    (hA : (49 / 64 : ℝ) ≤ (selectorLaw ν q).toFiniteLaw.prob (· ∈ A))
    (initial : PairedSupportFrontier.State A (Column q W) (Fin q) W)
    (hP : ∀ a : A, ∀ c ∈ initial.columns,
      initial.protocol.eval a c = matrix R a.val c)
    (hcost : initial.protocol.cost ≤ H + ell)
    (hmass : ∀ b ∈ initial.blocks, SourceSupportSchedule.floor q x 0 ≤
      SourceSupportStep.mass μ.toFiniteLaw (initial.support b))
    (hreaches : ∀ b ∈ initial.blocks, ∀ w ∈ initial.support b,
      (b, w) ∈ initial.columns) :
    let T := PairedSupportFrontier.run μ.toFiniteLaw
      (fun b w => (b, w)) (ell + 1) initial
    ∀ v : T.Leaves, 0 < (T.state v).h →
      H ≤ (T.state v).protocol.cost ∧ (T.route v).length ≤ ell ∧
      ∃ query left right, (T.state v).protocol = Protocol.aNode query left right := by
  classical
  let input : Block q → W → Column q W := fun b w => (b, w)
  let floor := SourceSupportSchedule.floor q x
  let T := PairedSupportFrontier.run μ.toFiniteLaw input (ell + 1) initial
  change ∀ v : T.Leaves, 0 < (T.state v).h →
    H ≤ (T.state v).protocol.cost ∧ (T.route v).length ≤ ell ∧
    ∃ query left right, (T.state v).protocol = Protocol.aNode query left right
  intro v hv
  obtain ⟨b, hb⟩ := blocks_nonempty_of_h_pos (T.state v) hv
  have hp := PairedSupportFrontier.run_bobPath μ.toFiniteLaw input (ell + 1) initial v
  have hs := PairedSupportFrontier.run_stopping μ.toFiniteLaw input (ell + 1) initial v
  change (T.route v).length ≤ ell + 1 ∧
    ((T.route v).length = ell + 1 ∨ SourceSupportFrontier.NonBob (T.state v).protocol) at hs
  have hm := PairedSupportFrontier.run_mass_floors μ.toFiniteLaw input floor
    (fun r => (SourceSupportSchedule.twice_next q x r).symm)
    0 (ell + 1) initial hmass v
  have hr := PairedSupportFrontier.run_support_reaches μ.toFiniteLaw input
    (ell + 1) initial hreaches v
  have hfloor : x ≤ floor (T.route v).length := by
    have hf := SourceSupportSchedule.threshold_le_floor hx hs.1
    have he := congrArg (fun n => SourceSupportSchedule.floor n x (T.route v).length) hq
    exact hf.trans_eq he.symm
  have hw : x ≤ μ.toFiniteLaw.prob (fun w => w ∈ (T.state v).support b) := by
    have hmb := hm b hb
    simp only [zero_add] at hmb
    exact hfloor.trans hmb
  let P := Workspace.UpperBound.Protocol.comap id
    (fun c : (T.state v).columns => c.val) (T.state v).protocol
  have hPc : P.Computes (fun (a : A) (c : (T.state v).columns) =>
      matrix R a.val c.val) := by
    intro a c
    rw [Workspace.UpperBound.Protocol.comap_eval]
    exact (hp.eval_eq a c.val c.property).trans
      (hP a c.val (hp.columns_subset c.property))
  have hl := coordinate_lower μ ν R H x hprofile b A
    ((T.state v).support b : Set W) (T.state v).columns
    (fun w hw => hr b hb w hw) hw (by linarith)
  have hup : Compression.restrictionD (matrix R) A (T.state v).columns ≤ P.cost :=
    Nat.sInf_le ⟨P, rfl, hPc⟩
  have hlower : H ≤ (T.state v).protocol.cost := by
    have hh := hl.trans hup
    simpa only [P, Workspace.UpperBound.Protocol.comap_cost] using hh
  have hdepth : (T.route v).length ≤ ell := by
    have hc : (T.state v).protocol.cost + (T.route v).length ≤ initial.protocol.cost :=
      hp.cost_add_length
    omega
  have hnb : SourceSupportFrontier.NonBob (T.state v).protocol :=
    hs.2.resolve_left (by omega)
  refine ⟨hlower, hdepth, ?_⟩
  cases he : (T.state v).protocol with
  | leaf value =>
    simp only [he, Protocol.cost] at hlower
    omega
  | aNode query left right => exact ⟨query, left, right, rfl⟩
  | bNode query left right => simp only [he, SourceSupportFrontier.NonBob] at hnb

end Paper2.PairedSelectorLiveStops

#print axioms Paper2.PairedSelectorLiveStops.blocks_nonempty_of_h_pos
#print axioms Paper2.PairedSelectorLiveStops.run_live_stops
