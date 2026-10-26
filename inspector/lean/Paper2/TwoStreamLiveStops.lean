import Paper2.TwoStreamScalarCost
import Paper2.ProjectedSupportFrontierScheduled
import Paper2.SourceSupportSchedule

/-!
# Live stops of the projection-aware outer-bin walk

Frozen v12, Section 5, `res:two-stream`. The walk is on the transposed
original protocol: Bob queries here are original row queries. Ordinary
columns remain unchanged throughout. The scalar restriction profile of
`T` excludes active leaves and exhaustion at depth `a+1`.
-/

namespace Paper2.TwoStreamLiveStops

open Workspace.Types.Protocol ProjectedSupportFrontier

variable {S J W Ω A C : Type*} [Fintype S] [Fintype J]
  [Fintype W] [Fintype Ω] {s : ℕ}

/-- Every nonempty stop is the first original column-player node on its
physical path, at depth at most `a`. The input maps and exact values are
the original ones; the tree and support floors are generated here. -/
theorem run_live_stops (μ : FiniteLaw S) (ν : FiniteLaw J) (κ : FiniteLaw Ω)
    (T : S → J → Bool) (H a : ℕ) (hH : 1 ≤ H) (hs : s = 2 ^ a)
    (x : ℝ) (hx : 0 ≤ x) (hprofile : RestrictionProfile T μ ν x (H : ℤ))
    (Φ : Ω → Fin s → J) (hΦ : κ.PushesTo (ν.iid s) Φ)
    (O : Set Ω) (hO : (3 / 5 : ℝ) ≤ κ.prob (· ∈ O))
    (σ : Fin s → W → S) (input : Fin s → W → C) (col : Ω → A)
    (initial : State A C (Fin s) W)
    (hP : ∀ i ∈ initial.coordinates, ∀ w ∈ initial.support i, ∀ c ∈ O,
      initial.protocol.eval (col c) (input i w) = T (σ i w) (Φ c i))
    (hcost : initial.protocol.cost ≤ H + a)
    (hmass : ∀ i ∈ initial.coordinates, SourceSupportSchedule.floor s x 0 ≤
      ProjectedSupportStep.mass μ (σ i) (initial.support i))
    (hreaches : ∀ i ∈ initial.coordinates, ∀ w ∈ initial.support i,
      input i w ∈ initial.columns) :
    let K := runScheduled μ σ input (SourceSupportSchedule.floor s x) 0 (a + 1) initial
    ∀ v : K.Leaves, (K.state v).coordinates.Nonempty →
      H ≤ (K.state v).protocol.cost ∧ (K.route v).length ≤ a ∧
      ∃ query left right, (K.state v).protocol = Protocol.aNode query left right := by
  classical
  let floor := SourceSupportSchedule.floor s x
  let K := runScheduled μ σ input floor 0 (a + 1) initial
  change ∀ v : K.Leaves, (K.state v).coordinates.Nonempty →
    H ≤ (K.state v).protocol.cost ∧ (K.route v).length ≤ a ∧
    ∃ query left right, (K.state v).protocol = Protocol.aNode query left right
  intro v hv
  obtain ⟨i, hi⟩ := hv
  have hp := runScheduled_bobPath μ σ input floor 0 (a + 1) initial v
  have hstop := runScheduled_stopping μ σ input floor 0 (a + 1) initial v
  change (K.route v).length ≤ a + 1 ∧
    ((K.route v).length = a + 1 ∨ SourceSupportFrontier.NonBob (K.state v).protocol) at hstop
  have hm := runScheduled_floor μ σ input floor
    (fun r => (SourceSupportSchedule.twice_next s x r).symm)
    0 (a + 1) initial hmass v
  have hr := runScheduled_support_reaches μ σ input floor 0 (a + 1)
    initial hreaches v
  have hsets := runScheduled_sets_subset μ σ input floor 0 (a + 1) initial v
  have hfloor : x ≤ floor (K.route v).length := by
    have hf := SourceSupportSchedule.threshold_le_floor hx hstop.1
    simpa only [floor, hs] using hf
  have hrow : x ≤ ProjectedSupportStep.mass μ (σ i) ((K.state v).support i) := by
    have hmi := hm i hi
    simp only [zero_add] at hmi
    exact hfloor.trans hmi
  have hlower : H ≤ (K.state v).protocol.cost := by
    apply TwoStreamScalarCost.one_bin_cost μ ν κ T H x hprofile (σ i)
      (fun c => Φ c i) (TwoStreamScalarCost.coordinate_pushes ν κ s Φ hΦ i)
      ((K.state v).support i) O hrow hO (input i) col (K.state v).protocol
    intro w hw c hc
    have hreach := hr i hi w hw
    exact (hp.eval_eq (col c) (input i w) hreach).trans
      (hP i (hsets.1 hi) w (hsets.2.2 i hw) c hc)
  have hdepth : (K.route v).length ≤ a := by
    have hbudget := hp.cost_add_length
    change (K.state v).protocol.cost + (K.route v).length ≤ initial.protocol.cost at hbudget
    omega
  have hnb : SourceSupportFrontier.NonBob (K.state v).protocol :=
    hstop.2.resolve_left (by omega)
  refine ⟨hlower, hdepth, ?_⟩
  cases he : (K.state v).protocol with
  | leaf value =>
    simp only [he, Protocol.cost] at hlower
    omega
  | aNode query left right => exact ⟨query, left, right, rfl⟩
  | bNode query left right =>
    simp only [he, SourceSupportFrontier.NonBob] at hnb

end Paper2.TwoStreamLiveStops

#print axioms Paper2.TwoStreamLiveStops.run_live_stops
