import CurrentAdditive.GeneratedTwoStreamOrdinaryNode
import CurrentAdditive.DeterministicIndexedHeadMarginals
import Paper2.TwoStreamLiveStops

/-! Live-stop exclusion from one genuine ordinary source coordinate. -/

namespace CurrentAdditive.DeterministicIndexedMatrix.Sources

open Paper2 Paper2.ProjectedSupportFrontier
open Workspace.Types.Protocol

variable {X Y Raw A C : Type*}
  [Fintype X] [Fintype Y] [Fintype Raw]
  [DecidableEq X] [DecidableEq Y]
  {D q₁ q₂ s : ℕ} [NeZero s] [NeZero q₁] [NeZero q₂]
  {μX : PositiveRationalLaw X} {μY : PositiveRationalLaw Y}
  (src : Sources (D := D) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY)

/-- One ordinary physical-bin coordinate has exactly the prescribed
`J₂` law, although the complete ordinary decoded vector need not be iid. -/
theorem ordinary_coordinate_pushes (hD : 1 ≤ D) (i : Fin s) :
    (ordinaryLaw src).toFiniteLaw.PushesTo
      ((PositiveRationalLaw.uniform (Fin q₂)).prod src.gamma.law).toFiniteLaw
      (fun c => src.outer.decode c.1 i) := by
  intro E
  exact (ordinary_first_marginal src
    (fun js => E (src.outer.decode js i))).trans
    (outer_position_pushes src hD i E)

/-- A nonempty stop of the row-prefix walk is the first ordinary-column
query, and it occurs before exhaustion. Only one-coordinate exactness is
used; no full-word iid property is imported. -/
theorem generated_run_live_stops
    (R₀ : X → Y → Bool) (H a : ℕ) (hH : 1 ≤ H)
    (hs : s = 2^a) (x : ℝ) (hx : 0 ≤ x) (hD : 1 ≤ D)
    (hprofile : RestrictionProfile (T src R₀)
      src.inner.law.toFiniteLaw
      ((PositiveRationalLaw.uniform (Fin q₂)).prod src.gamma.law).toFiniteLaw
      x (H : ℤ))
    (O : Set (src.outer.Label × src.gamma.Label))
    (hO : (3/5 : ℝ) ≤ (ordinaryLaw src).toFiniteLaw.prob (· ∈ O))
    (σ : Fin s → Raw → src.inner.Label)
    (input : Fin s → Raw → C)
    (col : (src.outer.Label × src.gamma.Label) → A)
    (initial : State A C (Fin s) Raw)
    (hP : ∀ i ∈ initial.coordinates, ∀ w ∈ initial.support i,
      ∀ c ∈ O, initial.protocol.eval (col c) (input i w) =
        T src R₀ (σ i w) (src.outer.decode c.1 i))
    (hcost : initial.protocol.cost ≤ H+a)
    (hmass : ∀ i ∈ initial.coordinates,
      SourceSupportSchedule.floor s x 0 ≤
        ProjectedSupportStep.mass src.inner.law.toFiniteLaw (σ i)
          (initial.support i))
    (hreaches : ∀ i ∈ initial.coordinates, ∀ w ∈ initial.support i,
      input i w ∈ initial.columns) :
    let K := runScheduled src.inner.law.toFiniteLaw σ input
      (SourceSupportSchedule.floor s x) 0 (a+1) initial
    ∀ v : K.Leaves, (K.state v).coordinates.Nonempty →
      H ≤ (K.state v).protocol.cost ∧ (K.route v).length ≤ a ∧
      ∃ query left right,
        (K.state v).protocol = Protocol.aNode query left right := by
  classical
  let floor := SourceSupportSchedule.floor s x
  let K := runScheduled src.inner.law.toFiniteLaw σ input floor 0 (a+1) initial
  change ∀ v : K.Leaves, (K.state v).coordinates.Nonempty →
    H ≤ (K.state v).protocol.cost ∧ (K.route v).length ≤ a ∧
    ∃ query left right,
      (K.state v).protocol = Protocol.aNode query left right
  intro v hv
  obtain ⟨i, hi⟩ := hv
  have hp := runScheduled_bobPath src.inner.law.toFiniteLaw σ input floor 0 (a+1) initial v
  have hstop := runScheduled_stopping src.inner.law.toFiniteLaw σ input floor 0 (a+1) initial v
  change (K.route v).length ≤ a+1 ∧
    ((K.route v).length = a+1 ∨ SourceSupportFrontier.NonBob (K.state v).protocol) at hstop
  have hm := runScheduled_floor src.inner.law.toFiniteLaw σ input floor
    (fun r => (SourceSupportSchedule.twice_next s x r).symm)
    0 (a+1) initial hmass v
  have hr := runScheduled_support_reaches src.inner.law.toFiniteLaw σ input floor 0 (a+1)
    initial hreaches v
  have hsets := runScheduled_sets_subset src.inner.law.toFiniteLaw σ input floor 0 (a+1)
    initial v
  have hfloor : x ≤ floor (K.route v).length := by
    have hf := SourceSupportSchedule.threshold_le_floor hx hstop.1
    simpa only [floor, hs] using hf
  have hrow : x ≤ ProjectedSupportStep.mass src.inner.law.toFiniteLaw
      (σ i) ((K.state v).support i) := by
    exact hfloor.trans (by simpa only [zero_add] using hm i hi)
  have hlower : H ≤ (K.state v).protocol.cost := by
    apply TwoStreamScalarCost.one_bin_cost src.inner.law.toFiniteLaw
      ((PositiveRationalLaw.uniform (Fin q₂)).prod src.gamma.law).toFiniteLaw
      (ordinaryLaw src).toFiniteLaw (T src R₀) H x hprofile (σ i)
      (fun c => src.outer.decode c.1 i)
      (ordinary_coordinate_pushes src hD i)
      ((K.state v).support i) O hrow hO (input i) col
      (K.state v).protocol
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

#print axioms ordinary_coordinate_pushes
#print axioms generated_run_live_stops

end CurrentAdditive.DeterministicIndexedMatrix.Sources
