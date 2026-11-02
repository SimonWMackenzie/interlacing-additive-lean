import CurrentAdditive.V39PairedTerminals
import CurrentAdditive.V39UnmarkedFrontier

/-! Scalar profile excludes premature leaves and the terminal Bob depth
on the actual tagged-support recursion. The selector-pair event remains
unchanged along every Bob-only path. -/

namespace CurrentAdditive.V39PairedLiveStops

open Paper2 Paper2.PairedSelectorMatrix Paper2.SourceSupportFrontier
open CurrentAdditive.DeterministicIndexedMatrix
open CurrentAdditive.DeterministicIndexedMatrix.Sources
open Workspace.Types.Protocol

variable {X Y I : Type*} [Fintype X] [Fintype Y] [Fintype I]
  [DecidableEq X] [DecidableEq Y]
  {D q₁ q₂ s : ℕ} [NeZero s] [NeZero q₁] [NeZero q₂]
  {μX : PositiveRationalLaw X} {μY : PositiveRationalLaw Y}
  (src : Sources (D := D) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY)

theorem paired_run_live_stops
    (R₀ : X → Y → Bool) (H ell : ℕ) (hH : 2 ≤ H)
    (hq : q₂ = 2 ^ ell) (x : ℝ) (hx : 0 ≤ x) (hD : 1 ≤ D)
    (hprofile : V38RestrictionProfiles.TwoThresholdProfile (A src R₀)
      src.gamma.law.toFiniteLaw
      ((PositiveRationalLaw.uniform (Fin q₁)).prod μX).toFiniteLaw
      x (H : ℤ))
    (K : Set (src.inner.Label × src.inner.Label))
    (hK : (49/64 : ℝ) ≤
      (src.inner.law.toFiniteLaw.prod src.inner.law.toFiniteLaw).prob (· ∈ K))
    (initial : State K (Paper2.PairedSelectorMatrix.Column q₂ src.gamma.Label)
      (Bool × Fin q₂) src.gamma.Label)
    (hP : ∀ z : K, ∀ c ∈ initial.columns,
      initial.protocol.eval z c = pairedIndexed src R₀ z.val
        (c.1.1, (c.1.2, c.2)))
    (hmarks : initial.attachments = ∅)
    (hcost : initial.protocol.cost ≤ H + ell)
    (hmass : ∀ b ∈ initial.coordinates, SourceSupportSchedule.floor q₂ x 0 ≤
      SourceSupportStep.mass src.gamma.law.toFiniteLaw (initial.support b))
    (hreaches : ∀ b ∈ initial.coordinates, ∀ γ ∈ initial.support b,
      (b, γ) ∈ initial.columns) :
    let T := run src.gamma.law.toFiniteLaw
      (fun b γ => (b, γ)) (SourceSupportSchedule.floor q₂ x) 0 (ell + 1) initial
    ∀ v : T.Leaves, (T.state v).coordinates.Nonempty →
      H ≤ (T.state v).protocol.cost ∧ (T.route v).length ≤ ell ∧
      ∃ query left right, (T.state v).protocol = Protocol.aNode query left right := by
  classical
  let input : Block q₂ → src.gamma.Label →
      Paper2.PairedSelectorMatrix.Column q₂ src.gamma.Label :=
    fun b γ => (b, γ)
  let floor := SourceSupportSchedule.floor q₂ x
  let T := run src.gamma.law.toFiniteLaw input floor 0 (ell + 1) initial
  change ∀ v : T.Leaves, (T.state v).coordinates.Nonempty →
    H ≤ (T.state v).protocol.cost ∧ (T.route v).length ≤ ell ∧
    ∃ query left right, (T.state v).protocol = Protocol.aNode query left right
  intro v hv
  obtain ⟨b, hb⟩ := hv
  have hp := run_bobPath src.gamma.law.toFiniteLaw input floor 0 (ell + 1) initial v
  have hs := run_stopping src.gamma.law.toFiniteLaw input floor 0 (ell + 1) initial v
  change (T.route v).length ≤ ell + 1 ∧
    ((T.route v).length = ell + 1 ∨
      SourceSupportFrontier.NonBob (T.state v).protocol) at hs
  have hm := run_mass_floors src.gamma.law.toFiniteLaw input floor
    (fun r => (SourceSupportSchedule.twice_next q₂ x r).symm)
    0 0 (ell + 1) initial hmass (by simp [hmarks]) v
  have hr := run_support_reaches src.gamma.law.toFiniteLaw input floor
    0 (ell + 1) initial hreaches v
  have hfloor : x ≤ floor (T.route v).length := by
    have hf := SourceSupportSchedule.threshold_le_floor hx hs.1
    have he := congrArg (fun n => SourceSupportSchedule.floor n x (T.route v).length) hq
    exact hf.trans_eq he.symm
  have hγ : x ≤ src.gamma.law.toFiniteLaw.prob
      (fun γ => γ ∈ (T.state v).support b) := by
    have hmb := hm.1 b hb
    simp only [zero_add] at hmb
    exact hfloor.trans hmb
  let P := Workspace.UpperBound.Protocol.comap id
    (fun c : (T.state v).columns => c.val) (T.state v).protocol
  have hPc : P.Computes (fun (z : K) (c : (T.state v).columns) =>
      pairedIndexed src R₀ z.val (c.val.1.1, (c.val.1.2, c.val.2))) := by
    intro z c
    rw [Workspace.UpperBound.Protocol.comap_eval]
    exact (hp.eval_eq z c.val c.property).trans
      (hP z c.val (hp.columns_subset c.property))
  have hl := V39PairedTerminals.paired_coordinate_cost src R₀ H x hD hprofile b K
    ((T.state v).support b : Set src.gamma.Label) (T.state v).columns
    (fun γ hγ => hr b hb γ hγ) hK hγ
  have hup : Compression.restrictionD
      (fun z c => pairedIndexed src R₀ z (c.1.1, (c.1.2, c.2)))
      K (T.state v).columns ≤ P.cost :=
    Nat.sInf_le ⟨P, rfl, hPc⟩
  have hlower : H ≤ (T.state v).protocol.cost := by
    have hh := hl.trans hup
    simpa only [P, Workspace.UpperBound.Protocol.comap_cost] using hh
  have hdepth : (T.route v).length ≤ ell := by
    have hc : (T.state v).protocol.cost + (T.route v).length ≤
        initial.protocol.cost := hp.cost_add_length
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

end CurrentAdditive.V39PairedLiveStops

#print axioms CurrentAdditive.V39PairedLiveStops.paired_run_live_stops
