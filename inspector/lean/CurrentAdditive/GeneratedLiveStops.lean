import CurrentAdditive.GeneratedStopping
import Paper2.SourceSupportLiveStops

/-!
The genuine Bob-only recursion cannot stop at a leaf or run one level too
deep while retaining an indexed diagonal support. Its row carrier is the
actual retained generated matrix; the gamma source law remains on labels.
-/

namespace CurrentAdditive.DeterministicIndexedMatrix.Sources

open Paper2 Paper2.SourceMatrix Paper2.SourceSupportFrontier
open Workspace.Types.Protocol

variable {X Y I : Type*} [Fintype X] [Fintype Y] [Fintype I]
  [DecidableEq X] [DecidableEq Y]
  {D q₁ q₂ s : ℕ} [NeZero s] [NeZero q₁] [NeZero q₂]
  {μX : PositiveRationalLaw X} {μY : PositiveRationalLaw Y}
  (src : Sources (D := D) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY)

theorem indexed_run_live_stops
    (hD : 8 ≤ D) (R : X → Y → Bool)
    (activity : I → Fin q₂ → Option (Fin s)) (ξ₀ : Tail s Y)
    (H ell : ℕ) (hH : 0 < H) (hq : q₂ = 2 ^ ell) (x : ℝ) (hx : 0 ≤ x)
    (hprofile : RestrictionProfile (A src R)
      src.gamma.law.toFiniteLaw
      ((PositiveRationalLaw.uniform (Fin q₁)).prod μX).toFiniteLaw
      x (H : ℤ))
    (p : Fin s) (K : Set src.inner.Label)
    (V : Set (Row (I := I) src))
    (hK : ∀ z ∈ K, Sum.inl (p, z) ∈ V)
    (hKmass : (3/5 : ℝ) ≤ src.inner.law.toFiniteLaw.prob (· ∈ K))
    (initial : State V (Column src) (Fin q₂) src.gamma.Label)
    (hP : ∀ v : V, ∀ z ∈ initial.columns,
      initial.protocol.eval v z = N src R activity ξ₀ z v.val)
    (hcost : initial.protocol.cost ≤ H + ell)
    (hZ : initial.attachments ⊆ initial.coordinates)
    (hmass : ∀ α ∈ initial.coordinates,
      Paper2.SourceSupportSchedule.floor q₂ x 0 ≤
      Paper2.SourceSupportStep.mass src.gamma.law.toFiniteLaw (initial.support α))
    (hreaches : ∀ α ∈ initial.coordinates, ∀ γ ∈ initial.support α,
      Column.diagonal (α, γ) ∈ initial.columns) :
    let T := run src.gamma.law.toFiniteLaw
      (fun α γ => Column.diagonal (α, γ))
      (Paper2.SourceSupportSchedule.floor q₂ x) 0 (ell + 1) initial
    ∀ v : T.Leaves, (T.state v).coordinates.Nonempty →
      H ≤ (T.state v).protocol.cost ∧ (T.route v).length ≤ ell ∧
      ∃ query left right, (T.state v).protocol = Protocol.aNode query left right := by
  classical
  let law := src.gamma.law.toFiniteLaw
  let input : Fin q₂ → src.gamma.Label → Column src :=
    fun α γ => Column.diagonal (α, γ)
  let floor := Paper2.SourceSupportSchedule.floor q₂ x
  let T := run law input floor 0 (ell + 1) initial
  change ∀ v : T.Leaves, (T.state v).coordinates.Nonempty →
    H ≤ (T.state v).protocol.cost ∧ (T.route v).length ≤ ell ∧
    ∃ query left right, (T.state v).protocol = Protocol.aNode query left right
  intro v hv
  obtain ⟨α, hα⟩ := hv
  have hp := run_bobPath law input floor 0 (ell + 1) initial v
  have hs := run_stopping law input floor 0 (ell + 1) initial v
  change (T.route v).length ≤ ell + 1 ∧
    ((T.route v).length = ell + 1 ∨ NonBob (T.state v).protocol) at hs
  have hm := run_mass_floors law input floor
    (fun r => (Paper2.SourceSupportSchedule.twice_next q₂ x r).symm) 0
    0 (ell + 1) initial hmass
    (fun i hi => by simpa only [zero_add] using hmass i (hZ hi)) v
  have hr := run_support_reaches law input floor 0 (ell + 1) initial hreaches v
  have hfloor : x ≤ floor (T.route v).length := by
    have hf := Paper2.SourceSupportSchedule.threshold_le_floor hx hs.1
    have he := congrArg (fun q =>
      Paper2.SourceSupportSchedule.floor q x (T.route v).length) hq
    exact hf.trans_eq he.symm
  have hw : x ≤ law.prob (fun γ => γ ∈ (T.state v).support α) := by
    have hmα := hm.1 α hα
    simp only [zero_add] at hmα
    exact hfloor.trans hmα
  let P := Workspace.UpperBound.Protocol.comap id
    (fun z : (T.state v).columns => z.val) (T.state v).protocol
  have hPc : P.Computes (fun (row : V) (z : (T.state v).columns) =>
      N src R activity ξ₀ z.val row.val) := by
    intro row z
    rw [Workspace.UpperBound.Protocol.comap_eval]
    exact (hp.eval_eq row z.val z.property).trans
      (hP row z.val (hp.columns_subset z.property))
  have hl := indexed_coordinate_cost src hD R activity ξ₀ H x hprofile
    p α K ((T.state v).support α : Set _) (T.state v).columns V
    hK (fun γ hγ => hr α hα γ hγ) hKmass hw
  have hup : Workspace.Types.CommComplexity.D
      (fun (row : V) (z : (T.state v).columns) =>
        N src R activity ξ₀ z.val row.val) ≤ P.cost :=
    Nat.sInf_le ⟨P, rfl, hPc⟩
  have he := Paper2.SourceProjection.restrictionD_transpose
    (N src R activity ξ₀) (T.state v).columns V
  have hlower : H ≤ (T.state v).protocol.cost := by
    have hpp : H ≤ P.cost := hl.trans (he ▸ hup)
    simpa only [P, Workspace.UpperBound.Protocol.comap_cost] using hpp
  have hdepth : (T.route v).length ≤ ell := by
    have hb : (T.state v).protocol.cost + (T.route v).length ≤
        initial.protocol.cost := hp.cost_add_length
    omega
  have hnb : NonBob (T.state v).protocol := hs.2.resolve_left (by omega)
  refine ⟨hlower, hdepth, ?_⟩
  cases he : (T.state v).protocol with
  | leaf value =>
    simp only [he, Protocol.cost] at hlower
    omega
  | aNode query left right => exact ⟨query, left, right, rfl⟩
  | bNode query left right => simp only [he, NonBob] at hnb

end CurrentAdditive.DeterministicIndexedMatrix.Sources

#print axioms CurrentAdditive.DeterministicIndexedMatrix.Sources.indexed_run_live_stops
