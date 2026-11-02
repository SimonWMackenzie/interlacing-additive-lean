import CurrentAdditive.V39TwoStreamTerminals
import Paper2.TwoStreamRetention
import Paper2.TwoStreamInitial

set_option maxHeartbeats 5000000

/-! The row-prefix frontier for the actual generated two-stream source. -/

namespace CurrentAdditive.V39TwoStreamConversation

open Paper2 Paper2.PairedSelectorMatrix Paper2.PairedSelectorPopulation
open Paper2.ProjectedSupportFrontier Paper2.SourceSupportFrontier
open Workspace.Types.Protocol
open CurrentAdditive.DeterministicIndexedMatrix
open CurrentAdditive.DeterministicIndexedMatrix.Sources
open CurrentAdditive.V39TwoStreamTerminals

variable {X Y Rw Raw F : Type*}
  [Fintype X] [Fintype Y] [Fintype Rw] [Nonempty Rw]
  [Fintype Raw] [DecidableEq Raw] [Fintype F]
  [DecidableEq X] [DecidableEq Y]
  {D q₁ q₂ s : ℕ} [NeZero s] [NeZero q₁] [NeZero q₂]
  {μX : PositiveRationalLaw X} {μY : PositiveRationalLaw Y}
  (src : Sources (D := D) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY)

/-- The original two-stream protocol cannot fit the sum of the generated
indexed inner and outer costs. The retained pair map is measured in the
original complete-label product law, while ordinary bins use only exact
bounded-wise marginals. -/
theorem no_short_generated_two_stream
    (R₀ : X → Y → Bool)
    (M : Rw → ((src.outer.Label × src.gamma.Label) ⊕ F) → Bool)
    (H ell a : ℕ) (hH : 2 ≤ H) (hq : q₂ = 2^ell) (hs : s = 2^a)
    (x : ℝ) (hx : 0 < x) (hD : 8 ≤ D)
    (hA : V38RestrictionProfiles.TwoThresholdProfile (A src R₀)
      src.gamma.law.toFiniteLaw
      ((PositiveRationalLaw.uniform (Fin q₁)).prod μX).toFiniteLaw
      x (H : ℤ))
    (hT : V38RestrictionProfiles.TwoThresholdProfile (T src R₀)
      src.inner.law.toFiniteLaw
      ((PositiveRationalLaw.uniform (Fin q₂)).prod src.gamma.law).toFiniteLaw
      x ((H+ell : ℕ) : ℤ))
    (κRaw : FiniteLaw Raw)
    (bin : Rw → Fin s) (selector : Rw → src.inner.Label)
    (ψ : F → J src)
    (hordinary : ∀ row c, M row (.inl c) =
      T src R₀ (selector row) (src.outer.decode c.1 (bin row)))
    (ζ : Raw → src.inner.Label × src.inner.Label)
    (hζ : κRaw.PushesTo
      (src.inner.law.toFiniteLaw.prod src.inner.law.toFiniteLaw) ζ)
    (σ : Raw → src.inner.Label) (hfirst : σ = fun w => (ζ w).1)
    (input : Raw → Rw) (star : Fin s)
    (initial : ProjectedSupportFrontier.State
      ((src.outer.Label × src.gamma.Label) ⊕ F) Rw (Fin s) Raw)
    (hQ : initial.coordinates = Finset.univ)
    (hZ : initial.attachments = {star})
    (hbin : ∀ i ∈ initial.coordinates, ∀ w ∈ initial.support i,
      bin (input w) = i)
    (hsel : ∀ i ∈ initial.coordinates, ∀ w ∈ initial.support i,
      σ w = selector (input w))
    (hreaches : ∀ i ∈ initial.coordinates, ∀ w ∈ initial.support i,
      input w ∈ initial.columns)
    (hmass : ∀ i ∈ initial.coordinates,
      SourceSupportSchedule.floor s x 0 ≤
        ProjectedSupportStep.mass src.inner.law.toFiniteLaw σ
          (initial.support i))
    (O : Set (src.outer.Label × src.gamma.Label)) (G : Set F)
    (hvalue : ∀ row ∈ initial.columns,
      ∀ c ∈ TwoStreamInitial.retainedColumns O G,
      initial.protocol.eval c row = M row c)
    (hforeign : ∀ w ∈ initial.support star, ∀ f,
      M (input w) (.inr f) = T src R₀ (ζ w).2 (ψ f))
    (hretain : ∀ P' : Finset Raw, P' ⊆ initial.support star →
      SourceSupportStep.mass κRaw (initial.support star \ P') <
        SourceSupportSchedule.floor s x 0 →
      (49/64 : ℝ) ≤
        (src.inner.law.toFiniteLaw.prod src.inner.law.toFiniteLaw).prob
          (· ∈ ζ '' (P' : Set Raw)))
    (ε δ : ℝ)
    (hO : 1-ε ≤ (ordinaryLaw src).toFiniteLaw.prob (· ∈ O))
    (hF : δ ≤
      (Paper2.PairedSelectorPopulation.columnLaw src.gamma.law).toFiniteLaw.prob
        (· ∈ ψ '' G))
    (hδ : δ ≤ 1)
    (hslack : 2*q₂*x+4*ε < δ)
    (hsmall : SourceSupportSchedule.floor s x 0 ≤ 1/8)
    (hpairsmall : 2*q₂*x ≤ 1/8)
    (hcost : initial.protocol.cost ≤ H+ell+a) : False := by
  classical
  let μS := src.inner.law.toFiniteLaw
  let νJ := ((PositiveRationalLaw.uniform (Fin q₂)).prod src.gamma.law).toFiniteLaw
  let κΩ := (ordinaryLaw src).toFiniteLaw
  let σBins : Fin s → Raw → src.inner.Label := fun _ => σ
  let inputBins : Fin s → Raw → Rw := fun _ => input
  let floor := SourceSupportSchedule.floor s x
  let K := runScheduled μS σBins inputBins floor 0 (a+1) initial
  have hqpos : 0 < q₂ := NeZero.pos q₂
  have hspos : 0 < s := by rw [hs]; positivity
  obtain ⟨hε, _, hdense⟩ := V39TwoStreamTerminals.ordinary_density κΩ O q₂
    x ε δ hx.le hO hδ hslack
  have hinitval : ∀ i ∈ initial.coordinates,
      ∀ w ∈ initial.support i, ∀ c ∈ O,
      initial.protocol.eval (.inl c) (inputBins i w) =
        T src R₀ (σBins i w) (src.outer.decode c.1 i) := by
    intro i hi w hw c hc
    rw [hvalue (input w) (hreaches i hi w hw) (.inl c)
      ((TwoStreamInitial.inl_mem O G c).mpr hc), hordinary,
      hbin i hi w hw, ← hsel i hi w hw]
  have hlive := V39TwoStreamTerminals.generated_run_live_stops src R₀ (H+ell) a
    (by omega) hs x hx.le (by omega) hT O (by linarith)
    σBins inputBins Sum.inl initial hinitval hcost hmass hreaches
  have hZsubset : initial.attachments ⊆ initial.coordinates := by
    simp [hZ, hQ]
  have hcount : initial.coordinates.card + 0 = s := by simp [hQ]
  obtain ⟨v, hbig, hover⟩ := runScheduled_active_overload μS σBins
    inputBins floor 0 (a+1) initial hZsubset s 0 hcount
    (by simp [hZ])
  have hpath := runScheduled_bobPath μS σBins inputBins floor 0 (a+1) initial v.val
  have hsets := runScheduled_sets_subset μS σBins inputBins floor 0 (a+1) initial v.val
  have hreach := runScheduled_support_reaches μS σBins inputBins floor 0 (a+1)
    initial hreaches v.val
  have hfloors := runScheduled_floor μS σBins inputBins floor
    (fun d => (SourceSupportSchedule.twice_next s x d).symm)
    0 (a+1) initial hmass v.val
  obtain ⟨_, hdepth, hAlice⟩ := hlive v.val v.property
  let node := K.state v.val
  let r := (K.route v.val).length
  change r ≤ a at hdepth
  change (s : ℝ)/(2 : ℝ)^r <
    (node.coordinates.card : ℝ)+(node.attachments.card : ℝ) at hover
  change (3*((s : ℝ)/(2 : ℝ)^r))/4 ≤
    (node.coordinates.card : ℝ) at hbig
  have hbinNode : ∀ i ∈ node.coordinates, ∀ w ∈ node.support i,
      bin (input w) = i := by
    intro i hi w hw
    exact hbin i (hsets.1 hi) w (hsets.2.2 i hw)
  have hselNode : ∀ i ∈ node.coordinates, ∀ w ∈ node.support i,
      σ w = selector (input w) := by
    intro i hi w hw
    exact hsel i (hsets.1 hi) w (hsets.2.2 i hw)
  have hvalueNode : ∀ i ∈ node.coordinates, ∀ w ∈ node.support i,
      ∀ c ∈ O, node.protocol.eval (.inl c) (input w) =
        M (input w) (.inl c) := by
    intro i hi w hw c hc
    exact (hpath.eval_eq (.inl c) (input w) (hreach i hi w hw)).trans
      (hvalue (input w) (hpath.columns_subset (hreach i hi w hw))
        (.inl c) ((TwoStreamInitial.inl_mem O G c).mpr hc))
  have hcostNode : node.protocol.cost ≤ H+ell+(a-r) := by
    have hc := hpath.cost_add_length
    change node.protocol.cost+r ≤ initial.protocol.cost at hc
    omega
  obtain ⟨query, left, right, hAliceEq⟩ := hAlice
  have hremain := V39TwoStreamTerminals.ordinary_node_forces_one src R₀ M bin selector hordinary
    input σ node.coordinates node.support hselNode hbinNode O hdense
    (H+ell) a r hdepth (by omega) x hx hD hs hsmall hT
    (by simpa only [zero_add] using hfloors)
    (by convert hbig using 1 <;> ring) query left right
    (by simpa only [← hAliceEq] using hvalueNode)
    (by simpa only [← hAliceEq] using hcostNode)
  obtain ⟨hkzero, hone⟩ := hremain
  have hrEq : r=a := by omega
  have hZnode : node.attachments ⊆ node.coordinates :=
    runScheduled_attachments_subset μS σBins inputBins floor 0 (a+1)
      initial hZsubset v.val
  have hoverOne : (1 : ℝ) < (node.coordinates.card : ℝ)+
      (node.attachments.card : ℝ) := by
    have hc := SourceRemainingConversationNumerics.capacity_eq_pow hs hdepth
    rw [hc, hrEq] at hover
    simpa [hone] using hover
  have hattachPos : 0 < node.attachments.card := by
    have : (0 : ℝ) < node.attachments.card := by
      rw [hone] at hoverOne
      norm_num only [Nat.cast_one] at hoverOne
      linarith
    exact_mod_cast this
  have hstarNode : star ∈ node.attachments := by
    obtain ⟨i, hi⟩ := Finset.card_pos.mp hattachPos
    have hsingle : i ∈ ({star} : Finset (Fin s)) := by
      rw [← hZ]
      exact hsets.2.1 hi
    have heq : i=star := Finset.mem_singleton.mp hsingle
    exact heq ▸ hi
  have hstarQ : star ∈ node.coordinates := hZnode hstarNode
  have hpairmass := TwoStreamRetention.retained_pair_mass κRaw μS ζ hζ
    σBins star (by simpa [σBins] using hfirst)
    inputBins floor (fun d => (SourceSupportSchedule.twice_next s x d).symm)
    (SourceSupportSchedule.floor_pos hspos hx) (a+1) initial hZ
    hretain v.val hstarNode
  let P : Set Raw := (node.support star : Set Raw)
  let Rnode : Set Rw := TwoStreamConversation.nodeRows
    node.coordinates node.support input
  have hpairRow : ∀ w ∈ P, input w ∈ Rnode := by
    intro w hw
    exact TwoStreamConversation.nodeRows_mem
      node.coordinates node.support input hstarQ hw
  have hpairStar : ∀ w ∈ P,
      bin (input w) = star ∧ selector (input w) = (ζ w).1 := by
    intro w hw
    refine ⟨hbinNode star hstarQ w hw, ?_⟩
    rw [← hselNode star hstarQ w hw, hfirst]
  have hpairForeign : ∀ w ∈ P, ∀ f,
      M (input w) (.inr f) = T src R₀ (ζ w).2 (ψ f) := by
    intro w hw f
    exact hforeign w (hsets.2.2 star hw) f
  have hOprojected : 1-ε ≤
      (Paper2.PairedSelectorPopulation.columnLaw src.gamma.law).toFiniteLaw.prob
        (· ∈ (fun c => src.outer.decode c.1 star) '' O) := by
    exact hO.trans (FiniteLaw.prob_le_image κΩ νJ
      (fun c => src.outer.decode c.1 star)
      (ordinary_coordinate_pushes src (by omega) star) O)
  have hδpos : 0 < δ := by
    have ht : 0 ≤ 2*(q₂ : ℝ)*x := by positivity
    linarith
  have hpairedSlack : 2*q₂*x+ε < δ := by linarith
  have hpairedLower := V39TwoStreamTerminals.paired_original_parent_lower src R₀ M bin selector
    ψ star input ζ hordinary P Rnode O G hpairStar hpairForeign
    hpairRow H ell hH hq x hx hD hA ε δ
    (by simpa only [μS] using hpairmass)
    hOprojected hF hδpos hδ hpairsmall hε hpairedSlack
  let Qp := Workspace.UpperBound.Protocol.comap
    (fun row : Rnode => row.val)
    (fun c : TwoStreamInitial.retainedColumns O G => c.val)
    (Workspace.UpperBound.Protocol.transpose node.protocol)
  have hQp : Qp.Computes (fun (row : Rnode)
      (c : TwoStreamInitial.retainedColumns O G) => M row.val c.val) := by
    intro row c
    rw [Workspace.UpperBound.Protocol.comap_eval,
      Workspace.UpperBound.Protocol.transpose_eval]
    rcases row.property with ⟨i, hi, w, hw, hwr⟩
    change node.protocol.eval c.val row.val = M row.val c.val
    rw [← hwr]
    exact (hpath.eval_eq c.val (input w) (hreach i hi w hw)).trans
      (hvalue (input w) (hpath.columns_subset (hreach i hi w hw))
        c.val c.property)
  have hparentUpper : Compression.restrictionD M Rnode
      (TwoStreamInitial.retainedColumns O G) ≤ node.protocol.cost := by
    have hh : Compression.restrictionD M Rnode
        (TwoStreamInitial.retainedColumns O G) ≤ Qp.cost :=
      Nat.sInf_le ⟨Qp, rfl, hQp⟩
    simpa only [Qp, Workspace.UpperBound.Protocol.comap_cost,
      Workspace.UpperBound.Protocol.transpose_cost] using hh
  have hparentCost : node.protocol.cost ≤ H+ell := by omega
  have hC : TwoStreamInitial.retainedColumns O G =
      (Sum.inl '' O) ∪ (Sum.inr '' G) := rfl
  rw [← hC] at hpairedLower
  omega

#print axioms no_short_generated_two_stream

end CurrentAdditive.V39TwoStreamConversation
