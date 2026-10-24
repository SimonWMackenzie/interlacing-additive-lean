import Paper2.TwoStreamLiveStops
import Paper2.TwoStreamColumnStep
import Paper2.TwoStreamOrdinaryCapacity
import Paper2.SourceRemainingConversationNumerics
import Paper2.TwoStreamRetention
import Paper2.TwoStreamPairedLocal
import Paper2.TwoStreamInitial

set_option maxHeartbeats 5000000

/-!
# The remaining ordinary conversation at a generated two-stream node

The raw supports are still sets of original row labels (or tagged lifts of
them). The row set below is their actual image under the public input map.
At the first original column-player query only the ordinary columns are
selected for the multi-bin lower bound; foreign columns are left untouched.
-/

namespace Paper2.TwoStreamConversation

open Workspace.Types.CommComplexity Workspace.Types.Protocol
open Paper2.SourceRemainingConversationNumerics

variable {S J W Rw Ω F : Type*} [Fintype S] [Fintype J]
  [Fintype W] [Fintype Rw] [Fintype Ω] [Fintype F]
  [Nonempty Rw] {s : ℕ}

/-- The actual original rows exposed by the selected raw supports. -/
def nodeRows (Q : Finset (Fin s)) (support : Fin s → Finset W)
    (input : W → Rw) : Set Rw :=
  {r | ∃ i ∈ Q, ∃ w ∈ support i, input w = r}

theorem nodeRows_mem (Q : Finset (Fin s)) (support : Fin s → Finset W)
    (input : W → Rw) {i : Fin s} (hi : i ∈ Q) {w : W}
    (hw : w ∈ support i) : input w ∈ nodeRows Q support input :=
  ⟨i, hi, w, hw, rfl⟩

/-- All ordinary capacity cases except the attached one-bin parent are
impossible at a live node. This theorem derives its row set and enumerates
the physical bins; it assumes neither a projected lower bound nor a frontier.
The latter is obtained by `runScheduled_active_overload` at the caller. -/
theorem ordinary_node_forces_one
    (μ : PositiveRationalLaw S) (ν : PositiveRationalLaw J)
    (κ : FiniteLaw Ω) (T : S → J → Bool)
    (M : Rw → (Ω ⊕ F) → Bool)
    (bin : Rw → Fin s) (selector : Rw → S) (Φ : Ω → Fin s → J)
    (hordinary : ∀ r c, M r (.inl c) = T (selector r) (Φ c (bin r)))
    (hΦ : κ.PushesTo (ν.toFiniteLaw.iid s) Φ)
    (input : W → Rw) (σ : W → S) (Q : Finset (Fin s))
    (support : Fin s → Finset W)
    (hsel : ∀ i ∈ Q, ∀ w ∈ support i, σ w = selector (input w))
    (hbin : ∀ i ∈ Q, ∀ w ∈ support i, bin (input w) = i)
    (O : Set Ω) (hO : (4 / 5 : ℝ) < κ.prob (· ∈ O))
    (H a r : ℕ) (hr : r ≤ a) (hH : 2 ≤ H) (x : ℝ) (hx : 0 < x)
    (hs : s = 2 ^ a)
    (hsmall : SourceSupportSchedule.floor s x 0 ≤ 1 / 8)
    (hprofile : RestrictionProfile T μ.toFiniteLaw ν.toFiniteLaw x (H : ℤ))
    (hmass : ∀ i ∈ Q, SourceSupportSchedule.floor s x r ≤
      ProjectedSupportStep.mass μ.toFiniteLaw σ (support i))
    (hbig : (3 / 4 : ℝ) * ((s : ℝ) / (2 : ℝ) ^ r) ≤ Q.card)
    (query : (Ω ⊕ F) → Bool)
    (left right : Protocol (Ω ⊕ F) Rw Bool)
    (hvalue : ∀ i ∈ Q, ∀ w ∈ support i, ∀ c ∈ O,
      (Protocol.aNode query left right).eval (.inl c) (input w) =
        M (input w) (.inl c))
    (hcost : (Protocol.aNode query left right).cost ≤ H + (a - r)) :
    a - r = 0 ∧ Q.card = 1 := by
  classical
  let R : Set Rw := nodeRows Q support input
  obtain ⟨b, hchild, _⟩ := TwoStreamColumnStep.exists_dense_child κ O
    Sum.inl query hO
  let Ochild := TwoStreamColumnStep.ordinaryChild O Sum.inl query b
  have hvalueR : ∀ row ∈ R, ∀ c ∈ O,
      (Protocol.aNode query left right).eval (.inl c) row = M row (.inl c) := by
    rintro row ⟨i, hi, w, hw, rfl⟩ c hc
    exact hvalue i hi w hw c hc
  have hchildcost : Compression.restrictionD
      (fun row c => M row (.inl c)) R Ochild + 1 ≤
      (Protocol.aNode query left right).cost :=
    TwoStreamColumnStep.ordinary_restriction_add_one_le
      (fun row c => M row (.inl c)) R O Sum.inl query left right
      hvalueR b
  have hmatrix : Compression.restrictionD M R (Sum.inl '' Ochild) =
      Compression.restrictionD (fun row c => M row (.inl c)) R Ochild := by
    have h := restrictionD_pullback_image M id Sum.inl R Ochild
    simpa using h.symm
  have hbudget : Compression.restrictionD M R (Sum.inl '' Ochild) + 1 ≤
      H + (a - r) := by
    rw [hmatrix]
    exact hchildcost.trans hcost
  let k := a - r
  have hcap : (s : ℝ) / (2 : ℝ) ^ r = (2 : ℝ) ^ k :=
    capacity_eq_pow hs hr
  have hscale := capacity_scale hx.le hsmall hs hr
  let e := coordinateEnumeration Q
  have he : Function.Injective e := coordinateEnumeration_injective Q
  have hrow : ∀ j : Fin Q.card, 2 * (2 : ℝ) ^ k * x ≤
      μ.toFiniteLaw.prob (fun z => ∃ row ∈ R,
        bin row = e j ∧ selector row = z) := by
    intro j
    have hf := hmass (e j) (coordinateEnumeration_mem Q j)
    rw [hs, SourceSupportSchedule.floor_capacity a r x hr] at hf
    change 2 * (2 : ℝ) ^ k * x ≤ _ at hf
    -- The raw selector image embeds in the actual original-row event.
    have hm : ProjectedSupportStep.mass μ.toFiniteLaw σ
        (support (e j)) ≤ μ.toFiniteLaw.prob
          (fun z => ∃ row ∈ R, bin row = e j ∧ selector row = z) := by
      apply μ.toFiniteLaw.prob_mono
      rintro z ⟨w, hw, hz⟩
      exact ⟨input w, nodeRows_mem Q support input
        (coordinateEnumeration_mem Q j) hw,
        hbin (e j) (coordinateEnumeration_mem Q j) w hw,
        (hsel (e j) (coordinateEnumeration_mem Q j) w hw).symm.trans hz⟩
    exact hf.trans hm
  have hbig' : (3 / 4 : ℝ) * (2 : ℝ) ^ k ≤ Q.card := by
    simpa only [← hcap] using hbig
  by_cases hk : 2 ≤ k
  · have hcount := SourceSupportSchedule.power_block_count hk hbig'
    have hrow' : ∀ j ∈ (Finset.univ : Finset (Fin Q.card)),
        (2 : ℝ) ^ k * x ≤ μ.toFiniteLaw.prob
          (fun z => ∃ row ∈ R, bin row = e j ∧ selector row = z) := by
      intro j _
      have hp := hrow j
      nlinarith [show 0 ≤ (2 : ℝ) ^ k * x by positivity]
    have hlower := TwoStreamOrdinaryCapacity.many_bin_power_from_ambient
      μ ν κ T M bin selector Φ hordinary hΦ e he R Ochild H k x
      hH hx hk hscale.1 hprofile Finset.univ (by simpa using hcount)
      hrow' (by dsimp only [Ochild]; linarith [hchild])
    omega
  · by_cases hkone : k = 1
    · have hcount : 2 ≤ Q.card := by
        apply SourceSupportSchedule.two_block_count
        simpa [hkone] using hbig'
      have hrow' : ∀ j ∈ (Finset.univ : Finset (Fin Q.card)),
          2 * x ≤ μ.toFiniteLaw.prob
            (fun z => ∃ row ∈ R, bin row = e j ∧ selector row = z) := by
        intro j _
        have hh := hrow j
        simp only [hkone, pow_one] at hh
        nlinarith [show 0 ≤ x by positivity]
      have hlower := TwoStreamOrdinaryCapacity.many_bin_two_from_ambient
        μ ν κ T M bin selector Φ hordinary hΦ e he R Ochild H x
        hH hx hscale.2 hprofile Finset.univ (by simpa using hcount)
        hrow' (by dsimp only [Ochild]; linarith [hchild])
      omega
    · have hkzero : k = 0 := by omega
      by_contra hcard
      have hcard' : 2 ≤ Q.card := by
        have hh : 0 < Q.card := by
          have : (0 : ℝ) < Q.card := by
            have hh : (3 / 4 : ℝ) ≤ Q.card := by simpa [hkzero] using hbig'
            linarith
          exact_mod_cast this
        omega
      have hrow' : ∀ j ∈ (Finset.univ : Finset (Fin Q.card)),
          2 * x ≤ μ.toFiniteLaw.prob
            (fun z => ∃ row ∈ R, bin row = e j ∧ selector row = z) := by
        intro j _
        simpa [hkzero] using hrow j
      have hlower := TwoStreamOrdinaryCapacity.many_bin_two_from_ambient
        μ ν κ T M bin selector Φ hordinary hΦ e he R Ochild H x
        hH hx hscale.2 hprofile Finset.univ (by simpa using hcard')
        hrow' (by dsimp only [Ochild]; linarith [hchild])
      omega

section Full

open Paper2.PairedSelectorMatrix Paper2.PairedSelectorPopulation
open Paper2.ProjectedSupportFrontier Paper2.SourceSupportFrontier

variable {B J₀ Raw : Type*} [Fintype B] [Fintype J₀] [Fintype Raw]
  [DecidableEq Raw]
  {q : ℕ} [NeZero q]

/-- The actual scheduled row-prefix conversation cannot be short. Its
paired-retention premise is structural on the initial raw event; the
surviving joint image, frontier and capacity contradiction are all derived.
The source bridge supplies the initial state and the original-law premise. -/
theorem no_short_transposed
    (μ : PositiveRationalLaw B) (ν : PositiveRationalLaw J₀)
    (base : B → J₀ → Bool) (M : Rw → (Ω ⊕ F) → Bool)
    (H ell a : ℕ) (hH : 2 ≤ H) (hq : q = 2 ^ ell) (hs : s = 2 ^ a)
    (x : ℝ) (hx : 0 < x)
    (hbase : RestrictionProfile base μ.toFiniteLaw ν.toFiniteLaw x (H : ℤ))
    (hT : RestrictionProfile
      (fun z : Fin q → J₀ => fun c : Fin q × B => base c.2 (z c.1))
      (ν.iid q).toFiniteLaw (columnLaw μ).toFiniteLaw x
      ((H + ell : ℕ) : ℤ))
    (κΩ : FiniteLaw Ω) (κRaw : FiniteLaw Raw)
    (bin : Rw → Fin s) (selector : Rw → Fin q → J₀)
    (Φ : Ω → Fin s → Fin q × B) (ψ : F → Fin q × B)
    (hordinary : ∀ row c, M row (.inl c) =
      base (Φ c (bin row)).2 (selector row (Φ c (bin row)).1))
    (hΦ : κΩ.PushesTo ((columnLaw μ).toFiniteLaw.iid s) Φ)
    (ζ : Raw → Selector q J₀)
    (hζ : κRaw.PushesTo (selectorLaw ν q).toFiniteLaw ζ)
    (σ : Raw → Fin q → J₀) (hfirst : σ = fun w => (ζ w).1)
    (input : Raw → Rw) (star : Fin s)
    (initial : ProjectedSupportFrontier.State (Ω ⊕ F) Rw (Fin s) Raw)
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
        ProjectedSupportStep.mass (ν.iid q).toFiniteLaw σ
          (initial.support i))
    (O : Set Ω) (G : Set F)
    (hvalue : ∀ row ∈ initial.columns,
      ∀ c ∈ TwoStreamInitial.retainedColumns O G,
        initial.protocol.eval c row = M row c)
    (hforeign : ∀ w ∈ initial.support star, ∀ f,
      M (input w) (.inr f) = base (ψ f).2 ((ζ w).2 (ψ f).1))
    (hretain : ∀ P' : Finset Raw, P' ⊆ initial.support star →
      SourceSupportStep.mass κRaw (initial.support star \ P') <
        SourceSupportSchedule.floor s x 0 →
      (49 / 64 : ℝ) ≤
        (selectorLaw ν q).toFiniteLaw.prob
          (· ∈ ζ '' (P' : Set Raw)))
    (ε δ : ℝ)
    (hO : 1 - ε ≤ κΩ.prob (· ∈ O))
    (hF : δ ≤ (columnLaw μ).toFiniteLaw.prob (· ∈ ψ '' G))
    (hδ : δ ≤ 1) (hslack : 2 * q * x + 5 * ε + 2 / q ≤ δ)
    (hsmall : SourceSupportSchedule.floor s x 0 ≤ 1 / 8)
    (hcost : initial.protocol.cost ≤ H + ell + a) : False := by
  classical
  let μS := (ν.iid q).toFiniteLaw
  let νJ : FiniteLaw (Fin q × B) := (columnLaw μ).toFiniteLaw
  let T : (Fin q → J₀) → (Fin q × B) → Bool := fun z c => base c.2 (z c.1)
  let σBins : Fin s → Raw → (Fin q → J₀) := fun _ => σ
  let inputBins : Fin s → Raw → Rw := fun _ => input
  let floor := SourceSupportSchedule.floor s x
  let K := runScheduled μS σBins inputBins floor 0 (a + 1) initial
  have hqpos : 0 < q := NeZero.pos q
  have hspos : 0 < s := by rw [hs]; positivity
  obtain ⟨hε, _, hdense⟩ := TwoStreamInitial.ordinary_density κΩ O q
    hqpos x ε δ hx.le hO hδ hslack
  have hordinaryT : ∀ row c,
      M row (.inl c) = T (selector row) (Φ c (bin row)) := hordinary
  have hinitval : ∀ i ∈ initial.coordinates,
      ∀ w ∈ initial.support i, ∀ c ∈ O,
      initial.protocol.eval (.inl c) (inputBins i w) =
        T (σBins i w) (Φ c i) := by
    intro i hi w hw c hc
    rw [hvalue (input w) (hreaches i hi w hw) (.inl c)
      ((TwoStreamInitial.inl_mem O G c).mpr hc), hordinaryT,
      hbin i hi w hw, ← hsel i hi w hw]
  have hlive := TwoStreamLiveStops.run_live_stops μS νJ κΩ T
    (H + ell) a (by omega) hs x hx.le hT Φ hΦ O (by linarith)
    σBins inputBins Sum.inl initial hinitval hcost hmass hreaches
  have hZsubset : initial.attachments ⊆ initial.coordinates := by simp [hZ, hQ]
  have hcount : initial.coordinates.card + 0 = s := by simp [hQ]
  obtain ⟨v, hbig, hover⟩ := runScheduled_active_overload μS σBins
    inputBins floor 0 (a + 1) initial hZsubset s 0 hcount
    (by simp [hZ])
  have hpath := runScheduled_bobPath μS σBins inputBins floor 0 (a + 1) initial v.val
  have hsets := runScheduled_sets_subset μS σBins inputBins floor 0 (a + 1) initial v.val
  have hreach := runScheduled_support_reaches μS σBins inputBins floor 0 (a + 1)
    initial hreaches v.val
  have hfloors := runScheduled_floor μS σBins inputBins floor
    (fun d => (SourceSupportSchedule.twice_next s x d).symm)
    0 (a + 1) initial hmass v.val
  obtain ⟨_, hdepth, hAlice⟩ := hlive v.val v.property
  let node := K.state v.val
  let r := (K.route v.val).length
  change r ≤ a at hdepth
  change (s : ℝ) / (2 : ℝ) ^ r <
    (node.coordinates.card : ℝ) + (node.attachments.card : ℝ) at hover
  change (3 * ((s : ℝ) / (2 : ℝ) ^ r)) / 4 ≤
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
      ∀ c ∈ O, node.protocol.eval (.inl c) (input w) = M (input w) (.inl c) := by
    intro i hi w hw c hc
    exact (hpath.eval_eq (.inl c) (input w) (hreach i hi w hw)).trans
      (hvalue (input w) (hpath.columns_subset (hreach i hi w hw)) (.inl c)
        ((TwoStreamInitial.inl_mem O G c).mpr hc))
  have hcostNode : node.protocol.cost ≤ H + ell + (a - r) := by
    have hc := hpath.cost_add_length
    change node.protocol.cost + r ≤ initial.protocol.cost at hc
    omega
  obtain ⟨query, left, right, hAliceEq⟩ := hAlice
  have hremain := ordinary_node_forces_one (ν.iid q) (columnLaw μ) κΩ T M bin selector Φ
    hordinaryT hΦ input σ node.coordinates node.support hselNode
    hbinNode O hdense (H + ell) a r hdepth (by omega) x hx hs hsmall
    hT (by simpa only [zero_add] using hfloors)
    (by convert hbig using 1 <;> ring) query left right
    (by simpa only [← hAliceEq] using hvalueNode)
    (by simpa only [← hAliceEq] using hcostNode)
  obtain ⟨hkzero, hone⟩ := hremain
  have hrEq : r = a := by omega
  have hZnode : node.attachments ⊆ node.coordinates :=
    runScheduled_attachments_subset μS σBins inputBins floor 0 (a + 1)
      initial hZsubset v.val
  have hoverOne : (1 : ℝ) < (node.coordinates.card : ℝ) +
      (node.attachments.card : ℝ) := by
    have hc := capacity_eq_pow hs hdepth
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
    have heq : i = star := Finset.mem_singleton.mp hsingle
    exact heq ▸ hi
  have hstarQ : star ∈ node.coordinates := hZnode hstarNode
  have hζ' : κRaw.PushesTo (μS.prod μS) ζ := by
    simpa only [μS, selectorLaw, PositiveRationalLaw.toFiniteLaw_prod] using hζ
  have hretain' : ∀ P' : Finset Raw, P' ⊆ initial.support star →
      SourceSupportStep.mass κRaw (initial.support star \ P') < floor 0 →
      (49 / 64 : ℝ) ≤ (μS.prod μS).prob (· ∈ ζ '' (P' : Set Raw)) := by
    intro P' hsub hloss
    simpa only [μS, selectorLaw, PositiveRationalLaw.toFiniteLaw_prod] using
      hretain P' hsub hloss
  have hpairmass := TwoStreamRetention.retained_pair_mass κRaw μS ζ hζ'
    σBins star (by simpa [σBins] using hfirst)
    inputBins floor (fun d => (SourceSupportSchedule.twice_next s x d).symm)
    (SourceSupportSchedule.floor_pos hspos hx) (a + 1) initial hZ
    hretain' v.val hstarNode
  let P : Set Raw := (node.support star : Set Raw)
  let Rnode : Set Rw := nodeRows node.coordinates node.support input
  have hpairRow : ∀ w ∈ P, input w ∈ Rnode := by
    intro w hw
    exact nodeRows_mem node.coordinates node.support input hstarQ hw
  have hpairStar : ∀ w ∈ P,
      bin (input w) = star ∧ selector (input w) = (ζ w).1 := by
    intro w hw
    refine ⟨hbinNode star hstarQ w hw, ?_⟩
    rw [← hselNode star hstarQ w hw, hfirst]
  have hpairForeign : ∀ w ∈ P, ∀ f,
      M (input w) (.inr f) = base (ψ f).2 ((ζ w).2 (ψ f).1) := by
    intro w hw f
    exact hforeign w (hsets.2.2 star hw) f
  have hOprojected : 1 - ε ≤ νJ.prob (· ∈ (fun c => Φ c star) '' O) := by
    have hcoord := TwoStreamScalarCost.coordinate_pushes νJ κΩ s Φ hΦ star
    exact hO.trans (FiniteLaw.prob_le_image κΩ νJ (fun c => Φ c star) hcoord O)
  have hδpos : 0 < δ := by
    have hqreal : (0 : ℝ) < q := by exact_mod_cast hqpos
    have : (0 : ℝ) < 2 / (q : ℝ) := by positivity
    have : 0 ≤ 2 * (q : ℝ) * x := by positivity
    linarith
  have hpairedLower := TwoStreamPairedLocal.parent_capacity μ ν base M
    H ell hH hq x hx hbase bin selector Φ ψ star input ζ hordinary
    P Rnode O G hpairStar hpairForeign hpairRow ε δ
    (by simpa only [μS, selectorLaw, PositiveRationalLaw.toFiniteLaw_prod] using hpairmass)
    hOprojected hF hδpos hδ hslack
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
      (hvalue (input w) (hpath.columns_subset (hreach i hi w hw)) c.val c.property)
  have hparentUpper : Compression.restrictionD M Rnode
      (TwoStreamInitial.retainedColumns O G) ≤ node.protocol.cost := by
    have hh : Compression.restrictionD M Rnode
        (TwoStreamInitial.retainedColumns O G) ≤ Qp.cost :=
      Nat.sInf_le ⟨Qp, rfl, hQp⟩
    simpa only [Qp, Workspace.UpperBound.Protocol.comap_cost,
      Workspace.UpperBound.Protocol.transpose_cost] using hh
  have hparentCost : node.protocol.cost ≤ H + ell := by omega
  have hC : TwoStreamInitial.retainedColumns O G =
      (Sum.inl '' O) ∪ (Sum.inr '' G) := rfl
  rw [← hC] at hpairedLower
  omega

end Full

end Paper2.TwoStreamConversation

#print axioms Paper2.TwoStreamConversation.ordinary_node_forces_one
#print axioms Paper2.TwoStreamConversation.no_short_transposed
