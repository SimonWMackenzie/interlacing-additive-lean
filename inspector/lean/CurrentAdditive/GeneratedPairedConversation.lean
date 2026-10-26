import CurrentAdditive.GeneratedPairedParentTerminal
import Paper2.PairedSelectorConversation

/-! Actual Bob-only frontier and terminal contradiction for `det:paired`. -/

namespace CurrentAdditive.DeterministicIndexedMatrix.Sources

open Paper2 Paper2.PairedSelectorMatrix Paper2.PairedSupportFrontier
open Paper2.SourceRemainingConversationNumerics
open CurrentAdditive.ArbitraryPrefix
open Workspace.Types.Protocol

variable {X Y I : Type*} [Fintype X] [Fintype Y] [Fintype I]
  [DecidableEq X] [DecidableEq Y]
  {D q₁ q₂ s : ℕ} [NeZero s] [NeZero q₁] [NeZero q₂]
  {μX : PositiveRationalLaw X} {μY : PositiveRationalLaw Y}
  (src : Sources (D := D) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY)

/-- The source-specific version of the paired-support conversation. Its
state, run and overload are the actual generic protocol recursion; terminal
costs use the indexed pair-source lemmas rather than a whole-word iid law. -/
theorem paired_remaining_conversation_contradiction
    (R₀ : X → Y → Bool) (H ell : ℕ) (hH : 2 ≤ H)
    (hq : q₂ = 2 ^ ell) (x : ℝ) (hx : 0 < x)
    (hD : 8 ≤ D)
    (hsmall : SourceSupportSchedule.floor q₂ x 0 < 1)
    (hprofile : RestrictionProfile (A src R₀)
      src.gamma.law.toFiniteLaw
      ((PositiveRationalLaw.uniform (Fin q₁)).prod μX).toFiniteLaw
      x (H : ℤ))
    (K : Set (src.inner.Label × src.inner.Label))
    (hK : (49/64 : ℝ) ≤
      (src.inner.law.toFiniteLaw.prod src.inner.law.toFiniteLaw).prob (· ∈ K))
    (initial : State K (Paper2.PairedSelectorMatrix.Column q₂ src.gamma.Label)
      (Fin q₂) src.gamma.Label)
    (hP : ∀ z : K, ∀ c ∈ initial.columns,
      initial.protocol.eval z c = pairedIndexed src R₀ z.val
        (c.1.1, (c.1.2, c.2)))
    (hcost : initial.protocol.cost ≤ H + ell)
    (hvalid : initial.Valid) (b : ℕ)
    (hcount : initial.h + b = q₂) (hexcess : 3*b < initial.z)
    (hmass : ∀ a ∈ initial.blocks, SourceSupportSchedule.floor q₂ x 0 ≤
      SourceSupportStep.mass src.gamma.law.toFiniteLaw (initial.support a))
    (hreaches : ∀ a ∈ initial.blocks, ∀ γ ∈ initial.support a,
      (a, γ) ∈ initial.columns) : False := by
  classical
  let law := src.gamma.law.toFiniteLaw
  let input : Block q₂ → src.gamma.Label →
      Paper2.PairedSelectorMatrix.Column q₂ src.gamma.Label :=
    fun a γ => (a, γ)
  let floor := SourceSupportSchedule.floor q₂ x
  let T := run law input (ell + 1) initial
  have hlive := paired_run_live_stops src R₀ H ell hH hq x hx.le
    (by omega) hprofile K hK initial hP hcost hmass hreaches
  change ∀ v : T.Leaves, 0 < (T.state v).h →
    H ≤ (T.state v).protocol.cost ∧ (T.route v).length ≤ ell ∧
    ∃ query left right, (T.state v).protocol = Protocol.aNode query left right at hlive
  obtain ⟨v, hdepth, hbig, hover⟩ := run_active_overload_bounded
    law input (ell + 1) initial hvalid q₂ b ell hcount hexcess
    (fun v => (hlive v.val v.property).2.1)
  let node := T.state v.val
  let depth := (T.route v.val).length
  let k := ell - depth
  change depth ≤ ell at hdepth
  have hcapacity : (q₂ : ℝ) / (2 : ℝ) ^ depth = (2 : ℝ) ^ k :=
    capacity_eq_pow hq hdepth
  change 3 * ((q₂ : ℝ) / (2 : ℝ) ^ depth) / 4 ≤ (node.h : ℝ) at hbig
  change (q₂ : ℝ) / (2 : ℝ) ^ depth <
    (node.h : ℝ) + (node.z : ℝ) at hover
  rw [hcapacity] at hbig hover
  have hbig' : (3/4 : ℝ) * (2 : ℝ)^k ≤ (node.h : ℝ) := by linarith
  have hp := run_bobPath law input (ell + 1) initial v.val
  change SourceSupportFrontier.BobPath initial.protocol initial.columns
    (T.route v.val) node.protocol node.columns at hp
  have hm := run_mass_floors law input floor
    (fun r => (SourceSupportSchedule.twice_next q₂ x r).symm)
    0 (ell + 1) initial hmass v.val
  change ∀ a ∈ node.blocks, floor (0 + depth) ≤
    SourceSupportStep.mass law (node.support a) at hm
  simp only [zero_add] at hm
  have hr := run_support_reaches law input (ell + 1)
    initial hreaches v.val
  change ∀ a ∈ node.blocks, ∀ γ ∈ node.support a,
    (a, γ) ∈ node.columns at hr
  have hv := run_valid law input (ell + 1) initial hvalid v.val
  change node.Valid at hv
  let P := Workspace.UpperBound.Protocol.comap id
    (fun c : node.columns => c.val) node.protocol
  have hPc : P.Computes (fun (z : K) (c : node.columns) =>
      pairedIndexed src R₀ z.val (c.val.1.1, (c.val.1.2, c.val.2))) := by
    intro z c
    rw [Workspace.UpperBound.Protocol.comap_eval]
    exact (hp.eval_eq z c.val c.property).trans
      (hP z c.val (hp.columns_subset c.property))
  have hnodecost : node.protocol.cost ≤ H + k :=
    remaining_cost hp.cost_add_length hcost hdepth
  have hPcost : P.cost ≤ H + k := by
    simpa only [P, Workspace.UpperBound.Protocol.comap_cost] using hnodecost
  obtain ⟨query, left, right, hAlice⟩ := (hlive v.val v.property).2.2
  change node.protocol = Protocol.aNode query left right at hAlice
  let left' := Workspace.UpperBound.Protocol.comap id
    (fun c : node.columns => c.val) left
  let right' := Workspace.UpperBound.Protocol.comap id
    (fun c : node.columns => c.val) right
  have hPalice : P = Protocol.aNode query left' right' := by
    simp only [P, hAlice, Workspace.UpperBound.Protocol.comap, id_eq, left', right']
  let primary := PairedSupportStep.primary node.singles node.pairs
  have hprimary : primary.card = node.h :=
    PairedSupportStep.primary_card node.singles node.pairs hv
  let e : Fin primary.card → Block q₂ :=
    fun i => (primary.equivFin.symm i).val
  have he : Function.Injective e := by
    intro i j hij
    apply primary.equivFin.symm.injective
    exact Subtype.ext hij
  have he_mem (i : Fin primary.card) : e i ∈ node.blocks :=
    PairedSupportStep.primary_subset_active node.singles node.pairs
      (primary.equivFin.symm i).property
  let Rows : Fin primary.card → Set src.gamma.Label :=
    fun i => node.support (e i)
  have hRows : ∀ i : Fin primary.card, ∀ γ ∈ Rows i,
      (e i, γ) ∈ node.columns := by
    intro i γ hγ
    exact hr (e i) (he_mem i) γ hγ
  have hf : floor depth = 2 * (2 : ℝ)^k * x := by
    dsimp only [floor]
    rw [hq]
    exact SourceSupportSchedule.floor_capacity ell depth x hdepth
  have hrow : ∀ i : Fin primary.card,
      2 * (2 : ℝ)^k * x ≤ law.prob (· ∈ Rows i) := by
    intro i
    have hi := hm (e i) (he_mem i)
    rw [hf] at hi
    exact hi
  have hbigPrimary : (3/4 : ℝ) * (2 : ℝ)^k ≤
      (primary.card : ℝ) := by
    rw [hprimary]
    exact hbig'
  have hscale := Paper2.PairedSelectorConversation.capacity_scale hx.le
    hsmall hq hdepth
  by_cases hk : 2 ≤ k
  · have hn := SourceSupportSchedule.power_block_count hk hbigPrimary
    have hweak : ∀ i : Fin primary.card,
        (2 : ℝ)^k*x ≤ law.prob (· ∈ Rows i) := by
      intro i
      have hi := hrow i
      have hp : 0 ≤ (2 : ℝ)^k*x := by positivity
      nlinarith
    have hl := selected_paired_alice_cost src R₀ H k primary.card x hD
      (by omega) hH hx hscale.1 hprofile e he hn Rows hweak
      K hK node.columns hRows query left' right'
      (by simpa only [← hPalice] using hPc)
    have hu : (Protocol.aNode query left' right').cost ≤ H+k := by
      simpa only [← hPalice] using hPcost
    omega
  · by_cases hkone : k = 1
    · have hn : 2 ≤ primary.card :=
        SourceSupportSchedule.two_block_count (by simpa [hkone] using hbigPrimary)
      have hweak : ∀ i : Fin primary.card,
          2*x ≤ law.prob (· ∈ Rows i) := by
        intro i
        have hi := hrow i
        simp only [hkone, pow_one] at hi
        nlinarith [hx.le]
      have hl := selected_paired_alice_cost src R₀ H 1 primary.card x hD
        (by omega) hH hx (by simpa only [pow_one] using hscale.2)
        hprofile e he (by simpa using hn) Rows
        (by intro i; simpa only [pow_one] using hweak i)
        K hK node.columns hRows query left' right'
        (by simpa only [← hPalice] using hPc)
      have hu : (Protocol.aNode query left' right').cost ≤ H+1 := by
        simpa only [← hPalice, hkone] using hPcost
      omega
    · have hkzero : k = 0 := by omega
      by_cases hn : 2 ≤ node.h
      · have hn' : 2 ≤ primary.card := by rw [hprimary]; exact hn
        have hweak : ∀ i : Fin primary.card,
            2*x ≤ law.prob (· ∈ Rows i) := by
          intro i
          simpa [hkzero] using hrow i
        have hl := selected_paired_alice_cost src R₀ H 1 primary.card x hD
          (by omega) hH hx (by simpa only [pow_one] using hscale.2)
          hprofile e he (by simpa using hn') Rows
          (by intro i; simpa only [pow_one] using hweak i)
          K hK node.columns hRows query left' right'
          (by simpa only [← hPalice] using hPc)
        have hu : (Protocol.aNode query left' right').cost ≤ H := by
          simpa only [← hPalice, hkzero, Nat.add_zero] using hPcost
        omega
      · have hoverN : 1 < node.h + node.z := by
          have hoverR : (1 : ℝ) < (node.h : ℝ) + (node.z : ℝ) := by
            simpa only [hkzero, pow_zero] using hover
          exact_mod_cast hoverR
        have hone := SourceSupportSchedule.single_support_attachment
          (by simpa only [hkzero, pow_zero, mul_one] using hbig')
          hoverN node.z_le_h (by omega)
        obtain ⟨α, hα⟩ := Finset.card_pos.mp
          (show 0 < node.pairs.card by change 0 < node.z; omega)
        have hblock (tag : Bool) : (tag, α) ∈ node.blocks :=
          (PairedSupportStep.mem_active node.singles node.pairs (tag, α)).mpr
            (Or.inr hα)
        have hword (tag : Bool) : 2*x ≤
            law.prob (fun γ => γ ∈ node.support (tag, α)) := by
          have ht := hm (tag, α) (hblock tag)
          rw [hf] at ht
          simpa only [hkzero, pow_zero, mul_one] using ht
        have hl := paired_parent_cost src R₀ H x hD hH hx hscale.2
          hprofile α K (node.support (false, α) : Set src.gamma.Label)
          (node.support (true, α) : Set src.gamma.Label) node.columns
          (hr (false, α) (hblock false))
          (hr (true, α) (hblock true))
          (hword false) (hword true) hK
        have hup : Compression.restrictionD
            (fun z c => pairedIndexed src R₀ z (c.1.1, (c.1.2, c.2)))
            K node.columns ≤ P.cost := Nat.sInf_le ⟨P, rfl, hPc⟩
        have hu : P.cost ≤ H := by
          simpa only [hkzero, Nat.add_zero] using hPcost
        have hc : H+1 ≤ P.cost := hl.trans hup
        omega

#print axioms paired_remaining_conversation_contradiction

end CurrentAdditive.DeterministicIndexedMatrix.Sources
