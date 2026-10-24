import Paper2.PairedSelectorLiveStops
import Paper2.PairedSupportFrontierOverload
import Paper2.PairedSelectorCapacity
import Paper2.PairedSelectorCapacityPair
import Paper2.SourceRemainingConversationNumerics

/-!
# The actual remaining conversation for two selectors

Frozen v12 Section 5, `res:paired`. We run the paired-support recursion
on the original protocol and derive its live stopping frontier. The counted
blocks include separated singles of either tag and one ordinary block for
each still-attached pair. At capacity one with a single attached pair, its
two literal tags contradict the original parent budget. No graph witness,
assumed stopping frontier, or desired lower-bound callback is needed.
-/

namespace Paper2.PairedSelectorConversation

open PairedSelectorMatrix PairedSupportFrontier
open SourceRemainingConversationNumerics Workspace.Types.Protocol

/-- The abstract paired lemma only has initial floor less than one.
The stronger one-eighth source bound is not needed for any terminal call. -/
theorem capacity_scale {q ell r : ℕ} {x : ℝ} (hx : 0 ≤ x)
    (hsmall : SourceSupportSchedule.floor q x 0 < 1)
    (hq : q = 2 ^ ell) (hr : r ≤ ell) :
    (2 : ℝ) ^ (ell - r) * x ≤ 1 ∧ 2 * x ≤ 1 := by
  subst q
  have hf : SourceSupportSchedule.floor (2 ^ ell) x r < 1 :=
    (SourceSupportSchedule.floor_antitone hx (Nat.zero_le r)).trans_lt hsmall
  rw [SourceSupportSchedule.floor_capacity ell r x hr] at hf
  have hb : 2 * (2 : ℝ) ^ ell * x < 1 := by
    simpa only [SourceSupportSchedule.floor_zero, Nat.cast_pow, Nat.cast_ofNat] using hsmall
  have hp : (1 : ℝ) ≤ 2 ^ ell := one_le_pow₀ (by norm_num)
  have hpx : 0 ≤ ((2 : ℝ) ^ ell - 1) * x := mul_nonneg (sub_nonneg.mpr hp) hx
  have hkx : 0 ≤ (2 : ℝ) ^ (ell - r) * x := by positivity
  constructor <;> nlinarith

variable {W J : Type*} [Fintype W] [Fintype J] {q : ℕ}

/-- A short protocol on an actual initial support state is impossible.
The hypotheses specify only the initial retained matrix, disjoint supports,
counts and masses. All frontier and terminal lower bounds are derived. -/
theorem remaining_conversation_contradiction
    (μ : PositiveRationalLaw W) (ν : PositiveRationalLaw J)
    (R : W → J → Bool) (H ell : ℕ) (hH : 2 ≤ H)
    (hq : q = 2 ^ ell) (x : ℝ) (hx : 0 < x)
    (hsmall : SourceSupportSchedule.floor q x 0 < 1)
    (hprofile : RestrictionProfile R μ.toFiniteLaw ν.toFiniteLaw x (H : ℤ))
    (A : Set (Selector q J))
    (hA : (49 / 64 : ℝ) ≤ (selectorLaw ν q).toFiniteLaw.prob (· ∈ A))
    (initial : State A (Column q W) (Fin q) W)
    (hP : ∀ a : A, ∀ c ∈ initial.columns,
      initial.protocol.eval a c = matrix R a.val c)
    (hcost : initial.protocol.cost ≤ H + ell)
    (hvalid : initial.Valid) (b : ℕ)
    (hcount : initial.h + b = q) (hexcess : 3 * b < initial.z)
    (hmass : ∀ a ∈ initial.blocks, SourceSupportSchedule.floor q x 0 ≤
      SourceSupportStep.mass μ.toFiniteLaw (initial.support a))
    (hreaches : ∀ a ∈ initial.blocks, ∀ w ∈ initial.support a,
      (a, w) ∈ initial.columns) : False := by
  classical
  let law := μ.toFiniteLaw
  let input : Block q → W → Column q W := fun a w => (a, w)
  let floor := SourceSupportSchedule.floor q x
  let T := PairedSupportFrontier.run law input (ell + 1) initial
  have hlive := PairedSelectorLiveStops.run_live_stops μ ν R H ell hH hq x hx.le
    hprofile A hA initial hP hcost hmass hreaches
  change ∀ v : T.Leaves, 0 < (T.state v).h →
    H ≤ (T.state v).protocol.cost ∧ (T.route v).length ≤ ell ∧
    ∃ query left right, (T.state v).protocol = Protocol.aNode query left right at hlive
  obtain ⟨v, hdepth, hbig, hover⟩ := PairedSupportFrontier.run_active_overload_bounded
    law input (ell + 1) initial hvalid q b ell hcount hexcess
    (fun v => (hlive v.val v.property).2.1)
  let node := T.state v.val
  let depth := (T.route v.val).length
  let k := ell - depth
  change depth ≤ ell at hdepth
  have hcapacity : (q : ℝ) / (2 : ℝ) ^ depth = (2 : ℝ) ^ k :=
    capacity_eq_pow hq hdepth
  change 3 * ((q : ℝ) / (2 : ℝ) ^ depth) / 4 ≤ (node.h : ℝ) at hbig
  change (q : ℝ) / (2 : ℝ) ^ depth < (node.h : ℝ) + (node.z : ℝ) at hover
  rw [hcapacity] at hbig hover
  have hbig' : (3 / 4 : ℝ) * (2 : ℝ) ^ k ≤ (node.h : ℝ) := by linarith
  have hp := PairedSupportFrontier.run_bobPath law input (ell + 1) initial v.val
  change SourceSupportFrontier.BobPath initial.protocol initial.columns (T.route v.val)
    node.protocol node.columns at hp
  have hm := PairedSupportFrontier.run_mass_floors law input floor
    (fun r => (SourceSupportSchedule.twice_next q x r).symm)
    0 (ell + 1) initial hmass v.val
  change ∀ a ∈ node.blocks, floor (0 + depth) ≤
    SourceSupportStep.mass law (node.support a) at hm
  simp only [zero_add] at hm
  have hr := PairedSupportFrontier.run_support_reaches law input (ell + 1)
    initial hreaches v.val
  change ∀ a ∈ node.blocks, ∀ word ∈ node.support a, (a, word) ∈ node.columns at hr
  have hv := PairedSupportFrontier.run_valid law input (ell + 1) initial hvalid v.val
  change node.Valid at hv
  let P := Workspace.UpperBound.Protocol.comap id
    (fun c : node.columns => c.val) node.protocol
  have hPc : P.Computes (fun (a : A) (c : node.columns) => matrix R a.val c.val) := by
    intro a c
    rw [Workspace.UpperBound.Protocol.comap_eval]
    exact (hp.eval_eq a c.val c.property).trans
      (hP a c.val (hp.columns_subset c.property))
  have hnodecost : node.protocol.cost ≤ H + k :=
    remaining_cost hp.cost_add_length hcost hdepth
  have hPcost : P.cost ≤ H + k := by
    simpa only [P, Workspace.UpperBound.Protocol.comap_cost] using hnodecost
  obtain ⟨query, left, right, hAlice⟩ := (hlive v.val v.property).2.2
  change node.protocol = Protocol.aNode query left right at hAlice
  let left' := Workspace.UpperBound.Protocol.comap id (fun c : node.columns => c.val) left
  let right' := Workspace.UpperBound.Protocol.comap id (fun c : node.columns => c.val) right
  have hPalice : P = Protocol.aNode query left' right' := by
    simp only [P, hAlice, Workspace.UpperBound.Protocol.comap, id_eq, left', right']
  let primary := PairedSupportStep.primary node.singles node.pairs
  have hprimary : primary.card = node.h :=
    PairedSupportStep.primary_card node.singles node.pairs hv
  let e : Fin primary.card → Block q := fun i => (primary.equivFin.symm i).val
  have he : Function.Injective e := by
    intro i j hij
    apply primary.equivFin.symm.injective
    exact Subtype.ext hij
  have he_mem (i : Fin primary.card) : e i ∈ node.blocks :=
    PairedSupportStep.primary_subset_active node.singles node.pairs
      (primary.equivFin.symm i).property
  let S : Set (Fin primary.card × W) := fun a => a.2 ∈ node.support (e a.1)
  have hS : ∀ a ∈ S, (e a.1, a.2) ∈ node.columns := by
    intro a ha
    exact hr (e a.1) (he_mem a.1) a.2 ha
  have hf : floor depth = 2 * (2 : ℝ) ^ k * x := by
    dsimp only [floor]
    rw [hq]
    exact SourceSupportSchedule.floor_capacity ell depth x hdepth
  have hrow : ∀ i, 2 * (2 : ℝ) ^ k * x ≤ law.prob (fun word => (i, word) ∈ S) := by
    intro i
    have hi := hm (e i) (he_mem i)
    rw [hf] at hi
    exact hi
  have hbigPrimary : (3 / 4 : ℝ) * (2 : ℝ) ^ k ≤ (primary.card : ℝ) := by
    rw [hprimary]
    exact hbig'
  have hscale := capacity_scale hx.le hsmall hq hdepth
  by_cases hk : 2 ≤ k
  · exact PairedSelectorCapacity.alice_power_contradiction μ ν R H k hH hx hk hscale.1
      hprofile e he A S hbigPrimary node.columns hS hrow hA query left' right'
      (by simpa only [← hPalice] using hPc) (by simpa only [← hPalice] using hPcost)
  · by_cases hkone : k = 1
    · exact PairedSelectorCapacity.alice_capacity_two_contradiction μ ν R H hH hx hscale.2
        hprofile e he A S (by simpa [hkone] using hbigPrimary) node.columns hS
        (fun i => by simpa only [hkone, pow_one, show (2 : ℝ) * 2 = 4 by norm_num] using hrow i)
        hA query left' right' (by simpa only [← hPalice] using hPc)
        (by simpa only [← hPalice, hkone] using hPcost)
    · have hkzero : k = 0 := by omega
      by_cases hn : 2 ≤ node.h
      · exact PairedSelectorCapacity.alice_capacity_one_many_contradiction μ ν R H hH hx
          hscale.2 hprofile e he A S (by omega) node.columns hS
          (fun i => by simpa [hkzero] using hrow i) hA query left' right'
          (by simpa only [← hPalice] using hPc)
          (by simpa only [← hPalice, hkzero, Nat.add_zero] using hPcost)
      · have hoverN : 1 < node.h + node.z := by
          have hoverR : (1 : ℝ) < (node.h : ℝ) + (node.z : ℝ) := by
            simpa only [hkzero, pow_zero] using hover
          exact_mod_cast hoverR
        have hone := SourceSupportSchedule.single_support_attachment
          (by simpa only [hkzero, pow_zero, mul_one] using hbig') hoverN
          node.z_le_h (by omega)
        obtain ⟨α, hα⟩ := Finset.card_pos.mp (show 0 < node.pairs.card by
          change 0 < node.z
          omega)
        have hblock (tag : Bool) : (tag, α) ∈ node.blocks :=
          (PairedSupportStep.mem_active node.singles node.pairs (tag, α)).mpr (Or.inr hα)
        have hword (tag : Bool) : 2 * x ≤
            μ.toFiniteLaw.prob (fun word => word ∈ node.support (tag, α)) := by
          have ht := hm (tag, α) (hblock tag)
          rw [hf] at ht
          simpa only [hkzero, pow_zero, mul_one] using ht
        exact PairedSelectorCapacityPair.paired_parent_contradiction μ ν R H hH hx
          hscale.2 hprofile α A (node.support (false, α) : Set W)
          (node.support (true, α) : Set W) node.columns
          (hr (false, α) (hblock false)) (hr (true, α) (hblock true))
          (hword false) (hword true) hA P hPc
          (by simpa only [hkzero, Nat.add_zero] using hPcost)

end Paper2.PairedSelectorConversation

#print axioms Paper2.PairedSelectorConversation.capacity_scale
#print axioms Paper2.PairedSelectorConversation.remaining_conversation_contradiction
