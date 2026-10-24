import Paper2.SourceSupportFrontierActive
import Paper2.SourceSupportSchedule
import Paper2.SourceRemainingConversationNumerics
import Workspace.UpperBound

/-!
The conserved demand in the selected v38 source, lem:collision-tracking.
This theorem runs the literal Bob-query recursion. A marked support has weight
two while it remains intact; after a split, its two descendants have weight
one each. Empty-coordinate leaves contribute zero and are removed only after
the actual run has been constructed.
-/

namespace CurrentAdditive.V38Collision

open Paper2.SourceSupportFrontier
open scoped BigOperators

variable {A C I W : Type*} [Fintype W]

/-- The actual run conserves the number of supports plus the number of
unsplit marks. No stop or frontier count is assumed. -/
theorem run_conserved_demand (μ : Paper2.FiniteLaw W) (input : I → W → C)
    (floor : ℕ → ℝ) (fuel : ℕ) (initial : State A C I W)
    (hmarked : initial.attachments ⊆ initial.coordinates) :
    let T := run μ input floor 0 fuel initial
    (∑ v : Active T, ((T.state v.val).coordinates.card +
      (T.state v.val).attachments.card)) =
      initial.coordinates.card + initial.attachments.card := by
  classical
  let T := run μ input floor 0 fuel initial
  have hm : ∀ v : T.Leaves, (T.state v).attachments ⊆
      (T.state v).coordinates :=
    run_attachments_subset μ input floor 0 fuel initial hmarked
  have hc := run_counts μ input floor 0 fuel initial hmarked
  have hcoords : (∑ v : Active T, (T.state v.val).coordinates.card) =
      initial.coordinates.card + T.totalSplits := by
    rw [sum_active_coordinates T]
    exact hc.1
  have hmarks : (∑ v : Active T, (T.state v.val).attachments.card) +
      T.totalSplits = initial.attachments.card := by
    rw [sum_active_attachments T hm]
    exact hc.2
  change (∑ v : Active T, ((T.state v.val).coordinates.card +
      (T.state v.val).attachments.card)) =
      initial.coordinates.card + initial.attachments.card
  rw [Finset.sum_add_distrib]
  omega

/-- There is an overloaded actual stopping node for the sharp v38 condition
w0>b. Its path is one of the original protocol's Bob-only paths. -/
theorem run_conserved_overload (μ : Paper2.FiniteLaw W) (input : I → W → C)
    (floor : ℕ → ℝ) (fuel : ℕ) (initial : State A C I W)
    (hmarked : initial.attachments ⊆ initial.coordinates)
    (q b : ℕ) (hcount : initial.coordinates.card + b = q)
    (hexcess : b < initial.attachments.card) :
    let T := run μ input floor 0 fuel initial
    ∃ v : Active T,
      (q : ℝ) / (2 : ℝ) ^ (T.route v.val).length <
        ((T.state v.val).coordinates.card : ℝ) +
          ((T.state v.val).attachments.card : ℝ) := by
  classical
  let T := run μ input floor 0 fuel initial
  have hdemand := run_conserved_demand μ input floor fuel initial hmarked
  change (∑ v : Active T, ((T.state v.val).coordinates.card +
      (T.state v.val).attachments.card)) =
      initial.coordinates.card + initial.attachments.card at hdemand
  have hlarge : q < initial.coordinates.card + initial.attachments.card := by omega
  have hsum : ∑ v : Active T, ((q : ℝ) / (2 : ℝ) ^ (T.route v.val).length) ≤ q :=
    Paper2.Frontier.sum_capacity_le (activeRoute T) (active_prefixFree T)
      (q : ℝ) (Nat.cast_nonneg q)
  by_contra hnone
  change ¬ ∃ v : Active T,
    (q : ℝ) / (2 : ℝ) ^ (T.route v.val).length <
      ((T.state v.val).coordinates.card : ℝ) +
        ((T.state v.val).attachments.card : ℝ) at hnone
  push Not at hnone
  have hle : ∑ v : Active T,
      (((T.state v.val).coordinates.card : ℝ) +
        ((T.state v.val).attachments.card : ℝ)) ≤
      ∑ v : Active T, (q : ℝ) / (2 : ℝ) ^ (T.route v.val).length := by
    apply Finset.sum_le_sum
    intro v _
    exact hnone v
  have hdemandReal : (∑ v : Active T,
      (((T.state v.val).coordinates.card : ℝ) +
        ((T.state v.val).attachments.card : ℝ))) =
      (initial.coordinates.card : ℝ) + initial.attachments.card := by
    exact_mod_cast hdemand
  have hlargeReal : (q : ℝ) <
      (initial.coordinates.card : ℝ) + initial.attachments.card := by
    exact_mod_cast hlarge
  linarith

end CurrentAdditive.V38Collision

#print axioms CurrentAdditive.V38Collision.run_conserved_demand
#print axioms CurrentAdditive.V38Collision.run_conserved_overload

namespace CurrentAdditive.V38Collision

open Paper2.SourceSupportFrontier Paper2.SourceSupportStep
open Paper2.SourceRemainingConversationNumerics
open Workspace.Types.Protocol

variable {A C I W : Type*} [Fintype A] [Fintype W]

/-- The three local lower bounds of the selected manuscript are given here
on original-law word supports and the actual protocol carrier. The second
bound selects a single Alice child before the capacity and support family
are chosen. It therefore does not assume an overloaded stop or a successful
projection. -/
theorem no_short_actual_protocol
    (μ : Paper2.FiniteLaw W) (input : I → W → C) (F : A → C → Bool)
    (q b ell H : ℕ) (hq : q = 2 ^ ell) (_hq2 : 2 ≤ q)
    (_hb : b < q)
    (initial : State A C I W)
    (hH : 0 < H) (hcount : initial.coordinates.card + b = q)
    (hexcess : b < initial.attachments.card)
    (x : ℝ) (hx : 0 < x) (hsmall : 2 * (q : ℝ) * x ≤ 1 / 8)
    (hcost : initial.protocol.cost ≤ H + ell)
    (hcorrect : ∀ a c, c ∈ initial.columns →
      initial.protocol.eval a c = F a c)
    (hmarked : initial.attachments ⊆ initial.coordinates)
    (hmass : ∀ i ∈ initial.coordinates, (3 / 4 : ℝ) ≤ mass μ (initial.support i))
    (hreaches : ∀ i ∈ initial.coordinates, ∀ w ∈ initial.support i,
      input i w ∈ initial.columns)
    (lowerBeforeAlice : ∀ (U : Set C) (P : Protocol A U Bool),
      P.Computes (fun a u => F a u.val) →
      ∀ (i : I) (S : Finset W),
        (∀ w ∈ S, input i w ∈ U) → x ≤ mass μ S → H ≤ P.cost)
    (lowerAfterAlice : ∀ (U : Set C) (query : A → Bool),
      ∃ bit : Bool, ∀ (k : ℕ), 1 ≤ k → (2 : ℝ) ^ k * x ≤ 1 →
        ∀ (Q : Finset I) (S : I → Finset W),
          2 ^ (k - 1) + 1 ≤ Q.card →
          (∀ i ∈ Q, (2 : ℝ) ^ k * x ≤ mass μ (S i) ∧
            ∀ w ∈ S i, input i w ∈ U) →
          ∀ child : Protocol {a : A // query a = bit} U Bool,
            child.Computes (fun a u => F a.val u.val) →
            H + k ≤ child.cost)
    (lowerMarked : ∀ (U : Set C) (P : Protocol A U Bool),
      P.Computes (fun a u => F a u.val) →
      ∀ i ∈ initial.attachments, ∀ S : Finset W,
        S ⊆ initial.support i →
        (∀ w ∈ S, input i w ∈ U) →
        (1 / 2 : ℝ) < mass μ S → H + 1 ≤ P.cost) :
    False := by
  classical
  let floor := Paper2.SourceSupportSchedule.floor q x
  let T := run μ input floor 0 (ell + 1) initial
  have hfloorSmall : floor 0 ≤ 1 / 8 := by
    simpa only [floor, Paper2.SourceSupportSchedule.floor_zero] using hsmall
  have hmass0 : ∀ i ∈ initial.coordinates, floor 0 ≤ mass μ (initial.support i) := by
    intro i hi
    have := hmass i hi
    linarith
  have hm := run_mass_floors μ input floor
    (fun r => (Paper2.SourceSupportSchedule.twice_next q x r).symm)
    (3 / 4 - floor 0) 0 (ell + 1) initial hmass0
    (fun i hi => by simpa only [sub_add_cancel] using hmass i (hmarked hi))
  have hr := run_support_reaches μ input floor 0 (ell + 1) initial hreaches
  have hs := run_sets_subset μ input floor 0 (ell + 1) initial
  have hz := run_attachments_subset μ input floor 0 (ell + 1) initial hmarked
  have hbase (v : Active T) :
      H ≤ (T.state v.val).protocol.cost := by
    let node := T.state v.val
    obtain ⟨i, hi⟩ := v.property
    have hpath := run_bobPath μ input floor 0 (ell + 1) initial v.val
    let P := Workspace.UpperBound.Protocol.comap id
      (fun u : node.columns => u.val) node.protocol
    have hP : P.Computes (fun a u => F a u.val) := by
      intro a u
      rw [Workspace.UpperBound.Protocol.comap_eval]
      exact (hpath.eval_eq a u.val u.property).trans
        (hcorrect a u.val (hpath.columns_subset u.property))
    have hfloor : x ≤ floor (T.route v.val).length := by
      have hlength := (run_stopping μ input floor 0 (ell + 1) initial v.val).1
      dsimp only [floor]
      rw [hq]
      exact Paper2.SourceSupportSchedule.threshold_le_floor hx.le hlength
    have hword : x ≤ mass μ (node.support i) :=
      hfloor.trans (by simpa only [zero_add] using (hm v.val).1 i hi)
    have hreach : ∀ w ∈ node.support i, input i w ∈ node.columns :=
      hr v.val i hi
    have hl := lowerBeforeAlice node.columns P hP i (node.support i) hreach hword
    simpa only [P, Workspace.UpperBound.Protocol.comap_cost] using hl
  have hdepth (v : Active T) : (T.route v.val).length ≤ ell := by
    have hpath := run_bobPath μ input floor 0 (ell + 1) initial v.val
    have hb := hpath.cost_add_length
    have hl := hbase v
    change (T.state v.val).protocol.cost + (T.route v.val).length ≤
      initial.protocol.cost at hb
    omega
  obtain ⟨v, hover⟩ := run_conserved_overload μ input floor (ell + 1)
    initial hmarked q b hcount hexcess
  change (q : ℝ) / (2 : ℝ) ^ (T.route v.val).length <
    ((T.state v.val).coordinates.card : ℝ) +
      ((T.state v.val).attachments.card : ℝ) at hover
  let node := T.state v.val
  let depth := (T.route v.val).length
  let k := ell - depth
  have hcap : (q : ℝ) / (2 : ℝ) ^ depth = (2 : ℝ) ^ k :=
    capacity_eq_pow hq (hdepth v)
  rw [hcap] at hover
  have hnat : 2 ^ k < node.coordinates.card + node.attachments.card := by
    exact_mod_cast hover
  have hsubset : node.attachments ⊆ node.coordinates := hz v.val
  have hmarkCount : node.attachments.card ≤ node.coordinates.card :=
    Finset.card_le_card hsubset
  have hpath := run_bobPath μ input floor 0 (ell + 1) initial v.val
  change BobPath initial.protocol initial.columns (T.route v.val)
    node.protocol node.columns at hpath
  have hstop := run_stopping μ input floor 0 (ell + 1) initial v.val
  have hnonbob : NonBob node.protocol := by
    change depth ≤ ell + 1 ∧ (depth = ell + 1 ∨ NonBob node.protocol) at hstop
    rcases hstop.2 with hfull | hnb
    · have hd := hdepth v
      change depth ≤ ell at hd
      omega
    · exact hnb
  have hAlice : ∃ query left right,
      node.protocol = Protocol.aNode query left right := by
    cases he : node.protocol with
    | leaf value =>
        have hpositive : H ≤ node.protocol.cost := hbase v
        simp only [he, Protocol.cost] at hpositive
        omega
    | aNode query left right => exact ⟨query, left, right, rfl⟩
    | bNode query left right => simp only [he, NonBob] at hnonbob
  let P := Workspace.UpperBound.Protocol.comap id
    (fun u : node.columns => u.val) node.protocol
  have hP : P.Computes (fun a u => F a u.val) := by
    intro a u
    rw [Workspace.UpperBound.Protocol.comap_eval]
    exact (hpath.eval_eq a u.val u.property).trans
      (hcorrect a u.val (hpath.columns_subset u.property))
  have hPcost : P.cost ≤ H + k := by
    have hc := hpath.cost_add_length
    have hc' : node.protocol.cost ≤ H + k := by omega
    simpa only [P, Workspace.UpperBound.Protocol.comap_cost] using hc'
  obtain ⟨query, left, right, hAlice⟩ := hAlice
  let left' := Workspace.UpperBound.Protocol.comap id
    (fun u : node.columns => u.val) left
  let right' := Workspace.UpperBound.Protocol.comap id
    (fun u : node.columns => u.val) right
  have hPnode : P = Protocol.aNode query left' right' := by
    simp only [P, hAlice, Workspace.UpperBound.Protocol.comap, id_eq,
      left', right']
  have hPcompute : (Protocol.aNode query left' right').Computes
      (fun a u => F a u.val) := hPnode ▸ hP
  obtain ⟨bit, hbit⟩ := lowerAfterAlice node.columns query
  let child : Protocol {a : A // query a = bit} node.columns Bool :=
    Workspace.UpperBound.Protocol.comap
      (fun (a : {a : A // query a = bit}) => a.val) id
      (if bit then right' else left')
  have hchildComputes : child.Computes
      (fun (a : {a : A // query a = bit}) (u : node.columns) =>
        F a.val u.val) := by
    intro a u
    have hp := hPcompute a.val u
    rw [Protocol.eval, a.property] at hp
    change (Workspace.UpperBound.Protocol.comap
      (fun (a : {a : A // query a = bit}) => a.val) id
      (if bit then right' else left')).eval a u = F a.val u.val
    rw [Workspace.UpperBound.Protocol.comap_eval]
    cases bit <;> simpa using hp
  have hchildCost : child.cost = (if bit then right' else left').cost :=
    Workspace.UpperBound.Protocol.comap_cost
      (fun (a : {a : A // query a = bit}) => a.val) id
      (if bit then right' else left')
  have hchild : (if bit then right' else left').cost + 1 ≤ P.cost := by
    rw [hPnode]
    cases bit with
    | false =>
        simp only [Bool.false_eq_true, if_false, Protocol.cost]
        have := Nat.le_max_left left'.cost right'.cost
        omega
    | true =>
        simp only [if_true, Protocol.cost]
        have := Nat.le_max_right left'.cost right'.cost
        omega
  have hfloor : floor depth = 2 * (2 : ℝ) ^ k * x := by
    dsimp only [floor]
    rw [hq]
    exact Paper2.SourceSupportSchedule.floor_capacity ell depth x (hdepth v)
  have hsupport (i : I) (hi : i ∈ node.coordinates) :
      (2 : ℝ) ^ k * x ≤ mass μ (node.support i) := by
    have hm' := (hm v.val).1 i hi
    simp only [zero_add] at hm'
    rw [hfloor] at hm'
    have : 0 ≤ (2 : ℝ) ^ k * x := by positivity
    linarith
  have hreached (i : I) (hi : i ∈ node.coordinates) :
      ∀ w ∈ node.support i, input i w ∈ node.columns := hr v.val i hi
  by_cases hk : 1 ≤ k
  · have hblocks : 2 ^ (k - 1) + 1 ≤ node.coordinates.card := by
      have hp : 2 ^ k = 2 * 2 ^ (k - 1) := by
        conv_lhs => rw [show k = k - 1 + 1 by omega]
        rw [pow_succ]
        omega
      omega
    have hscale : (2 : ℝ) ^ k * x ≤ 1 := by
      have hs' := capacity_scale hx.le hfloorSmall hq (hdepth v)
      exact hs'.1
    have hl := hbit k hk hscale node.coordinates node.support hblocks
      (fun i hi => ⟨hsupport i hi, hreached i hi⟩) child hchildComputes
    omega
  · have hkzero : k = 0 := by omega
    have hcountOne : 1 < node.coordinates.card + node.attachments.card := by
      simpa only [hkzero, pow_zero] using hnat
    by_cases hmany : 2 ≤ node.coordinates.card
    · have hscale : (2 : ℝ) ^ 1 * x ≤ 1 := by
        have hs' := capacity_scale hx.le hfloorSmall hq (hdepth v)
        simpa only [pow_one] using hs'.2
      have hblocks : 2 ^ (1 - 1) + 1 ≤ node.coordinates.card := by
        simpa using hmany
      have hrow : ∀ i ∈ node.coordinates,
          (2 : ℝ) ^ 1 * x ≤ mass μ (node.support i) := by
        intro i hi
        simpa only [hkzero, pow_zero, one_mul, pow_one] using
          (by
            have hm' := (hm v.val).1 i hi
            simp only [zero_add] at hm'
            rw [hfloor] at hm'
            change 2 * (2 : ℝ) ^ k * x ≤ mass μ (node.support i) at hm'
            simpa only [hkzero, pow_zero, mul_one] using hm' :
            2 * x ≤ mass μ (node.support i))
      have hl := hbit 1 (by omega) hscale node.coordinates node.support hblocks
        (fun i hi => ⟨hrow i hi, hreached i hi⟩) child hchildComputes
      omega
    · have hsingle : node.coordinates.card = 1 ∧
          node.attachments.card = 1 := by omega
      obtain ⟨i, hi⟩ := Finset.card_pos.mp
        (show 0 < node.attachments.card by omega)
      have hmassMark : (1 / 2 : ℝ) < mass μ (node.support i) :=
        Paper2.SourceSupportSchedule.attachment_mass_gt_half hx.le hfloorSmall
          (by simpa only [zero_add] using (hm v.val).2 i hi)
      have hsubsetInitial := (hs v.val).2.1 hi
      have hwordSubset := (hs v.val).2.2 i
      have hreach := hreached i (hsubset hi)
      have hl := lowerMarked node.columns P hP i hsubsetInitial
        (node.support i) hwordSubset hreach hmassMark
      omega

#print axioms no_short_actual_protocol

end CurrentAdditive.V38Collision
