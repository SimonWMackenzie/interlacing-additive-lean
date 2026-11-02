import CurrentAdditive.GeneratedLiveStops
import Paper2.SourceSupportFrontierOverload
import Paper2.SourceRemainingConversationNumerics

/-!
Appendix I `det:near-full`: run the actual Bob-only stopping tree in the
indexed generated matrix. Every overloaded node with at least two surviving
coordinates is excluded by the source-specific Alice cost theorem. The only
remaining outcome is an actual attached single coordinate, its surviving
gamma support of mass above one half, and a correct short parent protocol.
No lower-bound certificate for that outcome is a premise.
-/

namespace CurrentAdditive.DeterministicIndexedMatrix.Sources

open Paper2 Paper2.SourceMatrix Paper2.SourceSupportFrontier
open Paper2.SourceRemainingConversationNumerics
open Workspace.Types.Protocol
open CurrentAdditive.ArbitraryPrefix

variable {X Y I : Type*} [Fintype X] [Fintype Y] [Fintype I]
  [DecidableEq X] [DecidableEq Y]
  {D q₁ q₂ s : ℕ} [NeZero s] [NeZero q₁] [NeZero q₂]
  {μX : PositiveRationalLaw X} {μY : PositiveRationalLaw Y}
  (src : Sources (D := D) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY)

theorem indexed_remaining_conversation_endpoint
    (hD : 8 ≤ D) (R : X → Y → Bool)
    (activity : I → Fin q₂ → Option (Fin s)) (ξ₀ : Tail s Y)
    (H ell : ℕ) (hH : 2 ≤ H) (hq : q₂ = 2 ^ ell)
    (x : ℝ) (hx : 0 < x)
    (hsmall : Paper2.SourceSupportSchedule.floor q₂ x 0 ≤ 1 / 8)
    (hprofile : RestrictionProfile (A src R)
      src.gamma.law.toFiniteLaw
      ((PositiveRationalLaw.uniform (Fin q₁)).prod μX).toFiniteLaw
      x (H : ℤ))
    (p : Fin s) (K : Set src.inner.Label)
    (V : Set (Row (I := I) src))
    (hK : ∀ z ∈ K, Sum.inl (p, z) ∈ V)
    (hKmass : (998/1000 : ℝ) < src.inner.law.toFiniteLaw.prob (· ∈ K))
    (initial : State V (Column src) (Fin q₂) src.gamma.Label)
    (hP : ∀ v : V, ∀ z ∈ initial.columns,
      initial.protocol.eval v z = N src R activity ξ₀ z v.val)
    (hcost : initial.protocol.cost ≤ H + ell)
    (hZ : initial.attachments ⊆ initial.coordinates)
    (b : ℕ) (hcount : initial.coordinates.card + b = q₂)
    (hexcess : 3 * b < initial.attachments.card)
    (hmass : ∀ α ∈ initial.coordinates,
      Paper2.SourceSupportSchedule.floor q₂ x 0 ≤
      Paper2.SourceSupportStep.mass src.gamma.law.toFiniteLaw (initial.support α))
    (hattachMass : ∀ α ∈ initial.attachments, (3/4 : ℝ) ≤
      Paper2.SourceSupportStep.mass src.gamma.law.toFiniteLaw (initial.support α))
    (hreaches : ∀ α ∈ initial.coordinates, ∀ γ ∈ initial.support α,
      Column.diagonal (α, γ) ∈ initial.columns) :
    ∃ α ∈ initial.attachments,
      ∃ W : Finset src.gamma.Label,
        W ⊆ initial.support α ∧
        (1/2 : ℝ) < Paper2.SourceSupportStep.mass src.gamma.law.toFiniteLaw W ∧
        ∃ U' : Set (Column src),
          U' ⊆ initial.columns ∧
          (∀ γ ∈ W, Column.diagonal (α, γ) ∈ U') ∧
          ∃ P : Protocol V U' Bool,
            P.Computes (fun v u => N src R activity ξ₀ u.val v.val) ∧
            P.cost ≤ H := by
  classical
  let law := src.gamma.law.toFiniteLaw
  let input : Fin q₂ → src.gamma.Label → Column src :=
    fun α γ => Column.diagonal (α, γ)
  let floor := Paper2.SourceSupportSchedule.floor q₂ x
  let T := run law input floor 0 (ell + 1) initial
  have hlive := indexed_run_live_stops src hD R activity ξ₀
    H ell (by omega) hq x hx.le hprofile p K V hK (by linarith)
    initial hP hcost hZ hmass hreaches
  change ∀ v : T.Leaves, (T.state v).coordinates.Nonempty →
    H ≤ (T.state v).protocol.cost ∧ (T.route v).length ≤ ell ∧
    ∃ query left right, (T.state v).protocol = Protocol.aNode query left right at hlive
  obtain ⟨v, hdepth, hbig, hover⟩ := run_active_overload_bounded
    law input floor (ell + 1) initial hZ q₂ b ell hcount hexcess
    (fun v => (hlive v.val v.property).2.1)
  let node := T.state v.val
  let depth := (T.route v.val).length
  let k := ell - depth
  change depth ≤ ell at hdepth
  have hcapacity : (q₂ : ℝ) / (2 : ℝ)^depth = (2 : ℝ)^k :=
    capacity_eq_pow hq hdepth
  change 3 * ((q₂ : ℝ) / (2 : ℝ)^depth) / 4 ≤
    (node.coordinates.card : ℝ) at hbig
  change (q₂ : ℝ) / (2 : ℝ)^depth <
    (node.coordinates.card : ℝ) + (node.attachments.card : ℝ) at hover
  rw [hcapacity] at hbig hover
  have hbig' : (3/4 : ℝ) * (2 : ℝ)^k ≤
      (node.coordinates.card : ℝ) := by linarith
  have hp := run_bobPath law input floor 0 (ell + 1) initial v.val
  change BobPath initial.protocol initial.columns (T.route v.val)
    node.protocol node.columns at hp
  have hm := run_mass_floors law input floor
    (fun r => (Paper2.SourceSupportSchedule.twice_next q₂ x r).symm)
    (3/4 - floor 0) 0 (ell + 1) initial hmass
    (fun α hα => by simpa only [sub_add_cancel] using hattachMass α hα) v.val
  change (∀ α ∈ node.coordinates, floor (0 + depth) ≤
      Paper2.SourceSupportStep.mass law (node.support α)) ∧
    (∀ α ∈ node.attachments, 3/4 - floor 0 + floor (0 + depth) ≤
      Paper2.SourceSupportStep.mass law (node.support α)) at hm
  simp only [zero_add] at hm
  have hr := run_support_reaches law input floor 0 (ell + 1) initial hreaches v.val
  change ∀ α ∈ node.coordinates, ∀ γ ∈ node.support α,
    Column.diagonal (α, γ) ∈ node.columns at hr
  have hs := run_sets_subset law input floor 0 (ell + 1) initial v.val
  change node.coordinates ⊆ initial.coordinates ∧
    node.attachments ⊆ initial.attachments ∧
    ∀ α, node.support α ⊆ initial.support α at hs
  have hz := run_attachments_subset law input floor 0 (ell + 1) initial hZ v.val
  change node.attachments ⊆ node.coordinates at hz
  let P := Workspace.UpperBound.Protocol.comap id
    (fun u : node.columns => u.val) node.protocol
  have hPc : P.Computes (fun (row : V) (u : node.columns) =>
      N src R activity ξ₀ u.val row.val) := by
    intro row u
    rw [Workspace.UpperBound.Protocol.comap_eval]
    exact (hp.eval_eq row u.val u.property).trans
      (hP row u.val (hp.columns_subset u.property))
  have hnodecost : node.protocol.cost ≤ H + k :=
    remaining_cost hp.cost_add_length hcost hdepth
  have hPcost : P.cost ≤ H + k := by
    simpa only [P, Workspace.UpperBound.Protocol.comap_cost] using hnodecost
  obtain ⟨query, left, right, hAlice⟩ := (hlive v.val v.property).2.2
  change node.protocol = Protocol.aNode query left right at hAlice
  let left' := Workspace.UpperBound.Protocol.comap id
    (fun u : node.columns => u.val) left
  let right' := Workspace.UpperBound.Protocol.comap id
    (fun u : node.columns => u.val) right
  have hPalice : P = Protocol.aNode query left' right' := by
    simp only [P, hAlice, Workspace.UpperBound.Protocol.comap, id_eq,
      left', right']
  have hf : floor depth = 2 * (2 : ℝ)^k * x := by
    dsimp only [floor]
    rw [hq]
    exact Paper2.SourceSupportSchedule.floor_capacity ell depth x hdepth
  let Rows : Fin q₂ → Set src.gamma.Label :=
    fun α => (node.support α : Set src.gamma.Label)
  have hrow : ∀ α ∈ node.coordinates,
      2 * (2 : ℝ)^k * x ≤ law.prob (· ∈ Rows α) := by
    intro α hα
    have hi := hm.1 α hα
    rw [hf] at hi
    exact hi
  have hreach : ∀ a ∈ rowRectangle node.coordinates Rows,
      Column.diagonal (a.1, a.2) ∈ node.columns := by
    intro a ha
    exact hr a.1 ha.1 a.2 ha.2
  have hscale := capacity_scale hx.le hsmall hq hdepth
  by_cases hk : 2 ≤ k
  · have hcount' := Paper2.SourceSupportSchedule.power_block_count hk hbig'
    have hl := indexed_alice_exact_cost src hD R activity ξ₀ p K
      node.coordinates Rows node.columns V H k x (by omega) hH hx
      hscale.1 hprofile hcount'
      (fun α hα => by have h := hrow α hα; nlinarith [show 0 ≤ (2 : ℝ)^k*x by positivity])
      hKmass hK hreach query left' right'
      (by simpa only [← hPalice] using hPc)
    have hc : (Protocol.aNode query left' right').cost ≤ H + k := by
      simpa only [← hPalice] using hPcost
    omega
  · by_cases hkone : k = 1
    · have hcount' := Paper2.SourceSupportSchedule.two_block_count
        (show (3/4 : ℝ)*2 ≤ (node.coordinates.card : ℝ) by
          simpa [hkone] using hbig')
      have hl := indexed_alice_exact_cost src hD R activity ξ₀ p K
        node.coordinates Rows node.columns V H 1 x (by omega) hH hx
        (by simpa only [pow_one] using hscale.2) hprofile hcount'
        (fun α hα => by
          have h := hrow α hα
          rw [hkone] at h
          norm_num at h
          nlinarith [show 0 ≤ x by positivity])
        hKmass hK hreach query left' right'
        (by simpa only [← hPalice] using hPc)
      have hc : (Protocol.aNode query left' right').cost ≤ H + 1 := by
        simpa only [← hPalice, hkone] using hPcost
      omega
    · have hkzero : k = 0 := by omega
      by_cases hn : 2 ≤ node.coordinates.card
      · have hl := indexed_alice_exact_cost src hD R activity ξ₀ p K
          node.coordinates Rows node.columns V H 1 x (by omega) hH hx
          (by simpa only [pow_one] using hscale.2) hprofile
          (by simpa using hn)
          (fun α hα => by have h := hrow α hα; simpa [hkzero] using h)
          hKmass hK hreach query left' right'
          (by simpa only [← hPalice] using hPc)
        have hc : (Protocol.aNode query left' right').cost ≤ H := by
          simpa only [← hPalice, hkzero, Nat.add_zero] using hPcost
        omega
      · have hoverN : 1 < node.coordinates.card + node.attachments.card := by
          have hoverR : (1 : ℝ) <
              (node.coordinates.card : ℝ) + (node.attachments.card : ℝ) := by
            simpa only [hkzero, pow_zero] using hover
          exact_mod_cast hoverR
        have hsingle := Paper2.SourceSupportSchedule.single_support_attachment
          (by simpa only [hkzero, pow_zero, mul_one] using hbig') hoverN
          (Finset.card_le_card hz) (by omega)
        obtain ⟨α, hα⟩ := Finset.card_pos.mp
          (show 0 < node.attachments.card by omega)
        have hhalf : (1/2 : ℝ) < Paper2.SourceSupportStep.mass law
            (node.support α) :=
          Paper2.SourceSupportSchedule.attachment_mass_gt_half hx.le hsmall
            (hm.2 α hα)
        refine ⟨α, hs.2.1 hα, node.support α, hs.2.2 α,
          hhalf, node.columns, hp.columns_subset, ?_, P, hPc, ?_⟩
        · exact hr α (hz hα)
        · simpa only [hkzero, Nat.add_zero] using hPcost

end CurrentAdditive.DeterministicIndexedMatrix.Sources

#print axioms CurrentAdditive.DeterministicIndexedMatrix.Sources.indexed_remaining_conversation_endpoint
