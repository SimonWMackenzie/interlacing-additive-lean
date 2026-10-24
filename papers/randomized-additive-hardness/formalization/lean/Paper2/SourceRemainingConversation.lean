import Paper2.SourceSupportLiveStops
import Paper2.SourceSupportFrontierOverload
import Paper2.SourceSupportCapacity
import Paper2.SourceRemainingConversationNumerics

/-!
# The remaining conversation in the retained source

Frozen v12 Section 4, `src:near-full`. Starting from actual retained inputs
and one correct short protocol, this theorem runs the actual Bob-only
recursion, proves its live stops and overload, and applies the concrete
Alice-node capacity bounds. Its only unassembled local continuation is
explicit: an original attached coordinate with a surviving word set of
mass greater than one half contradicts an `H`-bit parent protocol. The
scheduled source theorem must discharge that continuation using its actual
collision items, not by assuming a communication lower-bound certificate.
-/

namespace Paper2.SourceRemainingConversation

open SourceMatrix SourceSupportFrontier SourceRemainingConversationNumerics
open Workspace.Types.Protocol

variable {X Y I : Type*} [Fintype X] [Fintype Y] [Fintype I]
variable {q₁ q₂ s : ℕ} [NeZero q₁] [NeZero s]

/-- The generic remaining-conversation contradiction, on the actual
generated stopping tree. The final premise is the explicit attached-witness
continuation, not a premise about the frontier or its capacity lower bounds. -/
theorem remaining_conversation_contradiction
    (μ : PositiveRationalLaw X) (ν : PositiveRationalLaw Y)
    (R : X → Y → Bool) (activity : I → Fin q₂ → Option (Fin s)) (ξ₀ : Tail s Y)
    (H ell : ℕ) (hH : 2 ≤ H) (hq : q₂ = 2 ^ ell) (x : ℝ) (hx : 0 < x)
    (hsmall : SourceSupportSchedule.floor q₂ x 0 ≤ 1 / 8)
    (hprofile : RestrictionProfile (fun (γ : Word q₁ s Y) j => M₁ R j γ)
      (ν.iid (q₁ + s + 1)).toFiniteLaw
      ((PositiveRationalLaw.uniform (Fin q₁)).prod μ).toFiniteLaw x (H : ℤ))
    (p : Fin s) (A : Set (Template q₁ q₂ X)) (V : Set (RawRow q₁ q₂ s X I))
    (hA : ∀ z ∈ A, Sum.inl (p, z) ∈ V)
    (hAmass : (998 / 1000 : ℝ) <
      (SourceLaws.templateLaw μ q₁ q₂).toFiniteLaw.prob (· ∈ A))
    (initial : State V (TaggedColumn q₁ q₂ s Y) (Fin q₂) (Word q₁ s Y))
    (hP : ∀ v : V, ∀ z ∈ initial.columns,
      initial.protocol.eval v z = N R activity ξ₀ z v.val)
    (hcost : initial.protocol.cost ≤ H + ell)
    (hZ : initial.attachments ⊆ initial.coordinates)
    (b : ℕ) (hcount : initial.coordinates.card + b = q₂)
    (hexcess : 3 * b < initial.attachments.card)
    (hmass : ∀ α ∈ initial.coordinates, SourceSupportSchedule.floor q₂ x 0 ≤
      SourceSupportStep.mass (ν.iid (q₁ + s + 1)).toFiniteLaw (initial.support α))
    (hattachMass : ∀ α ∈ initial.attachments, (3 / 4 : ℝ) ≤
      SourceSupportStep.mass (ν.iid (q₁ + s + 1)).toFiniteLaw (initial.support α))
    (hreaches : ∀ α ∈ initial.coordinates, ∀ word ∈ initial.support α,
      TaggedColumn.diagonal (α, word) ∈ initial.columns)
    (hAttached : ∀ α ∈ initial.attachments, ∀ W : Finset (Word q₁ s Y),
      W ⊆ initial.support α →
      (1 / 2 : ℝ) < SourceSupportStep.mass (ν.iid (q₁ + s + 1)).toFiniteLaw W →
      ∀ U : Set (TaggedColumn q₁ q₂ s Y),
      (∀ word ∈ W, TaggedColumn.diagonal (α, word) ∈ U) →
      ∀ P : Protocol V U Bool,
      P.Computes (fun v u => N R activity ξ₀ u.val v.val) → P.cost ≤ H → False) :
    False := by
  classical
  let law := (ν.iid (q₁ + s + 1)).toFiniteLaw
  let input : Fin q₂ → Word q₁ s Y → TaggedColumn q₁ q₂ s Y :=
    fun α word => TaggedColumn.diagonal (α, word)
  let floor := SourceSupportSchedule.floor q₂ x
  let T := run law input floor 0 (ell + 1) initial
  have hlive := SourceSupportLiveStops.run_live_stops μ ν R activity ξ₀
    H ell (by omega) hq x hx.le hprofile p A V hA (by linarith)
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
  have hcapacity : (q₂ : ℝ) / (2 : ℝ) ^ depth = (2 : ℝ) ^ k :=
    capacity_eq_pow hq hdepth
  change 3 * ((q₂ : ℝ) / (2 : ℝ) ^ depth) / 4 ≤
    (node.coordinates.card : ℝ) at hbig
  change (q₂ : ℝ) / (2 : ℝ) ^ depth <
    (node.coordinates.card : ℝ) + (node.attachments.card : ℝ) at hover
  rw [hcapacity] at hbig hover
  have hbig' : (3 / 4 : ℝ) * (2 : ℝ) ^ k ≤ (node.coordinates.card : ℝ) := by
    linarith
  have hp := run_bobPath law input floor 0 (ell + 1) initial v.val
  change BobPath initial.protocol initial.columns (T.route v.val)
    node.protocol node.columns at hp
  have hm := run_mass_floors law input floor
    (fun r => (SourceSupportSchedule.twice_next q₂ x r).symm)
    (3 / 4 - floor 0) 0 (ell + 1) initial hmass
    (fun α hα => by simpa only [sub_add_cancel] using hattachMass α hα) v.val
  change (∀ α ∈ node.coordinates, floor (0 + depth) ≤
      SourceSupportStep.mass law (node.support α)) ∧
    (∀ α ∈ node.attachments, 3 / 4 - floor 0 + floor (0 + depth) ≤
      SourceSupportStep.mass law (node.support α)) at hm
  simp only [zero_add] at hm
  have hr := run_support_reaches law input floor 0 (ell + 1) initial hreaches v.val
  change ∀ α ∈ node.coordinates, ∀ word ∈ node.support α,
    TaggedColumn.diagonal (α, word) ∈ node.columns at hr
  have hs := run_sets_subset law input floor 0 (ell + 1) initial v.val
  change node.coordinates ⊆ initial.coordinates ∧
    node.attachments ⊆ initial.attachments ∧
    ∀ α, node.support α ⊆ initial.support α at hs
  have hz := run_attachments_subset law input floor 0 (ell + 1) initial hZ v.val
  change node.attachments ⊆ node.coordinates at hz
  let P := Workspace.UpperBound.Protocol.comap id
    (fun u : node.columns => u.val) node.protocol
  have hPc : P.Computes (fun (row : V) (u : node.columns) =>
      N R activity ξ₀ u.val row.val) := by
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
  let e := coordinateEnumeration node.coordinates
  let S := selectedSupport node.coordinates
    (fun α => (node.support α : Set (Word q₁ s Y)))
  have he : Function.Injective e := coordinateEnumeration_injective node.coordinates
  have hS : ∀ a ∈ S, TaggedColumn.diagonal (e a.1, a.2) ∈ node.columns := by
    intro a ha
    exact hr (e a.1) (coordinateEnumeration_mem node.coordinates a.1) a.2 ha
  have hf : floor depth = 2 * (2 : ℝ) ^ k * x := by
    dsimp only [floor]
    rw [hq]
    exact SourceSupportSchedule.floor_capacity ell depth x hdepth
  have hrow : ∀ i, 2 * (2 : ℝ) ^ k * x ≤
      law.prob (fun word => (i, word) ∈ S) := by
    intro i
    have hi := hm.1 (e i) (coordinateEnumeration_mem node.coordinates i)
    rw [hf] at hi
    exact hi
  have hscale := capacity_scale hx.le hsmall hq hdepth
  by_cases hk : 2 ≤ k
  · apply SourceSupportCapacity.alice_power_contradiction μ ν R activity ξ₀
      H k hH hx hk hscale.1 hprofile p e he A S hbig' node.columns V hA hS hrow
      hAmass query left' right'
    · simpa only [← hPalice] using hPc
    · simpa only [← hPalice] using hPcost
  · by_cases hkone : k = 1
    · apply SourceSupportCapacity.alice_capacity_two_contradiction μ ν R activity ξ₀
        H hH hx hscale.2 hprofile p e he A S (by simpa [hkone] using hbig')
        node.columns V hA hS
        (fun i => by simpa only [hkone, pow_one, show (2 : ℝ) * 2 = 4 by norm_num] using hrow i)
        hAmass query left' right'
      · simpa only [← hPalice] using hPc
      · simpa only [← hPalice, hkone] using hPcost
    · have hkzero : k = 0 := by omega
      by_cases hn : 2 ≤ node.coordinates.card
      · apply SourceSupportCapacity.alice_capacity_one_many_contradiction
          μ ν R activity ξ₀ H hH hx hscale.2 hprofile p e he A S hn node.columns V
          hA hS (fun i => by simpa [hkzero] using hrow i) hAmass query left' right'
        · simpa only [← hPalice] using hPc
        · simpa only [← hPalice, hkzero, Nat.add_zero] using hPcost
      · have hoverN : 1 < node.coordinates.card + node.attachments.card := by
          have hoverR : (1 : ℝ) <
              (node.coordinates.card : ℝ) + (node.attachments.card : ℝ) := by
            simpa only [hkzero, pow_zero] using hover
          exact_mod_cast hoverR
        have hsingle := SourceSupportSchedule.single_support_attachment
          (by simpa only [hkzero, pow_zero, mul_one] using hbig') hoverN
          (Finset.card_le_card hz) (by omega)
        obtain ⟨α, hα⟩ := Finset.card_pos.mp (show 0 < node.attachments.card by omega)
        have hhalf : (1 / 2 : ℝ) < SourceSupportStep.mass law (node.support α) :=
          SourceSupportSchedule.attachment_mass_gt_half hx.le hsmall (hm.2 α hα)
        exact hAttached α (hs.2.1 hα) (node.support α) (hs.2.2 α) hhalf
          node.columns (hr α (hz hα)) P hPc (by simpa only [hkzero, Nat.add_zero] using hPcost)

end Paper2.SourceRemainingConversation

#print axioms Paper2.SourceRemainingConversation.remaining_conversation_contradiction
