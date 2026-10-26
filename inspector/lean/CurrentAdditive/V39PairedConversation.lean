import CurrentAdditive.V39PairedLiveStops
import Paper2.SourceRemainingConversationNumerics

/-! Actual current res:paired conversation. More than q tagged supports
are conserved along original Bob messages. One stopping Alice node is
strictly overloaded; width twice its capacity works uniformly at capacity
one as well as every larger dyadic capacity. -/

namespace CurrentAdditive.V39PairedConversation

open Paper2 Paper2.PairedSelectorMatrix Paper2.SourceSupportFrontier
open Paper2.SourceRemainingConversationNumerics
open CurrentAdditive.DeterministicIndexedMatrix
open CurrentAdditive.DeterministicIndexedMatrix.Sources
open CurrentAdditive.ArbitraryPrefix
open Workspace.Types.Protocol

variable {X Y I : Type*} [Fintype X] [Fintype Y] [Fintype I]
  [DecidableEq X] [DecidableEq Y]
  {D q₁ q₂ s : ℕ} [NeZero s] [NeZero q₁] [NeZero q₂]
  {μX : PositiveRationalLaw X} {μY : PositiveRationalLaw Y}
  (src : Sources (D := D) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY)

theorem paired_remaining_conversation_contradiction
    (R₀ : X → Y → Bool) (H ell : ℕ) (hH : 2 ≤ H)
    (hq : q₂ = 2^ell) (x : ℝ) (hx : 0 < x) (hD : 8 ≤ D)
    (hsmall : SourceSupportSchedule.floor q₂ x 0 ≤ 1/8)
    (hprofile : V38RestrictionProfiles.TwoThresholdProfile (A src R₀)
      src.gamma.law.toFiniteLaw
      ((PositiveRationalLaw.uniform (Fin q₁)).prod μX).toFiniteLaw x (H : ℤ))
    (K : Set (src.inner.Label × src.inner.Label))
    (hK : (49/64 : ℝ) ≤
      (src.inner.law.toFiniteLaw.prod src.inner.law.toFiniteLaw).prob (· ∈ K))
    (initial : State K (Column q₂ src.gamma.Label) (Bool × Fin q₂) src.gamma.Label)
    (hP : ∀ z : K, ∀ c ∈ initial.columns,
      initial.protocol.eval z c = pairedIndexed src R₀ z.val (c.1.1,(c.1.2,c.2)))
    (hcost : initial.protocol.cost ≤ H+ell)
    (hmarks : initial.attachments = ∅) (hcount : q₂ < initial.coordinates.card)
    (hmass : ∀ a ∈ initial.coordinates, SourceSupportSchedule.floor q₂ x 0 ≤
      SourceSupportStep.mass src.gamma.law.toFiniteLaw (initial.support a))
    (hreaches : ∀ a ∈ initial.coordinates, ∀ γ ∈ initial.support a,
      (a,γ) ∈ initial.columns) : False := by
  classical
  let law := src.gamma.law.toFiniteLaw
  let input : (Bool × Fin q₂) → src.gamma.Label → Column q₂ src.gamma.Label :=
    fun a γ => (a,γ)
  let floor := SourceSupportSchedule.floor q₂ x
  let T := run law input floor 0 (ell+1) initial
  have hlive := V39PairedLiveStops.paired_run_live_stops src R₀ H ell hH hq x hx.le
    (by omega) hprofile K hK initial hP hmarks hcost hmass hreaches
  change ∀ v : T.Leaves, (T.state v).coordinates.Nonempty →
    H ≤ (T.state v).protocol.cost ∧ (T.route v).length ≤ ell ∧
    ∃ query left right, (T.state v).protocol = Protocol.aNode query left right at hlive
  obtain ⟨v,hover⟩ := V39UnmarkedFrontier.run_overload law input floor
    0 (ell+1) initial hmarks q₂ hcount
  let node := T.state v.val
  let depth := (T.route v.val).length
  let k := ell-depth
  have hdepth : depth ≤ ell := (hlive v.val v.property).2.1
  have hcapacity : (q₂ : ℝ)/(2 : ℝ)^depth = (2 : ℝ)^k :=
    capacity_eq_pow hq hdepth
  change (q₂ : ℝ)/(2 : ℝ)^depth < (node.coordinates.card : ℝ) at hover
  rw [hcapacity] at hover
  have hcountN : 2^k+1 ≤ node.coordinates.card := by
    have hn : 2^k < node.coordinates.card := by exact_mod_cast hover
    omega
  have hp := run_bobPath law input floor 0 (ell+1) initial v.val
  change BobPath initial.protocol initial.columns (T.route v.val)
    node.protocol node.columns at hp
  have hm := run_mass_floors law input floor
    (fun r => (SourceSupportSchedule.twice_next q₂ x r).symm)
    0 0 (ell+1) initial hmass (by simp [hmarks]) v.val
  have hr := run_support_reaches law input floor 0 (ell+1) initial hreaches v.val
  change ∀ a ∈ node.coordinates, ∀ γ ∈ node.support a, (a,γ) ∈ node.columns at hr
  let P := Workspace.UpperBound.Protocol.comap id (fun c : node.columns => c.val)
    node.protocol
  have hPc : P.Computes (fun (z : K) (c : node.columns) =>
      pairedIndexed src R₀ z.val (c.val.1.1,(c.val.1.2,c.val.2))) := by
    intro z c
    rw [Workspace.UpperBound.Protocol.comap_eval]
    exact (hp.eval_eq z c.val c.property).trans
      (hP z c.val (hp.columns_subset c.property))
  have hPcost : P.cost ≤ H+k := by
    simpa only [P,Workspace.UpperBound.Protocol.comap_cost] using
      remaining_cost hp.cost_add_length hcost hdepth
  obtain ⟨query,left,right,hAlice⟩ := (hlive v.val v.property).2.2
  change node.protocol = Protocol.aNode query left right at hAlice
  let left' := Workspace.UpperBound.Protocol.comap id
    (fun c : node.columns => c.val) left
  let right' := Workspace.UpperBound.Protocol.comap id
    (fun c : node.columns => c.val) right
  have hPalice : P = Protocol.aNode query left' right' := by
    simp only [P,hAlice,Workspace.UpperBound.Protocol.comap,id_eq,left',right']
  let Q := node.coordinates
  let e : Fin Q.card → Bool × Fin q₂ := fun i => (Q.equivFin.symm i).val
  have he : Function.Injective e := by
    intro i j hij
    exact Q.equivFin.symm.injective (Subtype.ext hij)
  have he_mem (i : Fin Q.card) : e i ∈ node.coordinates :=
    (Q.equivFin.symm i).property
  let Rows : Fin Q.card → Set src.gamma.Label := fun i => node.support (e i)
  have hRows : ∀ i : Fin Q.card, ∀ γ ∈ Rows i, (e i,γ) ∈ node.columns := by
    intro i γ hγ
    exact hr (e i) (he_mem i) γ hγ
  have hf : floor depth = (2 : ℝ)^(k+1)*x := by
    change SourceSupportSchedule.floor q₂ x depth = _
    rw [hq,SourceSupportSchedule.floor_capacity ell depth x hdepth,pow_succ]
    ring
  have hrow : ∀ i : Fin Q.card,
      (2 : ℝ)^(k+1)*x ≤ law.prob (· ∈ Rows i) := by
    intro i
    have hi := hm.1 (e i) (he_mem i)
    simp only [zero_add] at hi
    change floor depth ≤ law.prob (· ∈ Rows i) at hi
    rwa [hf] at hi
  have hscale : (2 : ℝ)^(k+1)*x ≤ 1 := by
    have ht := (SourceSupportSchedule.floor_antitone hx.le (Nat.zero_le depth)).trans hsmall
    change floor depth ≤ 1/8 at ht
    rw [hf] at ht
    linarith
  have hl := V39PairedTerminals.selected_paired_alice_cost src R₀ H (k+1) Q.card x
    hD (by omega) hH hx hscale hprofile e he (by simpa using hcountN) Rows hrow
    K hK node.columns hRows query left' right'
    (by simpa only [← hPalice] using hPc)
  have hu : (Protocol.aNode query left' right').cost ≤ H+k := by
    simpa only [← hPalice] using hPcost
  omega

end CurrentAdditive.V39PairedConversation

#print axioms CurrentAdditive.V39PairedConversation.paired_remaining_conversation_contradiction
