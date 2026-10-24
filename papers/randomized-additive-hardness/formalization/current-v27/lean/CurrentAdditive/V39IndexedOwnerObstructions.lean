import CurrentAdditive.V39IndexedTwoFamilyRun
import CurrentAdditive.V39OwnerLiveLeaf
import Paper2.ReferenceRunCorrectness
import CurrentAdditive.GeneratedOwnerTuple

/-! The local finite-two-threshold theorems are applied to the actual
annotated prefix. Every support, row event and residual budget is derived
from that one run on the original complete-stream event. -/

namespace CurrentAdditive.V39IndexedOwnerObstructions

open Paper2 Paper2.SourceSupportStep Paper2.ReferenceCertificates
open Paper2.ReferenceCertificateTree Paper2.ReferenceCertificateProtocol
open CurrentAdditive.DeterministicIndexedMatrix
open CurrentAdditive.DeterministicIndexedMatrix.Sources
open CurrentAdditive.V39IndexedTwoFamilyRun
open scoped BigOperators Classical

variable {I X Y : Type*} [Fintype I] [Fintype X] [Fintype Y]
  [DecidableEq I] [DecidableEq X] [DecidableEq Y]
  {q₁ q₂ s w : ℕ} [NeZero q₁] [NeZero q₂] [NeZero s]
  {μX : PositiveRationalLaw X} {μY : PositiveRationalLaw Y}
  (src : Sources (D := 8192) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY)
  {μI : PositiveRationalLaw I} (streams : InternalStreams src μI w)

theorem initial_floor
    (R : Set (Rows src (w := w))) (E : Finset (Fin w))
    (η x : ℝ) (hw : 0 < w)
    (hR : 1-η/(16*w) ≤ (firstRowLaw src hw).prob (· ∈ R))
    (hmargin : 2*(w : ℝ)*x+η/(16*(255/256 : ℝ)) ≤ 1) :
    ∀ i ∈ (initialFamily src R E).active,
      ReferenceSchedule.floor w x 0 ≤
        mass (ordinaryLaw src).toFiniteLaw ((initialFamily src R E).support i) := by
  intro i _
  have htotal := reference_initial_defect src hw R E η hR
  have hi : 1-mass (ordinaryLaw src).toFiniteLaw ((initialFamily src R E).support i) ≤
      ∑ j : Fin w, (1-mass (ordinaryLaw src).toFiniteLaw ((initialFamily src R E).support j)) := by
    exact Finset.single_le_sum
      (fun j _ => sub_nonneg.mpr ((ordinaryLaw src).toFiniteLaw.prob_le_one
        (fun Z => Z ∈ (initialFamily src R E).support j)))
      (Finset.mem_univ i)
  rw [ReferenceSchedule.floor_zero]
  linarith

/-- Actual final and first-Bob support bounds, with no local-cost callback.
The same set E and original event are used at every physical node. -/
theorem local_obstructions
    (ν : PositiveRationalLaw (Row (I := I) src))
    (R₀ : X → Y → Bool) (activity : I → Fin q₂ → Option (Fin s))
    (ξ₀ : Paper2.SourceMatrix.Tail s Y)
    (R : Set (Rows src (w := w))) (Yevent : Set (InternalLabel src streams))
    (P : Workspace.Types.Protocol.Protocol (Rows src (w := w))
      (InternalLabel src streams) Bool)
    (E : Finset (Fin w)) (H r : ℕ) (η x θ τ : ℝ)
    (hw : 0 < w) (hwr : w=2^r) (hH : 2 ≤ H) (hx : 0 < x)
    (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hτ : 0 < τ)
    (hR : 1-η/(16*w) ≤ (firstRowLaw src hw).prob (· ∈ R))
    (hmargin : 2*(w : ℝ)*x+η/(16*(255/256 : ℝ)) ≤ 1)
    (hwx : (w : ℝ)*x ≤ 1) (h2x : 2*x ≤ 1)
    (hY : θ ≤ streams.law.toFiniteLaw.prob (· ∈ Yevent))
    (hprofile : V38RestrictionProfiles.TwoThresholdProfile
      (Nref src R₀ activity ξ₀) (ordinaryLaw src).toFiniteLaw
      ν.toFiniteLaw x (H : ℤ))
    (hwise : IsDWise 8192 streams.law.toFiniteLaw
      (InternalStreams.decode src streams) ν.toFiniteLaw)
    (hTV : ∀ J : Finset (Fin w), J ⊆ Finset.univ \ E → J.card ≤ 8 →
      projectionTV (condition streams.law.toFiniteLaw (· ∈ Yevent) (hθ.trans_le hY))
        ν.toFiniteLaw (InternalStreams.decode src streams) J ≤
        V38Moments.epsilon θ τ)
    (hcompute : ∀ row ∈ R, ∀ t ∈ Yevent,
      P.eval row t=V39OwnerLocalCost.internalMatrix src streams R₀ activity ξ₀ row t)
    (hbudget : P.cost ≤ H+r) :
    let st := initialState src R P E r
    let tr := run (ordinaryLaw src).toFiniteLaw (input src) (ReferenceSchedule.floor w x) 0 r st
    (∀ v : tr.Leaves, (tr.route v).length=r → (tr.state v).family.active.card ≤ 1) ∧
    (∀ v : tr.Leaves, (tr.route v).length≠r →
      units (tr.state v).family ≤ 2^(r-(tr.route v).length)) := by
  classical
  dsimp only
  let st := initialState src R P E r
  let μ := (ordinaryLaw src).toFiniteLaw
  let floor := ReferenceSchedule.floor w x
  let tr := run μ (input src) floor 0 r st
  have hinit := initial_floor src R E η x hw hR hmargin
  have hfloor := run_floor μ (input src) floor (ReferenceSchedule.floor_half w x)
    0 r st hinit
  have hreach := run_reaches μ (input src) floor 0 r st (initial_reaches src R E)
  have hvalid := run_valid μ (input src) floor 0 r st (initial_valid src R E)
  have hsets := run_sets_subset μ (input src) floor 0 r st
  have hpad : st.protocol.cost ≤ H+r :=
    (ReferencePrefix.padAlicePrefix_cost_le r P).trans (max_le hbudget (by omega))
  have hnode (v : tr.Leaves) : ∀ row ∈ (tr.state v).rows, ∀ t ∈ Yevent,
      (tr.state v).protocol.eval row t=
        V39OwnerLocalCost.internalMatrix src streams R₀ activity ξ₀ row t := by
    apply ReferenceRunCorrectness.computes_on_original_rectangle μ (input src) floor
      0 r st (V39OwnerLocalCost.internalMatrix src streams R₀ activity ξ₀) Yevent _ v
    intro row hr t ht
    rw [show st.protocol=ReferencePrefix.padAlicePrefix r P from rfl,
      ReferencePrefix.padAlicePrefix_eval]
    exact hcompute row hr t ht
  have hout (v : tr.Leaves) : ∀ i ∈ (tr.state v).family.active, i ∉ E := by
    intro i hi
    exact (Finset.mem_sdiff.mp ((hsets v).1 hi)).2
  have hdepth (v : tr.Leaves) : (tr.route v).length ≤ r :=
    ReferenceRunCorrectness.depth_le μ (input src) floor 0 r st v
  have hcost (v : tr.Leaves) : (tr.state v).protocol.cost ≤ H+(r-(tr.route v).length) :=
    ReferenceRunCorrectness.remaining_cost μ (input src) floor r H st hpad v
  constructor
  · intro v hv
    change (tr.route v).length=r at hv
    refine V39OwnerLocalCost.owner_reference_final_active_le_one src streams
      ν R₀ activity ξ₀ (tr.state v).rows Yevent (tr.state v).family E
      H x θ τ (tr.state v).protocol hH hx h2x hprofile hwise (hout v)
      ?_ (hreach v) hθ hθ1 hY hτ hTV (hnode v) ?_
    · intro i hi
      have hh := hfloor v i hi
      change floor (0+(tr.route v).length) ≤ mass μ ((tr.state v).family.support i) at hh
      rw [Nat.zero_add,show floor (tr.route v).length=2*x by
        dsimp only [floor]; rw [ReferenceSchedule.floor_dyadic x hwr (hdepth v),hv]; simp] at hh
      exact hh
    · simpa only [hv,Nat.sub_self,Nat.add_zero] using hcost v
  · intro v hv
    obtain ⟨ha,query,left,right,hbob⟩ :=
      ReferenceRunCorrectness.before_depth_is_bob μ (input src) floor r st
        (ReferencePrefix.padAlicePrefix_noEarlyLeaf r P) v hv
    let a := r-(tr.route v).length
    have hscale : (2 : ℝ)^a*x ≤ 1 := by
      have hp : (2 : ℝ)^a ≤ w := by
        rw [hwr,Nat.cast_pow,Nat.cast_ofNat]
        exact pow_le_pow_right₀ (by norm_num) (Nat.sub_le _ _)
      exact (mul_le_mul_of_nonneg_right hp hx.le).trans hwx
    have hf : ∀ i ∈ (tr.state v).family.active, (2 : ℝ)^a*x ≤
        (ordinaryLaw src).toFiniteLaw.prob (fun Z => Z ∈ (tr.state v).family.support i) := by
      intro i hi
      have hh := hfloor v i hi
      change floor (0+(tr.route v).length) ≤ mass μ ((tr.state v).family.support i) at hh
      rw [Nat.zero_add,show floor (tr.route v).length=2*(2 : ℝ)^a*x from
        ReferenceSchedule.floor_dyadic x hwr (hdepth v)] at hh
      change (2 : ℝ)^a*x ≤ mass μ ((tr.state v).family.support i)
      nlinarith [show 0 ≤ (2 : ℝ)^a*x by positivity]
    have hc : (Workspace.Types.Protocol.Protocol.bNode query left right).cost ≤ H+a := by
      rw [← hbob]; exact hcost v
    have hcomp : ∀ row ∈ (tr.state v).rows, ∀ t ∈ Yevent,
        (Workspace.Types.Protocol.Protocol.bNode query left right).eval row t=
          V39OwnerLocalCost.internalMatrix src streams R₀ activity ξ₀ row t := by
      rw [← hbob]; exact hnode v
    exact (V39OwnerLocalCost.owner_reference_first_bob_bounds src streams
      ν R₀ activity ξ₀ (tr.state v).rows Yevent (tr.state v).family E
      H a (2^a) x θ τ query left right ha hH hx rfl (hvalid v) hscale hprofile
      hwise (hout v) hf (hreach v) hθ hθ1 hY hτ hTV hcomp hc).2

end CurrentAdditive.V39IndexedOwnerObstructions

#print axioms CurrentAdditive.V39IndexedOwnerObstructions.initial_floor
#print axioms CurrentAdditive.V39IndexedOwnerObstructions.local_obstructions
