import CurrentAdditive.V39IndexedTwoFamilyOwnerFrontier
import CurrentAdditive.V39IndexedTwoFamilyRunConservation
import CurrentAdditive.V39IndexedOwnerObstructions
import CurrentAdditive.V39SharedReceiptJoin
import CurrentAdditive.V39IncomingBob
import CurrentAdditive.V39IncomingGuard

/-! Common internal-interlace contradiction for the actual indexed
two-tag matrix. The one retained event determines one exceptional set;
its physical frontier supplies both receiving estimates and conservation. -/

namespace CurrentAdditive.V39IndexedAlignmentProtocol

open Paper2 Paper2.SourceMatrix Paper2.ReferenceOwners
open Paper2.ReferenceCertificates Paper2.ReferenceCertificateTree
open Paper2.ReferenceCertificateProtocol
open CurrentAdditive.DeterministicIndexedMatrix
open CurrentAdditive.DeterministicIndexedMatrix.Sources
open CurrentAdditive.V39IndexedTwoFamilyRun
open scoped BigOperators Classical

variable {G V Aux X Y : Type*}
  [Fintype G] [Fintype V] [Fintype Aux] [Fintype X] [Fintype Y]
  [DecidableEq G] [DecidableEq V] [DecidableEq Aux] [DecidableEq X] [DecidableEq Y]
  {q₁ q₂ s w : ℕ} [NeZero q₁] [NeZero q₂] [NeZero s]
  {μX : PositiveRationalLaw X} {μY : PositiveRationalLaw Y}
  (src : Sources (D := 8192) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY)
  (μI : PositiveRationalLaw (G × (V ⊕ Aux)))
  (streams : InternalStreams src μI w)

theorem protocol_impossible
    (R₀ : X → Y → Bool) (activity : (G × (V ⊕ Aux)) → Fin q₂ → Option (Fin s))
    (ξ₀ : Tail s Y) (H ell b r e0 : ℕ) (x θ η : ℝ)
    (hH : 2 ≤ H) (hr : 2 ≤ r) (hwr : w=2^r) (hq : q₂=2^ell) (hs : s=2^b)
    (hx : 0 < x) (hθ : 0 < θ) (hη : 0 < η)
    (hA : V38RestrictionProfiles.TwoThresholdProfile (A src R₀)
      src.gamma.law.toFiniteLaw
      ((PositiveRationalLaw.uniform (Fin q₁)).prod μX).toFiniteLaw x (H : ℤ))
    (hT : V38RestrictionProfiles.TwoThresholdProfile (T src R₀)
      src.inner.law.toFiniteLaw
      ((PositiveRationalLaw.uniform (Fin q₂)).prod src.gamma.law).toFiniteLaw
      x ((H+ell : ℕ) : ℤ))
    (href : V38RestrictionProfiles.TwoThresholdProfile (Nref src R₀ activity ξ₀)
      (ordinaryLaw src).toFiniteLaw (rowLaw src μI).toFiniteLaw x ((H+ell+b : ℕ) : ℤ))
    (hnearfull : ∀ (U : Set (V38IndexedTwoTag.Column src)) (Z : Set (Row (I := G × (V ⊕ Aux)) src)),
      1-η ≤ (V38IndexedTwoTag.law src).toFiniteLaw.prob (· ∈ U) →
      1-η ≤ (rowLaw src μI).toFiniteLaw.prob (· ∈ Z) →
      H+ell+b+1 ≤ Compression.restrictionD (V38IndexedTwoTag.matrix src R₀ activity ξ₀) U Z)
    (hcap : V38Moments.exceptionCount θ (η/2) ≤ e0)
    (hexc : 4*(2*e0) ≤ w)
    (hexcReceipt : (512*(1/256 : ℝ)*(r+2)*s)*(2*e0) ≤ η*w/16)
    (hinit : 2*(w : ℝ)*x+η/(16*(255/256 : ℝ)) ≤ 1)
    (hwx : (w : ℝ)*x ≤ 1) (h2x : 2*x ≤ 1)
    (hloss : 2*(w : ℝ)^2*x ≤ η/(16*(255/256 : ℝ)))
    (hwidth : (w : ℝ)^2*q₂*x ≤ 1)
    (hforeignWidth : 4*(1/256 : ℝ)*w*q₂*x ≤ η/32)
    (hfloor : 2*s*x ≤ 1-η*(s : ℝ)/(2*(255/256 : ℝ)))
    (hpairMargin : 49/64+2*s*x <
      ((99/100 : ℝ)+(255/256 : ℝ)^2-1)/(255/256 : ℝ)^2)
    (hsmall : 2*s*x ≤ 1/8) (hpairSmall : 2*q₂*x ≤ 1/8)
    (hflag : V39IncomingGuard.flagConstant/(s : ℝ)^128 ≤ θ/4)
    (hException : V38Moments.exceptionCount (θ/4) 1 ≤ s*q₂)
    (R : Set (Rows src (w := w))) (Yevent : Set (InternalLabel src streams))
    (P : Workspace.Types.Protocol.Protocol (Rows src (w := w)) (InternalLabel src streams) Bool)
    (hR : 1-η/(16*w) ≤ (firstRowLaw src (by rw [hwr]; positivity)).prob (· ∈ R))
    (hY : θ ≤ streams.law.toFiniteLaw.prob (· ∈ Yevent))
    (hcompute : ∀ row ∈ R, ∀ t ∈ Yevent,
      P.eval row t=V39OwnerLocalCost.internalMatrix src streams R₀ activity ξ₀ row t)
    (hbudget : P.cost ≤ (H+ell+b+1)+r-1) : False := by
  classical
  have hw : 0 < w := by rw [hwr]; positivity
  have hw2 : 2 ≤ w := by
    rw [hwr]
    exact le_trans (by norm_num : 2 ≤ 2^2) (Nat.pow_le_pow_right (by omega) hr)
  have hθ1 : θ ≤ 1 := hY.trans (streams.law.toFiniteLaw.prob_le_one _)
  have hwise := internal_streams_row_dwise src μI streams
  obtain ⟨E,hE,hTV,hsingle,hpair,hforeign⟩ :=
    V39SharedReceiptJoin.choose_exception_before_nodes src μI streams R₀ activity ξ₀
      Yevent H ell b hH hq hs x θ η hx hθ hη hY hA hT hfloor hpairMargin hsmall hpairSmall
  have hTVold : ∀ J : Finset (Fin w), J ⊆ Finset.univ \ E → J.card ≤ 8 →
      projectionTV (condition streams.law.toFiniteLaw (· ∈ Yevent) (hθ.trans_le hY))
        (rowLaw src μI).toFiniteLaw (InternalStreams.decode src streams) J ≤
        V38Moments.epsilon θ (η/2) := by
    simpa only [V39SharedConditioning.epsilon_eq_R1024] using hTV
  obtain ⟨hfinal,hbob⟩ := V39IndexedOwnerObstructions.local_obstructions src streams
    (rowLaw src μI) R₀ activity ξ₀ R Yevent P E (H+ell+b) r η x θ (η/2)
    hw hwr (by omega) hx hθ hθ1 (by linarith) hR hinit hwx h2x hY href hwise hTVold
    hcompute (by omega)
  let st := initialState src R P E r
  let μ := (ordinaryLaw src).toFiniteLaw
  let floor := ReferenceSchedule.floor w x
  let tr := run μ (input src) floor 0 r st
  let F := fun v : tr.Leaves => (tr.state v).family
  let final := fun v : tr.Leaves => (tr.route v).length=r
  let O := ownerNodes F final
  let orig : tr.Leaves → Fin w := fun v =>
    if hv : v ∈ O then origin F final ⟨v,hv⟩ else ⟨0,hw⟩
  have horig (v : tr.Leaves) (hv : v ∈ O) :
      orig v=origin F final ⟨v,hv⟩ := by simp only [orig,dif_pos hv]
  have hinj : Function.Injective (fun v : O => orig v.val) := by
    intro a b hab
    apply run_origin_injective μ (input src) floor r st
    simpa only [horig a.val a.property,horig b.val b.property] using hab
  have hout (v : tr.Leaves) (hv : v ∈ O) : orig v ∉ E := by
    rw [horig v hv]
    exact (Finset.mem_sdiff.mp (run_origin_mem_initial μ (input src) floor r st ⟨v,hv⟩)).2
  have hprojection : ∀ i ∉ E,
      1-η ≤ (rowLaw src μI).toFiniteLaw.prob
        (· ∈ V39OwnerSourceCost.projection (InternalStreams.decode src streams) Yevent i) := by
    intro i hi
    have hh := hsingle i hi
    change 1-η ≤ (rowLaw src μI).toFiniteLaw.prob
      (· ∈ (fun t => InternalStreams.decode src streams t i) '' Yevent)
    linarith
  obtain ⟨hcount,hcountle,hexcapacity,hownloss,hmiss⟩ :=
    V39IndexedTwoFamilyOwnerFrontier.owner_frontier src (rowLaw src μI).toFiniteLaw
      (V38IndexedTwoTag.matrix src R₀ activity ξ₀) (InternalStreams.decode src streams)
      Yevent R P E r e0 (H+ell+b+1) η x hw hwr (by omega) (hE.trans hcap)
      hexc hx.le hR hloss hnearfull hprojection hcompute hbudget hfinal hbob
  have hnode (v : tr.Leaves) : ∀ row ∈ (tr.state v).rows, ∀ t ∈ Yevent,
      (tr.state v).protocol.eval row t=
        V39IndexedIncomingLocal.internal src streams R₀ activity ξ₀ row t := by
    apply ReferenceRunCorrectness.computes_on_original_rectangle μ (input src) floor
      0 r st (V39IndexedIncomingLocal.internal src streams R₀ activity ξ₀) Yevent _ v
    intro row hr t ht
    rw [show st.protocol=ReferencePrefix.padAlicePrefix r P from rfl,
      ReferencePrefix.padAlicePrefix_eval]
    exact hcompute row hr t ht
  have hpad : st.protocol.cost ≤ (H+ell+b)+r :=
    (ReferencePrefix.padAlicePrefix_cost_le r P).trans (max_le (by omega) (by omega))
  have hcost (v : tr.Leaves) : (tr.state v).protocol.cost ≤
      (H+ell+b)+(r-(tr.route v).length) :=
    ReferenceRunCorrectness.remaining_cost μ (input src) floor r (H+ell+b) st hpad v
  have hdepth (v : tr.Leaves) : (tr.route v).length ≤ r :=
    ReferenceRunCorrectness.depth_le μ (input src) floor 0 r st v
  let I₀ := O.image orig
  have hsum (v : tr.Leaves) :
      (∑ d ∈ O, (1/256 : ℝ)*(diagonalLaw src).toFiniteLaw.prob
        (fun j => (orig d,.inr j) ∈ (tr.state v).rows)) =
      ∑ i ∈ I₀, V39IncomingDensity.receipt (diagonalLaw src).toFiniteLaw w (tr.state v).rows i := by
    dsimp only [I₀,V39IncomingDensity.receipt]
    rw [Finset.sum_image]
    intro a ha b hb hab
    exact congrArg Subtype.val (hinj (show orig (⟨a,ha⟩ : O).val=orig (⟨b,hb⟩ : O).val from hab))
  let K : ℝ := 512*(1/256 : ℝ)*(r+2)*s
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hincoming (v : tr.Leaves) :
      (∑ d ∈ O, (1/256 : ℝ)*(diagonalLaw src).toFiniteLaw.prob
        (fun j => (orig d,.inr j) ∈ (tr.state v).rows)) ≤ K*(2^(r-(tr.route v).length) : ℕ) := by
    rw [hsum]
    let k := r-(tr.route v).length
    let a := 1+b+k+ell
    have hpow : 2^a=2*s*(2^k)*q₂ := by
      dsimp only [a]; rw [hs,hq]; simp only [pow_add,pow_one]
    have hguard := V39IncomingGuard.destination_guard s (2^k) θ (NeZero.pos s)
      (by have hh := Nat.two_pow_pos k; omega) hflag
    by_cases hv : (tr.route v).length=r
    · have hn := V39OwnerLocalCost.owner_node_restriction_le_protocol src streams
        R₀ activity ξ₀ (tr.state v).rows Yevent (tr.state v).protocol (hnode v)
      change Compression.restrictionD (V39IndexedIncomingLocal.internal src streams R₀ activity ξ₀)
        (tr.state v).rows Yevent ≤ (tr.state v).protocol.cost at hn
      have hlocal : Compression.restrictionD
          (V39IndexedIncomingLocal.internal src streams R₀ activity ξ₀) (tr.state v).rows Yevent < H+a := by
        have hc := hcost v
        dsimp only [a,k]
        rw [hv] at hc ⊢
        omega
      have hh := V39IncomingSharpBound.incoming_diagonal_mass_lt src streams
        r (2^k) H a x θ (tr.state v).rows I₀ Yevent R₀ activity ξ₀
        hwr (by have hh:=Nat.two_pow_pos k; omega) (by dsimp [a]; omega) hH hpow hx hθ hwidth hA
        (by linarith) hguard hException hlocal
      exact hh.le
    · obtain ⟨hk,query,left,right,heq⟩ :=
        ReferenceRunCorrectness.before_depth_is_bob μ (input src) floor r st
          (ReferencePrefix.padAlicePrefix_noEarlyLeaf r P) v hv
      have hc : (Workspace.Types.Protocol.Protocol.bNode query left right).cost ≤ H+a := by
        rw [← heq]
        change (tr.state v).protocol.cost ≤ H+a
        have hh:=hcost v
        dsimp only [a,k]
        omega
      have hcomp : ∀ row ∈ (tr.state v).rows, ∀ t ∈ Yevent,
          (Workspace.Types.Protocol.Protocol.bNode query left right).eval row t=
            V39IndexedIncomingLocal.internal src streams R₀ activity ξ₀ row t := by
        rw [← heq]; exact hnode v
      exact (V39IncomingBob.first_bob_diagonal_mass_lt src streams
        r (2^k) H a x θ (tr.state v).rows I₀ Yevent R₀ activity ξ₀ query left right
        hwr (by have hh:=Nat.two_pow_pos k; omega) (by dsimp [a]; omega) hH hpow hx hθ hwidth hA hY
        hguard hException hcomp hc).le
  apply V39IndexedTwoFamilyRunConservation.contradiction src st r η x K q₂ hw2 hη hK
    hR O orig hinj hcount hcountle
  · intro v hv
    simpa only [horig v hv] using hmiss ⟨v,hv⟩
  · have heq : (∑ v ∈ O, (1-μ.prob (fun Z => input src (orig v) Z ∈ (tr.state v).rows))) =
        ∑ v : O, (1-μ.prob (fun Z => input src (origin F final v) Z ∈ (tr.state v.val).rows)) := by
      rw [← Finset.sum_coe_sort]
      apply Finset.sum_congr rfl
      intro v _; rw [horig v.val v.property]
    rw [heq]; exact hownloss
  · intro v _; exact hincoming v
  · have hcapR : (∑ v ∈ Finset.univ \ O,
        ((2^(r-(tr.route v).length) : ℕ) : ℝ)) ≤ (2*e0 : ℕ) := by
      have heq : (∑ v ∈ Finset.univ \ O, 2^(r-(tr.route v).length)) =
          exceptionalCapacity F final (fun v => 2^(r-(tr.route v).length)) := by
        have hset : Finset.univ \ O = Finset.univ.filter (fun v => v ∉ O) := by
          ext v; simp
        rw [hset,Finset.sum_filter]
        unfold exceptionalCapacity
        apply Finset.sum_congr rfl
        intro v _
        by_cases hv : v ∈ O <;> simp only [O] at hv ⊢ <;> simp [hv]
      have hh := heq.le.trans hexcapacity
      exact_mod_cast hh
    have hm := mul_le_mul_of_nonneg_left hcapR hK
    exact hm.trans (by simpa only [K,Nat.cast_mul,Nat.cast_ofNat] using hexcReceipt)
  · intro d hd v hv hne
    have hij : orig v ≠ orig d := by
      intro heq
      have hab := hinj (show orig (⟨v,hv⟩ : O).val=orig (⟨d,hd⟩ : O).val from heq)
      exact hne (congrArg Subtype.val hab).symm
    have hc : Compression.restrictionD (V39TwoTagOwnerEmbedding.actualW src streams R₀ activity ξ₀)
        Yevent (tr.state v).rows ≤ H+ell+b := by
      rw [SourceProjection.restrictionD_transpose]
      exact (V39OwnerLocalCost.owner_node_restriction_le_protocol src streams R₀ activity ξ₀
        (tr.state v).rows Yevent (tr.state v).protocol (hnode v)).trans
        (by have hh:=hcost v; have hf:=((mem_ownerNodes F final v).mp hv).1
            change (tr.route v).length=r at hf; simpa [hf] using hh)
    exact hforeign (tr.state v).rows
      (1-μ.prob (fun Z => input src (orig v) Z ∈ (tr.state v).rows))
      (orig v) (orig d) hij (hout v hv) (hout d hd) (by dsimp [μ,input]; linarith) hc
  · positivity
  · exact hforeignWidth

end CurrentAdditive.V39IndexedAlignmentProtocol

#print axioms CurrentAdditive.V39IndexedAlignmentProtocol.protocol_impossible
