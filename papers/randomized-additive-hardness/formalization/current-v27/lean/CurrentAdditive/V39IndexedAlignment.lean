import CurrentAdditive.V39IndexedAlignmentProtocol
import CurrentAdditive.V39IndexedInternalProfile
import Paper2.InterlaceProtocol

/-! The common finite theorem for the same actual indexed W. Source
profiles, source near-full hardness and the current schedule inequalities
are the stated common inputs. No target profile, receipt or frontier
conclusion is an input. -/

namespace CurrentAdditive.V39IndexedAlignment

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

theorem nearfull
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
    (hR : 1-η/(16*w) ≤ (firstRowLaw src (by rw [hwr]; positivity)).prob (· ∈ R))
    (hY : θ ≤ streams.law.toFiniteLaw.prob (· ∈ Yevent)) :
    H+ell+b+1+r ≤ Compression.restrictionD
      (V39TwoTagOwnerEmbedding.actualW src streams R₀ activity ξ₀) Yevent R := by
  classical
  have hw : 0 < w := by rw [hwr]; positivity
  have hw1 : (1 : ℝ) ≤ w := by exact_mod_cast hw
  have hthreshold : 0 < 1-η/(16*w) := by
    have hxw : 0 ≤ 2*(w : ℝ)*x := by positivity
    have hηbound : η ≤ 255/16 := by
      norm_num at hinit
      nlinarith
    have hηw : η < 16*(w : ℝ) := by nlinarith
    have hdiv : η/(16*(w : ℝ)) < 1 :=
      (div_lt_iff₀ (by positivity : (0 : ℝ)<16*w)).2 (by simpa using hηw)
    linarith
  have hRne : R.Nonempty := by
    by_contra hn
    rw [Set.not_nonempty_iff_eq_empty.mp hn] at hR
    simp only [Set.mem_empty_iff_false,FiniteLaw.prob_false] at hR
    linarith
  have hYne : Yevent.Nonempty := by
    by_contra hn
    rw [Set.not_nonempty_iff_eq_empty.mp hn] at hY
    simp only [Set.mem_empty_iff_false,FiniteLaw.prob_false] at hY
    linarith
  let M := V39OwnerLocalCost.internalMatrix src streams R₀ activity ξ₀
  have ht : Compression.restrictionD M R Yevent = Compression.restrictionD
      (V39TwoTagOwnerEmbedding.actualW src streams R₀ activity ξ₀) Yevent R :=
    (SourceProjection.restrictionD_transpose M R Yevent).symm
  by_contra hn
  have hshort : Compression.restrictionD M R Yevent ≤ H+ell+b+1+r-1 := by omega
  let F := fun (row : R) (t : Yevent) => M row.val t.val
  obtain ⟨P,hPc,hP⟩ := Nat.sInf_mem (Workspace.UpperBound.AchievableCosts_nonempty F)
  obtain ⟨Q,hQc,hQ⟩ := ArbitraryPrefix.extend_restriction_protocol R Yevent hRne hYne P
  have hcompute : ∀ row ∈ R, ∀ t ∈ Yevent, Q.eval row t=M row t := by
    intro row hr t ht
    rw [hQ row hr t ht]
    exact hP ⟨row,hr⟩ ⟨t,ht⟩
  have hbudget : Q.cost ≤ H+ell+b+1+r-1 := by
    rw [hQc,hPc]
    exact hshort
  exact V39IndexedAlignmentProtocol.protocol_impossible src μI streams R₀ activity ξ₀ H ell b r e0 x θ η hH hr hwr hq hs hx hθ hη
    hA hT href hnearfull hcap hexc hexcReceipt hinit hwx h2x hloss hwidth hforeignWidth
    hfloor hpairMargin hsmall hpairSmall hflag hException
    R Yevent Q hR hY hcompute hbudget

theorem selector_upper
    (R₀ : X → Y → Bool) (activity : (G × (V ⊕ Aux)) → Fin q₂ → Option (Fin s))
    (ξ₀ : Tail s Y) (C r : ℕ) (hwr : w=2^r)
    (hsource : Workspace.Types.CommComplexity.D
      (V38IndexedTwoTag.matrix src R₀ activity ξ₀) ≤ C) :
    Workspace.Types.CommComplexity.D
      (V39TwoTagOwnerEmbedding.actualW src streams R₀ activity ξ₀) ≤ C+r := by
  subst w
  let N := V38IndexedTwoTag.matrix src R₀ activity ξ₀
  have hfull : Workspace.Types.CommComplexity.D
      (fun (t : Fin (2^r) → Row (I := G × (V ⊕ Aux)) src)
        (row : Fin (2^r) × V38IndexedTwoTag.Column src) => N row.2 (t row.1)) ≤ r+C := by
    rw [Paper2.transpose_D]
    exact (fullInterlace_two_pow_D_le N r).trans (Nat.add_le_add_left hsource r)
  have hp := Workspace.ProofLemmas.SublemmaPrecompNoIncrease
    (fun (t : Fin (2^r) → Row (I := G × (V ⊕ Aux)) src)
      (row : Fin (2^r) × V38IndexedTwoTag.Column src) => N row.2 (t row.1))
    (InternalStreams.decode src streams) id
  exact (hp.trans hfull).trans_eq (Nat.add_comm r C)

theorem alignment
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
    (hθ1 : θ ≤ 1) (he : V38Moments.exceptionCount θ 1 ≤ w/128)
    (hwxProfile : (w : ℝ)*x < 1/256)
    (hsourceUpper : Workspace.Types.CommComplexity.D
      (V38IndexedTwoTag.matrix src R₀ activity ξ₀) ≤ H+ell+b+1) :
    Workspace.Types.CommComplexity.D
      (V39TwoTagOwnerEmbedding.actualW src streams R₀ activity ξ₀) = H+ell+b+1+r ∧
    (letI : Nonempty (Fin w) := Fin.pos_iff_nonempty.mp (by rw [hwr]; positivity)
     V38RestrictionProfiles.TwoThresholdProfile
      (V39TwoTagOwnerEmbedding.actualW src streams R₀ activity ξ₀)
      streams.law.toFiniteLaw
      ((PositiveRationalLaw.uniform (Fin w)).prod (V38IndexedTwoTag.law src)).toFiniteLaw
      θ (((H+ell+b+1+r : ℕ) : ℤ)-1)) ∧
    (∀ (R : Set (Rows src (w := w))) (Yevent : Set (InternalLabel src streams)),
      1-η/(16*w) ≤ (firstRowLaw src (by rw [hwr]; positivity)).prob (· ∈ R) →
      θ ≤ streams.law.toFiniteLaw.prob (· ∈ Yevent) →
      H+ell+b+1+r ≤ Compression.restrictionD
        (V39TwoTagOwnerEmbedding.actualW src streams R₀ activity ξ₀) Yevent R) := by
  classical
  letI : NeZero w := ⟨by rw [hwr]; positivity⟩
  have hn := nearfull src μI streams R₀ activity ξ₀ H ell b r e0 x θ η hH hr hwr hq hs hx hθ hη
    hA hT href hnearfull hcap hexc hexcReceipt hinit hwx h2x hloss hwidth hforeignWidth
    hfloor hpairMargin hsmall hpairSmall hflag hException
  have hRfull : 1-η/(16*w) ≤
      (firstRowLaw src (by rw [hwr]; positivity)).prob (· ∈ (Set.univ : Set (Rows src (w := w)))) := by
    simp only [Set.mem_univ,FiniteLaw.prob_true]
    have hh : 0 ≤ η/(16*(w : ℝ)) := by positivity
    linarith
  have hYfull : θ ≤ streams.law.toFiniteLaw.prob
      (· ∈ (Set.univ : Set (InternalLabel src streams))) := by simpa using hθ1
  have hlower := hn Set.univ Set.univ hRfull hYfull
  have huniv : Compression.restrictionD
      (V39TwoTagOwnerEmbedding.actualW src streams R₀ activity ξ₀) Set.univ Set.univ =
      Workspace.Types.CommComplexity.D
        (V39TwoTagOwnerEmbedding.actualW src streams R₀ activity ξ₀) := by
    have hh := Paper2.pullback_D_eq_of_surjective
      (V39TwoTagOwnerEmbedding.actualW src streams R₀ activity ξ₀) Subtype.val Subtype.val
      (fun z => ⟨⟨z,Set.mem_univ z⟩,rfl⟩) (fun z => ⟨⟨z,Set.mem_univ z⟩,rfl⟩)
    exact hh
  rw [huniv] at hlower
  have hupper := selector_upper src μI streams R₀ activity ξ₀ (H+ell+b+1) r hwr hsourceUpper
  have hprofile := V39IndexedInternalProfile.profile src streams (rowLaw src μI)
    R₀ activity ξ₀ (H+ell+b) r x θ (by omega) hr hwr hx hθ hθ1 he hwxProfile
    (internal_streams_row_dwise src μI streams) href
  have hheight : ((H+ell+b+r : ℕ) : ℤ)=((H+ell+b+1+r : ℕ) : ℤ)-1 := by omega
  refine ⟨Nat.le_antisymm hupper hlower,?_,hn⟩
  simpa only [hheight,V39IndexedInternalProfile.W] using hprofile

end CurrentAdditive.V39IndexedAlignment

#print axioms CurrentAdditive.V39IndexedAlignment.nearfull
#print axioms CurrentAdditive.V39IndexedAlignment.selector_upper

#print axioms CurrentAdditive.V39IndexedAlignment.alignment
