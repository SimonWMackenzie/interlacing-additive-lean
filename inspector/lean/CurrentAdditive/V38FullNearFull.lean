import CurrentAdditive.V38FullNoState
import CurrentAdditive.V38SelectUsableMarks
import CurrentAdditive.V38PrefixResidual
import CurrentAdditive.V38Fin2ActualSeparation

/-!
Selected v39/v38 src:near-full, robustness.tex:153--278, full-product case.
Actual two-family retention, actual source profiles and graph gap produce
the literal source restriction lower bound. The prefix, fixed assignment,
collision geometry, usable marks and initial state are all constructed.
The source's numerical margins and its three source-profile assertions
remain explicit; no desired source hardness or witness count is a premise.
-/

namespace CurrentAdditive.V38FullNearFull

open Paper2 Paper2.SourceMatrix Paper2.SourceProjection
open Paper2.SourceSurvivingCollisions
open CurrentAdditive.EdgeSourceMatrix CurrentAdditive.V38Matrix
open CurrentAdditive.V38PrefixResidual CurrentAdditive.V38Fin2ActualPrefix
open Workspace.Types.Protocol Workspace.Types.CommComplexity

variable {V E X Y : Type*} [Fintype V] [Nonempty V] [Fintype E]
  [Fintype X] [Fintype Y] {q₁ q₂ t : ℕ}
  [NeZero q₁] [NeZero q₂] [NeZero (2^t)]

theorem restriction_lower
    (order : Items (2^t) V ≃ Fin (Fintype.card (Items (2^t) V)))
    (edge : E → Bool → V) (loopless : ∀ e, edge e false ≠ edge e true)
    (hs : 4 ≤ 2^t) (r Δ : ℕ) (hΔ : 0 < Δ)
    (hsourceq : q₂ = EdgeSource.sourceQ0 (Fin (4*(2^t))) E * r)
    (hdegree : ∀ v, SourceItems.degree edge v ≤ Δ)
    (γ : ℝ) (hγ : 0 < γ) (hE : 0 < Fintype.card E)
    (gap : ∀ colour : V → Fin 3, γ * Fintype.card E ≤
      ((Finset.univ.filter (fun e => colour (edge e false) = colour (edge e true))).card : ℝ))
    (μ : PositiveRationalLaw X) (ν : PositiveRationalLaw Y)
    (R : X → Y → Bool) (ξ₀ : Tail (2^t) Y)
    (H ell : ℕ) (hq₂ : q₂=2^ell) (hq2 : 2 ≤ q₂) (hH : 2 ≤ H)
    (x ρ η : ℝ) (hx : 0 < x) (hη : 0 < η)
    (hηSmall : η < 1/100)
    (hηTemplate : η*(2^t : ℕ)/(255/256 : ℝ) ≤ 1/1000)
    (hηAllowance : η ≤ deletionAllowance (V := V) (E := E) γ Δ (2^t))
    (hassign : 4*((2^t : ℕ) : ℝ)^2*ρ ≤ 1)
    (hmargin : 8*((2^t : ℕ) : ℝ)*q₁ + 1024*(2^t : ℕ)*η*q₂ < (γ/24)*q₂/4)
    (hsmall : 2*(q₂ : ℝ)*x ≤ 1/8)
    (hprefixGap : 2*(2 : ℝ)^t*x < 999/1000)
    (hdominant : (998/1000 : ℝ) ≤ 999/1000 - 2*((2^t : ℕ)-1 : ℕ)*x)
    (hprofileA : V38RestrictionProfiles.TwoThresholdProfile
      (fun (word : Word q₁ (2^t) Y) j => M₁ R j word)
      (ν.iid (q₁+2^t+1)).toFiniteLaw
      ((PositiveRationalLaw.uniform (Fin q₁)).prod μ).toFiniteLaw x (H : ℤ))
    (hprofileT : V38RestrictionProfiles.TwoThresholdProfile (SourceMatrix.T R)
      (SourceLaws.templateLaw μ q₁ q₂).toFiniteLaw
      (SourceLaws.outerLaw ν q₁ q₂ (2^t)).toFiniteLaw x ((H+ell : ℕ) : ℤ))
    (threeTail : ∀ (Rows : Set (Fin (q₁+3) × X))
      (Words : Set (Fin (q₁+3) → Y)),
      (∀ i, 2*((2^t : ℕ) : ℝ)*ρ ≤ μ.toFiniteLaw.prob (fun u => (i,u) ∈ Rows)) →
      (1/2 : ℝ) < (ν.iid (q₁+3)).toFiniteLaw.prob (· ∈ Words) →
      H+1 ≤ Compression.restrictionD (fullInterlace R (q₁+3)) Rows Words)
    (W : Set (RawRow q₁ q₂ (2^t) X (Items (2^t) V)))
    (U : Set (V38Matrix.TaggedColumn q₁ q₂ (2^t) Y))
    (hW : 1-η ≤ (V38Matrix.columnLaw (V := V) μ hs).toFiniteLaw.prob (· ∈ W))
    (hU : 1-η ≤ (V38Matrix.taggedLaw ν).toFiniteLaw.prob (· ∈ U)) :
    H+ell+t+1 ≤ Compression.restrictionD
      (V38Matrix.matrix order edge (by omega : 3 ≤ 2^t) r hsourceq R ξ₀) U W := by
  classical
  let M := V38Matrix.matrix (q₁ := q₁) order edge (by omega : 3 ≤ 2^t) r hsourceq R ξ₀
  by_contra hneg
  change ¬ H+ell+t+1 ≤ Compression.restrictionD M U W at hneg
  have hupper : Compression.restrictionD M U W ≤ H+ell+t := by omega
  let F := fun (a : W) (c : U) => M c.val a.val
  obtain ⟨P,hPcost,hP⟩ := Nat.sInf_mem (Workspace.UpperBound.AchievableCosts_nonempty F)
  have he : D F = Compression.restrictionD M U W := restrictionD_transpose M U W
  have hcost : P.cost ≤ H+ell+t :=
    (show P.cost = D F from hPcost).le.trans (he.le.trans hupper)
  have htag : (99/100 : ℝ) < (V38Matrix.taggedLaw ν).toFiniteLaw.prob (· ∈ U) := by
    linarith
  have hUne : U.Nonempty := by
    by_contra hn
    have heU : U=∅ := Set.not_nonempty_iff_eq_empty.mp hn
    simp [heU] at htag
    norm_num at htag
  have hrow (p : Fin (2^t)) : (999/1000 : ℝ) ≤
      (SourceLaws.templateLaw μ q₁ q₂).toFiniteLaw.prob
        (fun z => (Sum.inl (p,z) : RawRow q₁ q₂ (2^t) X (Items (2^t) V)) ∈ W) := by
    have hr := SourceProjectionRetention.template_bin_retained μ hs (· ∈ W) η hW p
    linarith
  have ht : 1 ≤ t := by
    by_contra hn
    have hz : t=0 := by omega
    have hs' : (4 : ℕ) ≤ 1 := by simpa only [hz,pow_zero] using hs
    omega
  have hscale : (2 : ℝ)^t*x ≤ 1 := by nlinarith
  obtain ⟨hpref,dom,_hown,_hforeign,hlarge⟩ := actual_two_threshold_separation
    (SourceLaws.templateLaw μ q₁ q₂) ν R
    (activity order edge (by omega : 3 ≤ 2^t) r hsourceq) ξ₀ W U P (H+ell)
    x (999/1000) ht (by omega) hx hscale hprofileT hrow hprefixGap htag hcost hP
  let K : Fin (2^t) → Set (Template q₁ q₂ X) := fun j => retainedPrefixFibre P (dom j) j
  have hKmass (j : Fin (2^t)) : (998/1000 : ℝ) <
      (SourceLaws.templateLaw μ q₁ q₂).toFiniteLaw.prob (· ∈ K j) :=
    hdominant.trans_lt (hlarge j)
  let code := rawCode (t := t) P
  obtain ⟨j,Marks,hMarks,hexcess,hcollision⟩ :=
    V38SelectUsableMarks.select_marks_from_actual_retention order edge loopless hs r Δ hΔ
      hsourceq hdegree γ hγ hE gap μ ν W U code K ρ η hη hηAllowance
      hassign hmargin hKmass hW hU
  let A := branchRows P j
  have hK : ∀ z ∈ K j, (Sum.inl (dom j,z) : RawRow q₁ q₂ (2^t) X (Items (2^t) V)) ∈ A := by
    intro z hz
    obtain ⟨hz,hcode⟩ := hz
    exact ⟨hz,(rawCode_of_mem P _ hz).trans hcode⟩
  have hresCost : (branchProtocol P hUne j).cost ≤ H+ell := by
    have hsub := branch_cost P hUne hpref j
    omega
  have hresCorrect : ∀ a c, c ∈ U → (branchProtocol P hUne j).eval a c = M c a.val :=
    branch_correct (fun a c => M c a) P hUne hpref hP j
  exact V38FullNoState.no_short_with_usable_collision_coordinates order edge
    (by omega : 3 ≤ 2^t) r hsourceq μ ν R ξ₀ H ell hq₂ hq2 hH x
    (2*((2^t : ℕ) : ℝ)*ρ) hx hsmall hprofileA threeTail (dom j) (K j) A U hK
    (hKmass j) Marks hMarks hexcess hcollision (branchProtocol P hUne j) hresCost hresCorrect

end CurrentAdditive.V38FullNearFull

#print axioms CurrentAdditive.V38FullNearFull.restriction_lower
