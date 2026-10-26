import CurrentAdditive.V42IndexedCollisionInterface
import CurrentAdditive.V39IndexedNearFull

/-! Standalone explicit-list src:near-full.  Only the stated template
profiles and first-list/three-tail collision bound are assumed.  No
restriction profile of the base matrix is an additional premise. -/

namespace CurrentAdditive.V42IndexedNearFullInterface

open Paper2 Paper2.SourceMatrix Paper2.SourceSurvivingCollisions
open CurrentAdditive.EdgeSourceMatrix CurrentAdditive.DeterministicIndexedMatrix
open CurrentAdditive.DeterministicIndexedMatrix.Sources
open CurrentAdditive.V38PrefixResidual CurrentAdditive.V38IndexedTwoTag
open Workspace.Types.Protocol Workspace.Types.CommComplexity
open V42IndexedCollisionInterface

variable {V E X Y : Type*} [Fintype V] [Nonempty V] [Fintype E]
  [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
  {D q₁ q₂ t : ℕ} [NeZero q₁] [NeZero q₂] [NeZero (2^t)]
  [Nonempty (Fin (4*(2^t)))] [Nonempty (Fin (2^t-3))]
  {μX : PositiveRationalLaw X} {μY : PositiveRationalLaw Y}
  (src : Sources (D := D) (q₁ := q₁) (q₂ := q₂) (s := 2^t) μX μY)

theorem restriction_lower
    (hD : 8 ≤ D) (π : Fin q₂ ≃ Fin q₂)
    (order : Items (2^t) V ≃ Fin (Fintype.card (Items (2^t) V)))
    (edge : E → Bool → V) (loopless : ∀ e, edge e false ≠ edge e true)
    (hs : 4 ≤ 2^t) (r Δ : ℕ) (hΔ : 0 < Δ)
    (hsourceq : q₂ = EdgeSource.sourceQ0 (Fin (4*(2^t))) E*r)
    (hdegree : ∀ v, SourceItems.degree edge v ≤ Δ)
    (γ : ℝ) (hγ : 0 < γ) (hE : 0 < Fintype.card E)
    (gap : ∀ colour : V → Fin 3, γ*Fintype.card E ≤
      ((Finset.univ.filter (fun e => colour (edge e false)=colour (edge e true))).card : ℝ))
    (R : X → Y → Bool) (ξ₀ : Tail (2^t) Y)
    (H ell : ℕ) (hH : 2 ≤ H) (hq₂ : q₂=2^ell) (hq2 : 2 ≤ q₂)
    (x ρ η : ℝ) (hx : 0 < x) (hη : 0 < η)
    (hηSmall : η < 1/100)
    (hηTemplate : (256/255 : ℝ)*(2^t : ℕ)*η ≤ 1/1000)
    (hηAllowance : η ≤ deletionAllowance (V := V) (E := E) γ Δ (2^t))
    (hassign : 4*((2^t : ℕ) : ℝ)^2*ρ ≤ 1)
    (hmargin : 8*((2^t : ℕ) : ℝ)*q₁+1024*(2^t : ℕ)*η*q₂ < (γ/24)*q₂/4)
    (hsmall : 2*(q₂ : ℝ)*x ≤ 1/8)
    (hprefixGap : 2*(2 : ℝ)^t*x < 999/1000)
    (hdominant : (998/1000 : ℝ) ≤ 999/1000-2*((2^t : ℕ)-1 : ℕ)*x)
    (hprofileA : V38RestrictionProfiles.TwoThresholdProfile (Sources.A src R)
      src.gamma.law.toFiniteLaw
      ((PositiveRationalLaw.uniform (Fin q₁)).prod μX).toFiniteLaw x (H : ℤ))
    (hprofileT : V38RestrictionProfiles.TwoThresholdProfile (Sources.T src R)
      src.inner.law.toFiniteLaw
      ((PositiveRationalLaw.uniform (Fin q₂)).prod src.gamma.law).toFiniteLaw x ((H+ell : ℕ) : ℤ))
    (threeTail : ThreeTailBound src R H (2*((2^t : ℕ) : ℝ)*ρ))
    (W : Set (Row (I := Items (2^t) V) src)) (U : Set (V38IndexedTwoTag.Column src))
    (hW : 1-η ≤ (rowLaw src
      (itemLaw (G := Fin (4*(2^t))) (V := V) (A := Fin (2^t-3)))).toFiniteLaw.prob (· ∈ W))
    (hU : 1-η ≤ (law src).toFiniteLaw.prob (· ∈ U)) :
    H+ell+t+1 ≤ Compression.restrictionD
      (matrix src R (fun i α => activity order edge (by omega : 3 ≤ 2^t) r hsourceq i (π α)) ξ₀) U W := by
  classical
  let M := matrix (I := Items (2^t) V) src R
    (fun i α => activity order edge (by omega : 3 ≤ 2^t) r hsourceq i (π α)) ξ₀
  by_contra hneg
  change ¬ H+ell+t+1 ≤ Compression.restrictionD M U W at hneg
  have hupper : Compression.restrictionD M U W ≤ H+ell+t := by omega
  let F := fun (a : W) (c : U) => M c.val a.val
  obtain ⟨P,hPcost,hP⟩ := Nat.sInf_mem (Workspace.UpperBound.AchievableCosts_nonempty F)
  have he : Workspace.Types.CommComplexity.D F = Compression.restrictionD M U W :=
    SourceProjection.restrictionD_transpose M U W
  have hcost : P.cost ≤ H+ell+t :=
    (show P.cost = Workspace.Types.CommComplexity.D F from hPcost).le.trans (he.le.trans hupper)
  have htag : (99/100 : ℝ) < (law src).toFiniteLaw.prob (· ∈ U) := by linarith
  have hUne : U.Nonempty := by
    by_contra hn
    have heU : U=∅ := Set.not_nonempty_iff_eq_empty.mp hn
    simp [heU] at htag
    norm_num at htag
  have hrow (p : Fin (2^t)) : (999/1000 : ℝ) ≤ src.inner.law.toFiniteLaw.prob
      (fun z => (Sum.inl (p,z) : Row (I := Items (2^t) V) src) ∈ W) :=
    retained_each_template_bin_of_total src
      (itemLaw (G := Fin (4*(2^t))) (V := V) (A := Fin (2^t-3))) W η hW hηTemplate p
  have ht : 1 ≤ t := by
    by_contra hn
    have hz : t=0 := by omega
    have hs' : (4 : ℕ) ≤ 1 := by simpa only [hz,pow_zero] using hs
    omega
  have hscale : (2 : ℝ)^t*x ≤ 1 := by nlinarith
  obtain ⟨hpref,dom,_hown,_hforeign,hlarge⟩ := indexed_two_threshold_separation src
    hD R (fun i α => activity order edge (by omega : 3 ≤ 2^t) r hsourceq i (π α)) ξ₀ U W P
    (H+ell) x (999/1000) ht (by omega) hx hscale hprofileT hrow hprefixGap htag hcost hP
  let K : Fin (2^t) → Set src.inner.Label := fun j => retainedIndexedPrefixFibre src P (dom j) j
  have hKmass (j : Fin (2^t)) : (998/1000 : ℝ) < src.inner.law.toFiniteLaw.prob (· ∈ K j) :=
    hdominant.trans_lt (hlarge j)
  let code := rawCode (t := t) P
  obtain ⟨j,Marks,hMarks,hexcess,hcollision⟩ :=
    V39IndexedSelectMarksPermuted.select_marks_from_actual_retention src (by omega) π order edge
      loopless hs r Δ hΔ hsourceq hdegree γ hγ hE gap W U code K ρ η hη
      hηAllowance hassign hmargin hKmass hW hU
  let A := branchRows P j
  have hK : ∀ z ∈ K j, (Sum.inl (dom j,z) : Row (I := Items (2^t) V) src) ∈ A := by
    intro z hz
    obtain ⟨hz,hcode⟩ := hz
    exact ⟨hz,(rawCode_of_mem P _ hz).trans hcode⟩
  have hresCost : (branchProtocol P hUne j).cost ≤ H+ell := by
    have hsub := branch_cost P hUne hpref j
    omega
  have hresCorrect : ∀ a c, c ∈ U → (branchProtocol P hUne j).eval a c = M c a.val :=
    branch_correct (fun a c => M c a) P hUne hpref hP j
  exact V42IndexedCollisionInterface.no_short_with_usable_collision_coordinates src hD R
    (fun i α => activity order edge (by omega : 3 ≤ 2^t) r hsourceq i (π α)) ξ₀
    H ell hH hq₂ hq2 x (2*((2^t : ℕ) : ℝ)*ρ) hx hsmall hprofileA threeTail
    (dom j) (K j) A U hK (hKmass j) Marks hMarks hexcess hcollision
    (branchProtocol P hUne j) hresCost hresCorrect

#print axioms restriction_lower

end CurrentAdditive.V42IndexedNearFullInterface

