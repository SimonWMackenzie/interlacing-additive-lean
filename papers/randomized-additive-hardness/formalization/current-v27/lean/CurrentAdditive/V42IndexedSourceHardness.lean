import CurrentAdditive.V42IndexedNearFullInterface
import CurrentAdditive.DeterministicIndexedUpper

/-! Exact standalone src:near-full for the explicit construction.  The
base cost and displayed width identities supply the independent upper
bound; no base restriction profile is assumed. -/

namespace CurrentAdditive.V42IndexedSourceHardness

open Paper2 Paper2.SourceMatrix Paper2.SourceSurvivingCollisions
open CurrentAdditive.EdgeSourceMatrix CurrentAdditive.DeterministicIndexedMatrix
open CurrentAdditive.DeterministicIndexedMatrix.Sources
open CurrentAdditive.V38IndexedTwoTag
open Workspace.Types.CommComplexity
open V42IndexedCollisionInterface

def sourceCost (d t ell : ℕ) : ℕ := d+t+ell+t+1
theorem sourceCost_eq (d t ell : ℕ) : sourceCost d t ell=d+2*t+ell+1 := by
  unfold sourceCost; omega

variable {V E X Y : Type*} [Fintype V] [Nonempty V] [Fintype E]
  [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
  {D q₁ q₂ t : ℕ} [NeZero q₁] [NeZero q₂] [NeZero (2^t)]
  [Nonempty (Fin (4*(2^t)))] [Nonempty (Fin (2^t-3))]
  {μX : PositiveRationalLaw X} {μY : PositiveRationalLaw Y}
  (src : Sources (D := D) (q₁ := q₁) (q₂ := q₂) (s := 2^t) μX μY)

omit [Nonempty (Fin (4*(2^t)))] [Nonempty (Fin (2^t-3))] in
theorem source_upper {I : Type*} [Fintype I]
    (R : X → Y → Bool) (activity : I → Fin q₂ → Option (Fin (2^t)))
    (ξ₀ : Tail (2^t) Y) (d ell : ℕ)
    (hbase : Workspace.Types.CommComplexity.D R=d)
    (hq₁ : q₁+2=2^t) (hq₂ : q₂=2^ell) :
    Workspace.Types.CommComplexity.D (matrix src R activity ξ₀) ≤ sourceCost d t ell := by
  classical
  have hsub : Workspace.Types.CommComplexity.D (matrix src R activity ξ₀) ≤
      Workspace.Types.CommComplexity.D (Sources.N src R activity ξ₀) :=
    Workspace.ProofLemmas.SublemmaPrecompNoIncrease (Sources.N src R activity ξ₀)
      (oldTag src) id
  have hu := Sources.indexed_B_universal_D_le src activity ξ₀ R
  rw [← Sources.indexed_N_D_eq_B src activity ξ₀ R] at hu
  have hs : Nat.clog 2 (2^t)=t := by simp
  have hq : Nat.clog 2 q₂=ell := by simp [hq₂]
  have ht : Nat.clog 2 (q₁+2^t+1) ≤ t+1 := by
    apply (Nat.clog_le_iff_le_pow (by decide)).2
    rw [pow_succ]
    omega
  rw [hs,hq,hbase] at hu
  unfold sourceCost
  omega

theorem hardness
    (hD : 8 ≤ D) (π : Fin q₂ ≃ Fin q₂)
    (order : Items (2^t) V ≃ Fin (Fintype.card (Items (2^t) V)))
    (edge : E → Bool → V) (loopless : ∀ e, edge e false ≠ edge e true)
    (hs : 4 ≤ 2^t) (r Δ : ℕ) (hΔ : 0 < Δ)
    (hsourceq : q₂=EdgeSource.sourceQ0 (Fin (4*(2^t))) E*r)
    (hdegree : ∀ v, SourceItems.degree edge v ≤ Δ)
    (γ : ℝ) (hγ : 0 < γ) (hE : 0 < Fintype.card E)
    (gap : ∀ colour : V → Fin 3, γ*Fintype.card E ≤
      ((Finset.univ.filter (fun e => colour (edge e false)=colour (edge e true))).card : ℝ))
    (R : X → Y → Bool) (ξ₀ : Tail (2^t) Y)
    (d ell : ℕ) (hd : 3 ≤ d) (hbase : Workspace.Types.CommComplexity.D R=d)
    (hq₁ : q₁+2=2^t) (hq₂ : q₂=2^ell) (hq2 : 2 ≤ q₂)
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
      ((PositiveRationalLaw.uniform (Fin q₁)).prod μX).toFiniteLaw x ((d+t : ℕ) : ℤ))
    (hprofileT : V38RestrictionProfiles.TwoThresholdProfile (Sources.T src R)
      src.inner.law.toFiniteLaw
      ((PositiveRationalLaw.uniform (Fin q₂)).prod src.gamma.law).toFiniteLaw x ((d+t+ell : ℕ) : ℤ))
    (threeTail : ThreeTailBound src R (d+t) (2*((2^t : ℕ) : ℝ)*ρ)) :
    let M := matrix src R (fun i α => activity order edge (by omega : 3 ≤ 2^t) r hsourceq i (π α)) ξ₀
    Workspace.Types.CommComplexity.D M=sourceCost d t ell ∧
    ∀ (W : Set (Row (I := Items (2^t) V) src)) (U : Set (V38IndexedTwoTag.Column src)),
      1-η ≤ (rowLaw src
        (itemLaw (G := Fin (4*(2^t))) (V := V) (A := Fin (2^t-3)))).toFiniteLaw.prob (· ∈ W) →
      1-η ≤ (law src).toFiniteLaw.prob (· ∈ U) →
      sourceCost d t ell ≤ Compression.restrictionD M U W := by
  classical
  dsimp only
  have hl := V42IndexedNearFullInterface.restriction_lower src hD π order edge loopless hs r Δ hΔ
    hsourceq hdegree γ hγ hE gap R ξ₀ (d+t) ell (by omega) hq₂ hq2 x ρ η hx hη
    hηSmall hηTemplate hηAllowance hassign hmargin hsmall hprefixGap hdominant
    hprofileA hprofileT threeTail
  refine ⟨?_,hl⟩
  apply Nat.le_antisymm (source_upper src R _ ξ₀ d ell hbase hq₁ hq₂)
  have hfull := hl Set.univ Set.univ
    (by simp only [Set.mem_univ,FiniteLaw.prob_true]; linarith)
    (by simp only [Set.mem_univ,FiniteLaw.prob_true]; linarith)
  exact hfull.trans (SourceProfilesInner.restrictionD_le _ Set.univ Set.univ)

#print axioms source_upper
#print axioms hardness

end CurrentAdditive.V42IndexedSourceHardness
