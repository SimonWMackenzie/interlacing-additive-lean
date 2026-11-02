import CurrentAdditive.V39FullProductAlignment
import CurrentAdditive.V39FullAlignmentGuards
import CurrentAdditive.V39SourceProfilesAllLarge
import CurrentAdditive.V39FullNearFullAllLarge

/-! The original full-product internal W at the public full schedule.
Every intermediate source profile, source near-full lower bound and common
scalar guard is supplied by its actual checked owner. The only hardness
inputs are the original base profile/exact cost and the graph promise. -/

namespace CurrentAdditive.V39FullScheduleAlignment

open Paper2 Paper2.SourceMatrix Workspace.Types.CommComplexity V38Schedule
open CurrentAdditive.EdgeSourceMatrix
open CurrentAdditive.V39FullProductSources

instance fullW_neZero (L : ℕ) : NeZero (V38Schedule.fullW L) := by
  constructor
  unfold V38Schedule.fullW
  positivity

variable {V E X Y : Type*} [Fintype V] [Nonempty V] [Fintype E]
  [Fintype X] [Fintype Y] [DecidableEq V] [DecidableEq E]
  [DecidableEq X] [DecidableEq Y]

def internalHeight (d L : ℕ) : ℕ := V39FullNearFullAllLarge.sourceCost d L+8*ell L

theorem internalHeight_eq (d L : ℕ) : internalHeight d L=d+L+65+12*ell L := by
  unfold internalHeight V39FullNearFullAllLarge.sourceCost
  omega

noncomputable def tupleLaw (μ : PositiveRationalLaw X) (L : ℕ) :
    FiniteLaw (Fin (V38Schedule.fullW L) → RawRow (fullQ₁ L) (fullQ₂ L) (fullS L) X (Items (fullS L) V)) :=
  (V38Matrix.columnLaw (q₁ := fullQ₁ L) (q₂ := fullQ₂ L) (s := fullS L)
    (V := V) μ (by have := fullS_ge_256 L; omega)).toFiniteLaw.iid (V38Schedule.fullW L)

noncomputable def copyLaw (ν : PositiveRationalLaw Y) (L : ℕ) :
    FiniteLaw (Fin (V38Schedule.fullW L) × V38Matrix.TaggedColumn (fullQ₁ L) (fullQ₂ L) (fullS L) Y) :=
  ((PositiveRationalLaw.uniform (Fin (V38Schedule.fullW L))).prod
    (V38Matrix.taggedLaw (q₁ := fullQ₁ L) (q₂ := fullQ₂ L) (s := fullS L) ν)).toFiniteLaw

noncomputable def matrix (L : ℕ)
    (order : Items (fullS L) V ≃ Fin (Fintype.card (Items (fullS L) V)))
    (edge : E → Bool → V) (rep : ℕ)
    (hq : fullQ₂ L=EdgeSource.sourceQ0 (Fin (4*fullS L)) E*rep)
    (R : X → Y → Bool) (ξ₀ : Tail (fullS L) Y) :
    (Fin (V38Schedule.fullW L) → RawRow (fullQ₁ L) (fullQ₂ L) (fullS L) X (Items (fullS L) V)) →
    (Fin (V38Schedule.fullW L) × V38Matrix.TaggedColumn (fullQ₁ L) (fullQ₂ L) (fullS L) Y) → Bool :=
  V39FullProductSources.fullW R
    (activity order edge (by have := fullS_ge_256 L; omega : 3 ≤ fullS L) rep hq) ξ₀

theorem alignment
    (L : ℕ) (hL : L=Nat.clog 2 (Fintype.card V))
    (order : Items (fullS L) V ≃ Fin (Fintype.card (Items (fullS L) V)))
    (edge : E → Bool → V) (loopless : ∀ e, edge e false ≠ edge e true)
    (rep Δ : ℕ) (hΔ : 0 < Δ)
    (hq : fullQ₂ L=EdgeSource.sourceQ0 (Fin (4*fullS L)) E*rep)
    (hdegree : ∀ v, SourceItems.degree edge v ≤ Δ)
    (γ : ℚ) (hγ : 0 < γ) (hE : 0 < Fintype.card E)
    (hnm : Fintype.card V ≤ 2*Fintype.card E)
    (hdeg : 2*Fintype.card E ≤ Δ*Fintype.card V)
    (hlarge : V39FullCutoff.sourceCutoff γ Δ ≤ Fintype.card V)
    (gap : ∀ colour : V → Fin 3, (γ : ℝ)*Fintype.card E ≤
      ((Finset.univ.filter (fun e => colour (edge e false)=colour (edge e true))).card : ℝ))
    (μ : PositiveRationalLaw X) (ν : PositiveRationalLaw Y)
    (R : X → Y → Bool) (ξ₀ : Tail (fullS L) Y)
    (d : ℕ) (hd : 3 ≤ d)
    (hp : V38RestrictionProfiles.TwoThresholdProfile R μ.toFiniteLaw ν.toFiniteLaw
      ((fullRho L : ℚ) : ℝ) (d : ℤ)) (hD : D R=d) :
    D (matrix L order edge rep hq R ξ₀)=internalHeight d L ∧
    V38RestrictionProfiles.TwoThresholdProfile (matrix L order edge rep hq R ξ₀)
      (tupleLaw (V := V) μ L) (copyLaw ν L)
      ((theta (fullQ L) : ℚ) : ℝ) ((internalHeight d L : ℤ)-1) ∧
    (∀ (U : Set (Fin (V38Schedule.fullW L) × V38Matrix.TaggedColumn (fullQ₁ L) (fullQ₂ L) (fullS L) Y))
      (Z : Set (Fin (V38Schedule.fullW L) → RawRow (fullQ₁ L) (fullQ₂ L) (fullS L) X (Items (fullS L) V))),
      1-((fullEta (fullConstant γ Δ (Fintype.card V) (Fintype.card E)) L : ℚ) : ℝ)/(16*V38Schedule.fullW L) ≤
        (copyLaw ν L).prob (· ∈ U) →
      ((theta (fullQ L) : ℚ) : ℝ) ≤ (tupleLaw (V := V) μ L).prob (· ∈ Z) →
      internalHeight d L ≤ Compression.restrictionD (matrix L order edge rep hq R ξ₀) Z U) := by
  classical
  let n := Fintype.card V
  let m := Fintype.card E
  let c := fullConstant γ Δ n m
  have hs : 4 ≤ fullS L := by have := fullS_ge_256 L; omega
  have hn : 0 < n := Fintype.card_pos
  have htests := V39FullCutoff.fullPublicTests_all_large γ Δ n m hγ hΔ hn hnm hdeg hlarge
  rw [← hL] at htests
  obtain ⟨h0,hc,_,_,_⟩ := V39PublicSchedule.fullConstant_interval γ Δ n m hγ hΔ hn hnm
  have hc0 : 0 < c := h0.trans_le hc
  have g := V39FullAlignmentGuards.guards_of_tests c (sourceDeltaV γ Δ n m) (sourceZeta γ) L m hc0 htests
  have hprofiles := V39FullScheduledSource.costs_and_profiles
    (q₁ := fullQ₁ L) (q₂ := fullQ₂ L) (s := fullS L) μ ν R order edge hs rep hq ξ₀ d hd
    c (sourceDeltaV γ Δ n m) (sourceZeta γ) L m rfl rfl rfl htests.1 hp hD
  rcases hprofiles with ⟨_,_,hA,hT,href⟩
  let μI := graphItemLaw (Vertex := V) hs
  have hlaw := raw_law_eq_current (D := 8192) (Vertex := V) (q₁ := fullQ₁ L) (q₂ := fullQ₂ L)
    (s := fullS L) μ ν hs
  rw [← hlaw] at href
  have hnear : ∀ (U : Set (V38Matrix.TaggedColumn (fullQ₁ L) (fullQ₂ L) (fullS L) Y))
      (Z : Set (RawRow (fullQ₁ L) (fullQ₂ L) (fullS L) X (Items (fullS L) V))),
      1-V39FullAlignmentGuards.Eta c L ≤ (V38Matrix.taggedLaw ν).toFiniteLaw.prob (· ∈ U) →
      1-V39FullAlignmentGuards.Eta c L ≤
        (DeterministicIndexedMatrix.Sources.rowLaw
          (fullSources (D := 8192) (q₁ := fullQ₁ L) (q₂ := fullQ₂ L) (s := fullS L) μ ν) μI).toFiniteLaw.prob (· ∈ Z) →
      V39FullNearFullAllLarge.sourceCost d L ≤ Compression.restrictionD
        (V38Matrix.matrix order edge (by omega : 3 ≤ fullS L) rep hq R ξ₀) U Z := by
    intro U Z hU hZ
    rw [hlaw] at hZ
    exact V39FullNearFullAllLarge.restriction_lower L hL order edge loopless rep Δ hΔ hq hdegree
      γ hγ hE hnm hdeg hlarge gap μ ν R ξ₀ d hd hp hD Z U hZ hU
  have hq₁ : fullQ₁ L+2=fullS L := by unfold fullQ₁; omega
  have hu := (V38Matrix.matrix_upper_budgets order edge (by omega : 3 ≤ fullS L) rep hq R ξ₀
    (16+ell L) (L+2*(16+ell L)) hq₁ rfl g.q_pow).1
  rw [hD] at hu
  have result := V39FullProductAlignment.alignment μ ν μI R
    (activity order edge (by omega : 3 ≤ fullS L) rep hq) ξ₀
    (d+(16+ell L)) (L+2*(16+ell L)) (16+ell L) (8*ell L)
    (e0 (fullQlog L) (fullEta c L))
    (V39FullAlignmentGuards.X L) (V39FullAlignmentGuards.Theta L) (V39FullAlignmentGuards.Eta c L)
    (by omega) g.r_ge g.w_pow g.q_pow g.s_pow g.x_pos g.theta_pos g.eta_pos
    hA hT href hnear g.cap g.exc g.receipt g.init g.wx g.two_x g.loss g.width
    g.foreign g.floor g.pair_margin g.small g.pair_small g.flag g.exception
    g.theta_le_one g.profile_exception g.profile_wx hu
  simp only [matrix,internalHeight,tupleLaw,copyLaw,← hlaw] at ⊢
  exact result

#print axioms alignment

end CurrentAdditive.V39FullScheduleAlignment
