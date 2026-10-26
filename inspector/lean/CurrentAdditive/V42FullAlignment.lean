import CurrentAdditive.V42FullNearFull
import CurrentAdditive.V42AlignmentGuards
import CurrentAdditive.V42FullProductAlignment
import CurrentAdditive.V39FullProductSpecialization
namespace CurrentAdditive.V42FullAlignment
open Paper2 Paper2.SourceMatrix Workspace.Types.CommComplexity
open CurrentAdditive.EdgeSourceMatrix CurrentAdditive.V39FullProductSources
open CurrentAdditive.DeterministicIndexedMatrix.Sources
open V42FullSuccessor V42PublicSchedule
set_option maxHeartbeats 2000000
variable {V E X Y : Type*} [Fintype V] [Nonempty V] [Fintype E]
  [Fintype X] [Fintype Y] [Nonempty X] [Nonempty Y]
  [DecidableEq V] [DecidableEq E] [DecidableEq X] [DecidableEq Y]
def internalHeight (d L : ℕ) : ℕ := V42FullNearFull.sourceCost d L+8*fullExponent L
noncomputable def tupleLaw (μ : PositiveRationalLaw X) (L : ℕ) :=
  ((V38Matrix.columnLaw (q₁:=fullQ₁ L) (q₂:=fullQ₂ L) (s:=fullS L)
    (V:=V) μ (by have := fullS_ge_256 L; omega)).iid (fullW L)).toFiniteLaw
noncomputable def copyLaw (ν : PositiveRationalLaw Y) (L : ℕ) :=
  ((PositiveRationalLaw.uniform (Fin (fullW L))).prod
    (V38Matrix.taggedLaw (q₁:=fullQ₁ L) (q₂:=fullQ₂ L) (s:=fullS L) ν)).toFiniteLaw
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
    (hk : V42Schedule.commonCutoff (V38Schedule.sourceDeltaV γ Δ (Fintype.card V) (Fintype.card E))
      (V38Schedule.sourceZeta γ) Δ ≤ fullExponent L) (hb : 4*fullExponent L≤L)
    (gap : ∀ colour : V → Fin 3, (γ : ℝ)*Fintype.card E ≤
      ((Finset.univ.filter (fun e => colour (edge e false)=colour (edge e true))).card : ℝ))
    (μ : PositiveRationalLaw X) (ν : PositiveRationalLaw Y)
    (R : X → Y → Bool) (ξ₀ : Tail (fullS L) Y)
    (d : ℕ) (hd : 3 ≤ d)
    (hp : V38RestrictionProfiles.TwoThresholdProfile R μ.toFiniteLaw ν.toFiniteLaw
      (V42Schedule.rho L:ℝ) (d : ℤ)) (hD : D R=d) :
    D (internal L order edge rep hq R ξ₀)=internalHeight d L ∧
    V38RestrictionProfiles.TwoThresholdProfile (internal L order edge rep hq R ξ₀)
      (tupleLaw (V := V) μ L) (copyLaw ν L)
      (V42Schedule.theta (fullExponent L):ℝ) ((internalHeight d L : ℤ)-1) ∧
    (∀ (U : Set (Fin (fullW L) × V38Matrix.TaggedColumn (fullQ₁ L) (fullQ₂ L) (fullS L) Y))
      (Z : Set (Fin (fullW L) → RawRow (fullQ₁ L) (fullQ₂ L) (fullS L) X (Items (fullS L) V))),
      1-(V42Schedule.eta (fullExponent L):ℝ)/(16*fullW L) ≤
        (copyLaw ν L).prob (· ∈ U) →
      (V42Schedule.theta (fullExponent L):ℝ) ≤ (tupleLaw (V := V) μ L).prob (· ∈ Z) →
      internalHeight d L ≤ Compression.restrictionD (internal L order edge rep hq R ξ₀) Z U) := by
  classical
  let k:=fullExponent L
  have hs : 4≤fullS L := by have := fullS_ge_256 L; omega
  have hk200 : 200≤k := by unfold V42Schedule.commonCutoff at hk; omega
  have g:=V42AlignmentGuards.guards k L hk200 hb
  obtain ⟨hA,hT,href⟩:=V42FullProfiles.profiles L hL μ ν R order edge rep hq ξ₀ d hd
    γ Δ hγ hΔ hnm hdeg hlarge hp hD
  let μI:=graphItemLaw (Vertex:=V) hs
  have hlaw:=raw_law_eq_current (D:=8192) (Vertex:=V) (q₁:=fullQ₁ L) (q₂:=fullQ₂ L)
    (s:=fullS L) μ ν hs
  rw [←hlaw] at href
  have hnear : ∀ (U : Set (V38Matrix.TaggedColumn (fullQ₁ L) (fullQ₂ L) (fullS L) Y))
      (Z : Set (RawRow (fullQ₁ L) (fullQ₂ L) (fullS L) X (Items (fullS L) V))),
      1-(V42Schedule.eta k:ℝ)≤(V38Matrix.taggedLaw ν).toFiniteLaw.prob (·∈U) →
      1-(V42Schedule.eta k:ℝ)≤
        (rowLaw (fullSources (D:=8192) (q₁:=fullQ₁ L) (q₂:=fullQ₂ L) (s:=fullS L) μ ν) μI).toFiniteLaw.prob (·∈Z) →
      V42FullNearFull.sourceCost d L≤Compression.restrictionD
        (V38Matrix.matrix order edge (by omega : 3≤fullS L) rep hq R ξ₀) U Z := by
    intro U Z hU hZ
    rw [hlaw] at hZ
    exact V42FullNearFull.nearfull L hL order edge loopless rep Δ hΔ hq hdegree γ hγ hE
      hnm hdeg hlarge hk hb gap μ ν R ξ₀ d hd hp hD Z U hZ hU
  have hq₁ : fullQ₁ L+2=fullS L := by unfold fullQ₁; omega
  have hu:=(V38Matrix.matrix_upper_budgets (q₁:=fullQ₁ L) order edge (by omega : 3≤fullS L)
    rep hq R ξ₀ k (L+2*k) hq₁ rfl rfl).1
  rw [hD] at hu
  have result:=V42FullProductAlignment.alignment μ ν μI R
    (activity order edge (by omega : 3≤fullS L) rep hq) ξ₀
    (d+k) (L+2*k) k (8*k) (V42Schedule.ownerBudget k)
    (V42Schedule.x L:ℝ) (V42Schedule.theta k:ℝ) (V42Schedule.eta k:ℝ)
    (by omega) g.r_ge g.w_pow g.q_pow g.s_pow g.x_pos g.theta_pos g.eta_pos
    hA hT href hnear g.cap g.exc g.receipt g.init g.wx g.two_x g.loss g.width g.foreign
    g.floor g.pair_margin g.small g.pair_small g.flag g.exception g.theta_le_one
    g.profile_exception g.profile_wx hu
  simpa only [internal,internalHeight,V42FullNearFull.sourceCost,tupleLaw,copyLaw,
    PositiveRationalLaw.toFiniteLaw_iid,k,←hlaw] using result

#print axioms alignment
end CurrentAdditive.V42FullAlignment
