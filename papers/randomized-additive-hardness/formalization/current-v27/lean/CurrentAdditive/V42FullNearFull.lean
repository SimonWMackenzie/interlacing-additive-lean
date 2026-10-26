import CurrentAdditive.V42FullProfiles
import CurrentAdditive.V42SourceNearFullGuards
import CurrentAdditive.V38FullNearFull

/-! The actual unchanged full-product source N, at replacement-v42 eta
and x. Profiles and the collision bound are proved dependencies. -/
namespace CurrentAdditive.V42FullNearFull
open Paper2 Paper2.SourceMatrix Workspace.Types.CommComplexity
open Paper2.SourceSurvivingCollisions
open V42FullSuccessor V42PublicSchedule
open CurrentAdditive.EdgeSourceMatrix
set_option maxHeartbeats 2000000

def sourceCost (d L : ℕ) : ℕ := d+fullExponent L+(L+2*fullExponent L)+fullExponent L+1

variable {X Y V E : Type*} [Fintype X] [Fintype Y] [Fintype V] [Fintype E]
  [Nonempty V]

theorem nearfull
    (L : ℕ) (hL : L=Nat.clog 2 (Fintype.card V))
    (order : Items (fullS L) V ≃ Fin (Fintype.card (Items (fullS L) V)))
    (edge : E → Bool → V) (loopless : ∀ e,edge e false≠edge e true)
    (rep Δ : ℕ) (hΔ : 0<Δ)
    (hq : fullQ₂ L=EdgeSource.sourceQ0 (Fin (4*fullS L)) E*rep)
    (hdegree : ∀ v,SourceItems.degree edge v≤Δ)
    (γ : ℚ) (hγ : 0<γ) (hE : 0<Fintype.card E)
    (hnm : Fintype.card V≤2*Fintype.card E)
    (hdeg : 2*Fintype.card E≤Δ*Fintype.card V)
    (hlarge : V39FullCutoff.sourceCutoff γ Δ≤Fintype.card V)
    (hk : V42Schedule.commonCutoff
      (V38Schedule.sourceDeltaV γ Δ (Fintype.card V) (Fintype.card E))
      (V38Schedule.sourceZeta γ) Δ≤fullExponent L)
    (hb : 4*fullExponent L≤L)
    (gap : ∀ colour : V → Fin 3,(γ:ℝ)*Fintype.card E≤
      ((Finset.univ.filter (fun e => colour (edge e false) = colour (edge e true))).card:ℝ))
    (μ : PositiveRationalLaw X) (ν : PositiveRationalLaw Y) (R : X → Y → Bool)
    (ξ₀ : Tail (fullS L) Y) (d : ℕ) (hd : 3≤d)
    (hp : V38RestrictionProfiles.TwoThresholdProfile R μ.toFiniteLaw ν.toFiniteLaw
      (V42Schedule.rho L:ℝ) (d:ℤ)) (hD : D R=d)
    (W : Set (RawRow (fullQ₁ L) (fullQ₂ L) (fullS L) X (Items (fullS L) V)))
    (U : Set (V38Matrix.TaggedColumn (fullQ₁ L) (fullQ₂ L) (fullS L) Y))
    (hW : 1-(V42Schedule.eta (fullExponent L):ℝ)≤
      (V38Matrix.columnLaw (V:=V) μ (by have := fullS_ge_256 L; omega)).toFiniteLaw.prob (·∈W))
    (hU : 1-(V42Schedule.eta (fullExponent L):ℝ)≤
      (V38Matrix.taggedLaw ν).toFiniteLaw.prob (·∈U)) :
    sourceCost d L≤Compression.restrictionD
      (V38Matrix.matrix order edge (by have := fullS_ge_256 L; omega) rep hq R ξ₀) U W := by
  subst L
  let L:=Nat.clog 2 (Fintype.card V)
  have hL : L=Nat.clog 2 (Fintype.card V) := rfl
  let k:=fullExponent L
  letI : NeZero (V42Schedule.q₁ k) := fullQ₁_neZero L
  letI : NeZero (V42Schedule.q₂ k L) := fullQ₂_neZero L
  have hs : 4≤fullS L := by have := fullS_ge_256 L; omega
  have hn : 0<Fintype.card V := Fintype.card_pos
  obtain ⟨hη,hηsmall,hηtemplate,hallow,hassign,hmargin,hsmall,hprefix,hdominant⟩ :=
    V42SourceNearFullGuards.source_guards_common γ Δ k L
      (Fintype.card V) (Fintype.card E) hγ hΔ hn hE hk hb
  have hallow' : (V42Schedule.eta k:ℝ)≤
      deletionAllowance (V:=V) (E:=E) (γ:ℝ) Δ (fullS L) := by
    simpa only [deletionAllowance,SourceDeletionParameters.eta,vertexTolerance,witnessDensity,
      Fintype.card_fin,k,fullS] using hallow
  obtain ⟨hA,hT,_href⟩ := V42FullProfiles.profiles L hL μ ν R order edge rep hq ξ₀ d hd
    γ Δ hγ hΔ hnm hdeg hlarge hp hD
  have hq2 : 2≤fullQ₂ L := by
    change 2≤2^(L+2*k)
    have hk1 : 1≤L+2*k := by unfold k fullExponent; omega
    simpa only [pow_one] using Nat.pow_le_pow_right (by decide : 1≤2) hk1
  have hx : (0:ℝ)<(V42Schedule.x L:ℝ) := by unfold V42Schedule.x; positivity
  have hηtemplate' : (V42Schedule.eta k:ℝ)*(2^k:ℕ)/(255/256:ℝ)≤1/1000 := by
    change (256/255:ℝ)*(V42Schedule.s k:ℝ)*(V42Schedule.eta k:ℝ)≤1/1000 at hηtemplate
    simp only [V42Schedule.s,Nat.cast_pow,Nat.cast_ofNat] at hηtemplate
    norm_num at hηtemplate ⊢
    nlinarith only [hηtemplate]
  have hρ : (0:ℝ)<(V42Schedule.rho L:ℝ) := by unfold V42Schedule.rho; positivity
  have hcap : 2*(fullS L:ℝ)*(V42Schedule.rho L:ℝ)≤1 := by
    have hsR : (4:ℝ)≤fullS L := by exact_mod_cast hs
    have hmul:=mul_nonneg (show (0:ℝ)≤4*fullS L-2 by linarith)
      (show (0:ℝ)≤(fullS L:ℝ)*(V42Schedule.rho L:ℝ) by positivity)
    change 4*(fullS L:ℝ)^2*(V42Schedule.rho L:ℝ)≤1 at hassign
    nlinarith only [hmul,hassign]
  have hqthree : fullQ₁ L+3=fullS L+1 := by unfold fullQ₁; omega
  have hthree : ∀ (Rows : Set (Fin (fullQ₁ L+3) × X))
      (Words : Set (Fin (fullQ₁ L+3) → Y)),
      (∀ i,2*(fullS L:ℝ)*(V42Schedule.rho L:ℝ)≤μ.toFiniteLaw.prob (fun u=>(i,u)∈Rows)) →
      (1/2:ℝ)<(ν.iid (fullQ₁ L+3)).toFiniteLaw.prob (·∈Words) →
      d+k+1≤Compression.restrictionD (fullInterlace R (fullQ₁ L+3)) Rows Words := by
    intro Rows Words hRows hWords
    exact V39ThreeTail.interlace_lower μ ν R d k (V42Schedule.rho L:ℝ) (by omega) hρ
      rfl hqthree hcap hp Rows Words hRows
      (by simpa only [PositiveRationalLaw.toFiniteLaw_iid] using hWords)
  exact V38FullNearFull.restriction_lower order edge loopless hs rep Δ hΔ hq hdegree
    (γ:ℝ) (by exact_mod_cast hγ) hE gap μ ν R ξ₀ (d+k) (L+2*k) rfl hq2 (by omega)
    (V42Schedule.x L:ℝ) (V42Schedule.rho L:ℝ) (V42Schedule.eta k:ℝ) hx hη
    hηsmall hηtemplate' hallow' hassign hmargin hsmall hprefix hdominant hA hT
    hthree W U hW hU

#print axioms nearfull
end CurrentAdditive.V42FullNearFull
