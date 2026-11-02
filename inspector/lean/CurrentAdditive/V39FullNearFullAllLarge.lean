import CurrentAdditive.V38FullNearFull
import CurrentAdditive.V39NearFullMargins
import CurrentAdditive.V39SourceProfilesAllLarge

/-! The full-product source near-full theorem at the proved public cutoff.
Only the actual graph promise, base profile and base exact cost are inputs;
all source profiles, numerical tests, prefixes, witnesses and local costs
are supplied by their proved constructors. -/

namespace CurrentAdditive.V39FullNearFullAllLarge

open Paper2 Paper2.SourceMatrix Paper2.SourceProjection
open Paper2.SourceSurvivingCollisions V38Schedule
open CurrentAdditive.EdgeSourceMatrix CurrentAdditive.V38Matrix
open Workspace.Types.CommComplexity

instance fullS_neZero (L : ℕ) : NeZero (fullS L) := ⟨by unfold fullS; positivity⟩
instance fullQ₁_neZero (L : ℕ) : NeZero (fullQ₁ L) := by
  have hs := fullS_ge_256 L
  constructor
  unfold fullQ₁
  omega
instance fullQ₂_neZero (L : ℕ) : NeZero (fullQ₂ L) := by
  constructor
  unfold fullQ₂
  exact mul_ne_zero (pow_ne_zero _ (by decide)) (pow_ne_zero _ (NeZero.ne _))

def sourceCost (d L : ℕ) : ℕ := d+(16+ell L)+(L+2*(16+ell L))+(16+ell L)+1

theorem restriction_lower
    {V E X Y : Type*} [Fintype V] [Nonempty V] [Fintype E]
    [Fintype X] [Fintype Y]
    (L : ℕ) (hL : L=Nat.clog 2 (Fintype.card V))
    (order : Items (fullS L) V ≃ Fin (Fintype.card (Items (fullS L) V)))
    (edge : E → Bool → V) (loopless : ∀ e, edge e false ≠ edge e true)
    (r Δ : ℕ) (hΔ : 0 < Δ)
    (hsourceq : fullQ₂ L = EdgeSource.sourceQ0 (Fin (4*fullS L)) E*r)
    (hdegree : ∀ v, SourceItems.degree edge v ≤ Δ)
    (γ : ℚ) (hγ : 0 < γ) (hE : 0 < Fintype.card E)
    (hnm : Fintype.card V ≤ 2*Fintype.card E)
    (hdeg : 2*Fintype.card E ≤ Δ*Fintype.card V)
    (hlarge : V39FullCutoff.sourceCutoff γ Δ ≤ Fintype.card V)
    (gap : ∀ colour : V → Fin 3, (γ : ℝ)*Fintype.card E ≤
      ((Finset.univ.filter (fun e => colour (edge e false) = colour (edge e true))).card : ℝ))
    (μ : PositiveRationalLaw X) (ν : PositiveRationalLaw Y)
    (R : X → Y → Bool) (ξ₀ : Tail (fullS L) Y)
    (d : ℕ) (hd : 3 ≤ d)
    (hp : V38RestrictionProfiles.TwoThresholdProfile R μ.toFiniteLaw ν.toFiniteLaw
      ((fullRho L : ℚ) : ℝ) (d : ℤ)) (hD : D R=d)
    (W : Set (RawRow (fullQ₁ L) (fullQ₂ L) (fullS L) X (Items (fullS L) V)))
    (U : Set (V38Matrix.TaggedColumn (fullQ₁ L) (fullQ₂ L) (fullS L) Y))
    (hW : 1-((fullEta (fullConstant γ Δ (Fintype.card V) (Fintype.card E)) L : ℚ) : ℝ) ≤
      (V38Matrix.columnLaw (V := V) μ (by have := fullS_ge_256 L; omega : 4 ≤ fullS L)).toFiniteLaw.prob (· ∈ W))
    (hU : 1-((fullEta (fullConstant γ Δ (Fintype.card V) (Fintype.card E)) L : ℚ) : ℝ) ≤
      (V38Matrix.taggedLaw ν).toFiniteLaw.prob (· ∈ U)) :
    sourceCost d L ≤ Compression.restrictionD
      (V38Matrix.matrix order edge (by have := fullS_ge_256 L; omega : 3 ≤ fullS L)
        r hsourceq R ξ₀) U W := by
  classical
  have hs : 4 ≤ fullS L := by have := fullS_ge_256 L; omega
  have hn : 0 < Fintype.card V := Fintype.card_pos
  have hγR : (0 : ℝ) < γ := by exact_mod_cast hγ
  have hdv := vertexTolerance_pos (V := V) (E := E) (γ : ℝ) Δ hγR hΔ hE
  have hz : (0 : ℝ) < witnessDensity (γ : ℝ) := by unfold witnessDensity; positivity
  have htests := V39FullCutoff.fullPublicTests_all_large γ Δ
    (Fintype.card V) (Fintype.card E) hγ hΔ hn hnm hdeg hlarge
  rw [← hL] at htests
  rcases htests.1 with ⟨_hs,_heta,_hq,h4,hcount,hqx,hsx,_rest⟩
  change 4*(fullS L : ℚ)^2*fullRho L ≤ 1 at h4
  change 8*(fullS L : ℚ)*fullQ₁ L ≤ sourceZeta γ*fullQ₂ L/16 at hcount
  change (fullQ₂ L : ℚ)*fullX L ≤ 1/10000 at hqx
  change (fullS L : ℚ)*fullX L ≤ 1/10000 at hsx
  have h4R : 4*(fullS L : ℝ)^2*((fullRho L : ℚ) : ℝ) ≤ 1 := by exact_mod_cast h4
  have hx : (0 : ℝ) < ((fullX L : ℚ) : ℝ) := by
    unfold fullX
    norm_num only [Rat.cast_div,Rat.cast_one,Rat.cast_pow,Rat.cast_ofNat]
    positivity
  have hcountR : 8*(fullS L : ℝ)*fullQ₁ L ≤ witnessDensity (γ : ℝ)*fullQ₂ L/16 := by
    unfold sourceZeta at hcount
    unfold witnessDensity
    exact_mod_cast hcount
  have hqxR : (fullQ₂ L : ℝ)*((fullX L : ℚ) : ℝ) ≤ 1/10000 := by
    have hh : ((((fullQ₂ L : ℚ)*fullX L : ℚ)) : ℝ) ≤ ((1/10000 : ℚ) : ℝ) := by exact_mod_cast hqx
    simpa only [Rat.cast_mul,Rat.cast_natCast,Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] using hh
  have hsxR : (fullS L : ℝ)*((fullX L : ℚ) : ℝ) ≤ 1/10000 := by
    have hh : ((((fullS L : ℚ)*fullX L : ℚ)) : ℝ) ≤ ((1/10000 : ℚ) : ℝ) := by exact_mod_cast hsx
    simpa only [Rat.cast_mul,Rat.cast_natCast,Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] using hh
  have hm := V39NearFullMargins.numeric_margins (fullS L) (fullQ₁ L) (fullQ₂ L)
    hs (NeZero.pos _) (vertexTolerance (V := V) (E := E) (γ : ℝ) Δ)
    (witnessDensity (γ : ℝ)) ((fullX L : ℚ) : ℝ) hdv hz hx hcountR hsxR hqxR
  have heta := V39NearFullMargins.full_eta_eq_deletionAllowance (V := V) (E := E) γ Δ L
  change ((fullEta (fullConstant γ Δ (Fintype.card V) (Fintype.card E)) L : ℚ) : ℝ) =
    SourceDeletionParameters.eta (fullS L)
      (vertexTolerance (V := V) (E := E) (γ : ℝ) Δ) (witnessDensity (γ : ℝ)) at heta
  simp only [← heta] at hm
  obtain ⟨hη,hηsmall,hηtemplate,hmargin,hsmall,hgap,hdom⟩ := hm
  have hq₂ : fullQ₂ L=2^(L+2*(16+ell L)) := by
    unfold fullQ₂ fullS
    rw [← pow_mul,← pow_add]
    congr 1
    omega
  have hq2 : 2 ≤ fullQ₂ L := by
    rw [hq₂]
    have hb : 1 ≤ L+2*(16+ell L) := by omega
    simpa only [pow_one] using (Nat.pow_le_pow_right (by decide : 1 ≤ 2) hb)
  have hps := V39FullScheduledSource.costs_and_profiles
    (q₁ := fullQ₁ L) (q₂ := fullQ₂ L) (s := fullS L) μ ν R order edge hs r hsourceq
    ξ₀ d hd (fullConstant γ Δ (Fintype.card V) (Fintype.card E))
    (sourceDeltaV γ Δ (Fintype.card V) (Fintype.card E)) (sourceZeta γ)
    L (Fintype.card E) rfl rfl rfl htests.1 hp hD
  dsimp only at hps
  obtain ⟨_hDA,_hDT,hpA,hpT,_hpref⟩ := hps
  have hρ : (0 : ℝ) < ((fullRho L : ℚ) : ℝ) := by
    unfold fullRho
    norm_num only [Rat.cast_div,Rat.cast_one,Rat.cast_pow,Rat.cast_ofNat]
    positivity
  have hcap : 2*(fullS L : ℝ)*((fullRho L : ℚ) : ℝ) ≤ 1 := by
    have hsR : (4 : ℝ) ≤ fullS L := by exact_mod_cast hs
    have hmul := mul_nonneg (show (0 : ℝ) ≤ 4*fullS L-2 by linarith)
      (show (0 : ℝ) ≤ (fullS L : ℝ)*((fullRho L : ℚ) : ℝ) by positivity)
    nlinarith only [hmul,h4R]
  have hqthree : fullQ₁ L+3=fullS L+1 := by unfold fullQ₁; omega
  have hthree : ∀ (Rows : Set (Fin (fullQ₁ L+3) × X))
      (Words : Set (Fin (fullQ₁ L+3) → Y)),
      (∀ i, 2*(fullS L : ℝ)*((fullRho L : ℚ) : ℝ) ≤
        μ.toFiniteLaw.prob (fun u => (i,u) ∈ Rows)) →
      (1/2 : ℝ) < (ν.iid (fullQ₁ L+3)).toFiniteLaw.prob (· ∈ Words) →
      d+(16+ell L)+1 ≤ Compression.restrictionD (fullInterlace R (fullQ₁ L+3)) Rows Words := by
    intro Rows Words hRows hWords
    exact V39ThreeTail.interlace_lower μ ν R d (16+ell L)
      ((fullRho L : ℚ) : ℝ) (by omega) hρ rfl hqthree hcap hp Rows Words hRows
      (by simpa only [PositiveRationalLaw.toFiniteLaw_iid] using hWords)
  exact V38FullNearFull.restriction_lower order edge loopless hs r Δ hΔ hsourceq
    hdegree (γ : ℝ) hγR hE gap μ ν R ξ₀ (d+(16+ell L)) (L+2*(16+ell L))
    hq₂ hq2 (by omega) ((fullX L : ℚ) : ℝ) ((fullRho L : ℚ) : ℝ)
    ((fullEta (fullConstant γ Δ (Fintype.card V) (Fintype.card E)) L : ℚ) : ℝ)
    hx hη hηsmall hηtemplate (V39NearFullMargins.full_eta_eq_deletionAllowance γ Δ L).le
    h4R hmargin hsmall
    (by simpa only [fullS,Nat.cast_pow,Nat.cast_ofNat] using hgap) hdom hpA hpT hthree W U hW hU

end CurrentAdditive.V39FullNearFullAllLarge

#print axioms CurrentAdditive.V39FullNearFullAllLarge.fullS_neZero
#print axioms CurrentAdditive.V39FullNearFullAllLarge.fullQ₁_neZero
#print axioms CurrentAdditive.V39FullNearFullAllLarge.fullQ₂_neZero
#print axioms CurrentAdditive.V39FullNearFullAllLarge.sourceCost
#print axioms CurrentAdditive.V39FullNearFullAllLarge.restriction_lower
