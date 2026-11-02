import CurrentAdditive.V39FullScheduleAlignment
import CurrentAdditive.V39FullIidRestoration
import CurrentAdditive.V38OneStep

/-! The literal full double interlace, with the actual v38 two-family
column law (255/256 ordinary and 1/256 diagonal). The full schedule and
graph promise supply all intermediate alignment and restoration inputs. -/

namespace CurrentAdditive.V39FullAmplifier

open Paper2 Paper2.SourceMatrix Paper2.RankLeaves Workspace.Types.CommComplexity V38Schedule
open CurrentAdditive.EdgeSourceMatrix
open CurrentAdditive.V39FullScheduleAlignment

set_option maxHeartbeats 2000000

private theorem restore_width {A B : Type*} [Fintype A] [Fintype B]
    [Nonempty A] [Nonempty B] (μ : PositiveRationalLaw A) (ν : PositiveRationalLaw B)
    (F : A → B → Bool) (Q r b : ℕ) (hQ : Q=2^r) (hQ0 : 0<Q) (θ δ : ℝ)
    (hC : 3 ≤ D F) (hb : 1 ≤ b) (hθ : 0<θ) (hδ : 0<δ) (hδ1 : δ≤1/64)
    (hwidth : 80*(b:ℝ)≤(Q:ℝ)*δ) (hscale : (Q:ℝ)*θ<1/20)
    (hn : RestrictionLowerBound F μ.toFiniteLaw ν.toFiniteLaw θ (1-δ) (D F:ℤ))
    (hp : V38RestrictionProfiles.TwoThresholdProfile F μ.toFiniteLaw ν.toFiniteLaw θ ((D F:ℤ)-1)) :
    D (fun (z : Fin Q → B) (a : Fin Q × A) => F a.2 (z a.1))=D F+r ∧
    V38RestrictionProfiles.TwoThresholdProfile
      (fun (z : Fin Q → B) (a : Fin Q × A) => F a.2 (z a.1))
      (ν.toFiniteLaw.iid Q) ((FiniteLaw.uniformFin Q hQ0).prod μ.toFiniteLaw)
      ((2:ℝ)^(-(b:ℝ))) ((D F+r:ℕ):ℤ) := by
  subst Q
  exact V39FullIidRestoration.rational_restoration μ ν F r b θ δ
    hC hb hθ hδ hδ1 (by exact_mod_cast hwidth) (by exact_mod_cast hscale) hn hp

def overhead (L : ℕ) : ℕ := L+64+28*ell L

theorem height_eq (d L : ℕ) : internalHeight d L+fullQlog L=d+overhead L+1 := by
  rw [internalHeight_eq]
  unfold fullQlog overhead
  omega

variable {V E X Y : Type*} [Fintype V] [Nonempty V] [Fintype E]
  [Fintype X] [Fintype Y] [Nonempty X] [Nonempty Y]
  [DecidableEq V] [DecidableEq E] [DecidableEq X] [DecidableEq Y]

instance fullQ_neZero (L : ℕ) : NeZero (fullQ L) := by
  constructor
  unfold fullQ V38Schedule.fullW
  positivity

noncomputable def successor (L : ℕ)
    (order : Items (fullS L) V ≃ Fin (Fintype.card (Items (fullS L) V)))
    (edge : E → Bool → V) (rep : ℕ)
    (hq : fullQ₂ L=EdgeSource.sourceQ0 (Fin (4*fullS L)) E*rep)
    (R : X → Y → Bool) (ξ₀ : Tail (fullS L) Y) :
    (Fin (fullQ L) → Fin (V38Schedule.fullW L) × V38Matrix.TaggedColumn (fullQ₁ L) (fullQ₂ L) (fullS L) Y) →
    (Fin (fullQ L) × (Fin (V38Schedule.fullW L) → RawRow (fullQ₁ L) (fullQ₂ L) (fullS L) X (Items (fullS L) V))) → Bool :=
  fun z a => matrix L order edge rep hq R ξ₀ a.2 (z a.1)

noncomputable def rowLaw (ν : PositiveRationalLaw Y) (L : ℕ) :=
  V38OneStep.successorRowLaw (q₁ := fullQ₁ L) (q₂ := fullQ₂ L)
    (s := fullS L) (w := V38Schedule.fullW L) (Q := fullQ L) ν

noncomputable def columnLaw (μ : PositiveRationalLaw X) (L : ℕ) :=
  V38OneStep.successorColumnLaw (q₁ := fullQ₁ L) (q₂ := fullQ₂ L)
    (s := fullS L) (V := V) (w := V38Schedule.fullW L) (Q := fullQ L) μ
    (by have := fullS_ge_256 L; omega)

theorem amplifier
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
    D (successor L order edge rep hq R ξ₀)=d+overhead L+1 ∧
    V38RestrictionProfiles.TwoThresholdProfile (successor L order edge rep hq R ξ₀)
      (rowLaw ν L).toFiniteLaw (columnLaw (V := V) μ L).toFiniteLaw
      ((fullRho L : ℚ) : ℝ) ((d+overhead L+1:ℕ):ℤ) := by
  classical
  let n := Fintype.card V
  let m := Fintype.card E
  let c := fullConstant γ Δ n m
  have hn : 0<n := Fintype.card_pos
  have ht := V39FullCutoff.fullPublicTests_all_large γ Δ n m hγ hΔ hn hnm hdeg hlarge
  rw [←hL] at ht
  obtain ⟨h0,hc,_,_,_⟩ := V39PublicSchedule.fullConstant_interval γ Δ n m hγ hΔ hn hnm
  have hc0 : 0<c := h0.trans_le hc
  have g := V39FullAlignmentGuards.guards_of_tests c (sourceDeltaV γ Δ n m)
    (sourceZeta γ) L m hc0 ht
  let μW := (V38Matrix.columnLaw (q₁ := fullQ₁ L) (q₂ := fullQ₂ L) (s := fullS L)
    (V := V) μ (by have := fullS_ge_256 L; omega)).iid (V38Schedule.fullW L)
  let νW := (PositiveRationalLaw.uniform (Fin (V38Schedule.fullW L))).prod
    (V38Matrix.taggedLaw (q₁ := fullQ₁ L) (q₂ := fullQ₂ L) (s := fullS L) ν)
  let θ : ℝ := ((theta (fullQ L):ℚ):ℝ)
  let δ : ℝ := ((fullEta c L:ℚ):ℝ)/(16*V38Schedule.fullW L)
  have hwpos : (0:ℝ)<V38Schedule.fullW L := by unfold V38Schedule.fullW; positivity
  have hδ : 0<δ := div_pos g.eta_pos (by positivity)
  have hδ1 : δ≤1/64 := by
    dsimp [δ]
    rw [div_le_iff₀ (by positivity)]
    have hw4 : (4:ℝ)≤V38Schedule.fullW L := by
      rw [g.w_pow]
      exact_mod_cast (show 4≤2^(8*ell L) by
        calc 4=2^2 := by norm_num
             _≤2^(8*ell L) := Nat.pow_le_pow_right (by decide) g.r_ge)
    linarith [g.eta_le_one]
  have hwidth : 80*(L:ℝ)≤(fullQ L:ℝ)*δ := by
    have hh := ht.2.1
    unfold deltaU at hh
    have hh' := (show (80*L:ℚ) ≤ (fullQ L:ℚ)*(fullEta c L/(16*V38Schedule.fullW L)) from by simpa only [Nat.cast_mul,Nat.cast_ofNat] using hh)
    dsimp [δ]
    exact_mod_cast hh'
  have hscale : (fullQ L:ℝ)*θ<1/20 := by
    have hh := congrArg (fun q:ℚ => (q:ℝ)) (full_Qtheta L)
    push_cast at hh
    dsimp [θ]
    linarith
  obtain ⟨hcost,hprof,hnear⟩ := V39FullScheduleAlignment.alignment L hL order edge loopless rep Δ hΔ hq
    hdegree γ hγ hE hnm hdeg hlarge gap μ ν R ξ₀ d hd hp hD
  have hμW : μW.toFiniteLaw=tupleLaw (V := V) μ L := by
    simp only [μW,PositiveRationalLaw.toFiniteLaw_iid,tupleLaw]
  have hνW : νW.toFiniteLaw=copyLaw ν L := rfl
  have hnW : RestrictionLowerBound (matrix L order edge rep hq R ξ₀)
      μW.toFiniteLaw νW.toFiniteLaw θ (1-δ) (D (matrix L order edge rep hq R ξ₀):ℤ) := by
    intro Z U hZ hU
    rw [hμW] at hZ
    rw [hνW] at hU
    rw [hcost]
    exact_mod_cast hnear U Z hU hZ
  rw [←hμW,←hνW,←hcost] at hprof
  have hr := restore_width μW νW (matrix L order edge rep hq R ξ₀)
    (fullQ L) (fullQlog L) L (fullQ_pow L) (by unfold fullQ V38Schedule.fullW; positivity) θ δ
    (by rw [hcost,internalHeight_eq]; omega) (by have := ht.2.2.1; omega)
    g.theta_pos hδ hδ1 hwidth hscale hnW hprof
  have hρ : (2:ℝ)^(-(L:ℝ))=((fullRho L:ℚ):ℝ) := by
    rw [Real.rpow_neg (by norm_num : (0:ℝ)≤2),Real.rpow_natCast]
    simp [fullRho]
  rw [hcost,height_eq,hρ] at hr
  have huf : FiniteLaw.uniformFin (fullQ L) (by unfold fullQ V38Schedule.fullW; positivity)=
      (PositiveRationalLaw.uniform (Fin (fullQ L))).toFiniteLaw := by
    apply FiniteLaw.eq_of_weight_eq
    funext z
    simp [FiniteLaw.uniformFin,PositiveRationalLaw.uniform,PositiveRationalLaw.toFiniteLaw]
  rw [huf] at hr
  simpa only [successor,rowLaw,columnLaw,μW,νW,V38OneStep.successorRowLaw,
    V38OneStep.successorColumnLaw,PositiveRationalLaw.toFiniteLaw_iid,
    PositiveRationalLaw.toFiniteLaw_prod] using hr

/-- Both selector protocols are charged once, on the same literal matrix
that appears in the NO/profile theorem. -/
theorem upper
    (L : ℕ)
    (order : Items (fullS L) V ≃ Fin (Fintype.card (Items (fullS L) V)))
    (edge : E → Bool → V) (rep : ℕ)
    (hq : fullQ₂ L=EdgeSource.sourceQ0 (Fin (4*fullS L)) E*rep)
    (R : X → Y → Bool) (ξ₀ : Tail (fullS L) Y) :
    D (successor L order edge rep hq R ξ₀) ≤ D R+overhead L+1 ∧
    (∀ colour : V → Fin 3, (∀ e, colour (edge e false)≠colour (edge e true)) →
      D (successor L order edge rep hq R ξ₀) ≤ D R+overhead L) := by
  classical
  have hs : 3≤fullS L := by have := fullS_ge_256 L; omega
  have hq₁ : fullQ₁ L+2=fullS L := by unfold fullQ₁; omega
  have hq₂ : fullQ₂ L=2^(L+2*(16+ell L)) := by
    unfold fullQ₂ fullS
    rw [←pow_mul,←pow_add]
    congr 1
    omega
  have hu := V38Matrix.matrix_upper_budgets (q₁ := fullQ₁ L) order edge hs rep hq R ξ₀
    (16+ell L) (L+2*(16+ell L)) hq₁ rfl hq₂
  have hw : V38Schedule.fullW L=2^(8*ell L) := rfl
  have hW : D (matrix L order edge rep hq R ξ₀) ≤
      8*ell L+D (V38Matrix.matrix (q₁ := fullQ₁ L) order edge hs rep hq R ξ₀) := by
    have hh := Paper2.fullInterlace_transpose_D_le
      (V38Matrix.matrix (q₁ := fullQ₁ L) order edge hs rep hq R ξ₀) (V38Schedule.fullW L)
      (by unfold V38Schedule.fullW; positivity)
    rw [hw,Nat.clog_pow 2 _ (by decide)] at hh
    exact hh
  have hS : D (successor L order edge rep hq R ξ₀) ≤
      fullQlog L+D (matrix L order edge rep hq R ξ₀) := by
    have hh := Paper2.fullInterlace_transpose_D_le (matrix L order edge rep hq R ξ₀)
      (fullQ L) (by unfold fullQ V38Schedule.fullW; positivity)
    rw [show Nat.clog 2 (fullQ L)=fullQlog L by
      rw [fullQ_pow,Nat.clog_pow 2 _ (by decide)]] at hh
    exact hh
  constructor
  · have := hu.1
    unfold overhead fullQlog at *
    omega
  · intro colour proper
    have := hu.2 colour proper
    unfold overhead fullQlog at *
    omega

/-- The two literal interlaces multiply the actual current two-family
source rank by their widths. -/
theorem rank_le
    (L : ℕ) (hn : Fintype.card V≤2^L)
    (order : Items (fullS L) V ≃ Fin (Fintype.card (Items (fullS L) V)))
    (edge : E → Bool → V) (rep : ℕ)
    (hq : fullQ₂ L=EdgeSource.sourceQ0 (Fin (4*fullS L)) E*rep)
    (R : X → Y → Bool) (ξ₀ : Tail (fullS L) Y) :
    (realMatrix (successor L order edge rep hq R ξ₀)).rank≤
      2^overhead L*(realMatrix R).rank := by
  classical
  have hs : 3≤fullS L := by have := fullS_ge_256 L; omega
  have hsq : 2*fullS L+2≤(fullS L)^2 := by nlinarith
  have ha : 1≤2^L := Nat.one_le_two_pow
  have hkey : 2*(Fintype.card V+fullS L)≤fullQ₂ L := by
    unfold fullQ₂
    have hm := Nat.mul_le_mul_left (2^L) hsq
    nlinarith
  have hI : Fintype.card (Items (fullS L) V)≤2*fullS L*fullQ₂ L := by
    simp only [Items,Fintype.card_prod,Fintype.card_fin,Fintype.card_sum]
    have hm := Nat.mul_le_mul_left (2*fullS L) hkey
    have hsub : fullS L-3≤fullS L := Nat.sub_le _ _
    nlinarith
  have hN := V38Matrix.matrix_rank_le (q₁ := fullQ₁ L) order edge hs rep hq R ξ₀
  have hW : (realMatrix (V39FullScheduleAlignment.matrix L order edge rep hq R ξ₀)).rank≤
      V38Schedule.fullW L*(realMatrix (V38Matrix.matrix (q₁ := fullQ₁ L) order edge hs rep hq R ξ₀)).rank := by
    have hh := fullInterlace_rank_le (V38Matrix.matrix (q₁ := fullQ₁ L) order edge hs rep hq R ξ₀)
      (V38Schedule.fullW L)
    change (realMatrix (fun z a => fullInterlace
      (V38Matrix.matrix (q₁ := fullQ₁ L) order edge hs rep hq R ξ₀) (V38Schedule.fullW L) a z)).rank≤_
    rw [transpose_rank]
    exact hh
  have hS : (realMatrix (successor L order edge rep hq R ξ₀)).rank≤
      fullQ L*(realMatrix (V39FullScheduleAlignment.matrix L order edge rep hq R ξ₀)).rank := by
    change (realMatrix (fun z a => fullInterlace
      (V39FullScheduleAlignment.matrix L order edge rep hq R ξ₀) (fullQ L) a z)).rank≤_
    rw [transpose_rank]
    exact fullInterlace_rank_le _ _
  have hfactor : fullS L*fullQ₁ L*fullQ₂ L+Fintype.card (Items (fullS L) V)≤
      (fullS L)^2*fullQ₂ L := by
    have hq₁ : fullQ₁ L+2=fullS L := by unfold fullQ₁; omega
    calc _≤fullS L*fullQ₁ L*fullQ₂ L+2*fullS L*fullQ₂ L := Nat.add_le_add_left hI _
         _=fullS L*(fullQ₁ L+2)*fullQ₂ L := by ring
         _=_ := by rw [hq₁]; ring
  have hpow : fullQ L*V38Schedule.fullW L*((fullS L)^2*fullQ₂ L)=2^overhead L := by
    rw [fullQ_pow]
    simp only [fullQ₂,fullS,V38Schedule.fullW,←pow_mul,←pow_add]
    congr 1
    unfold overhead fullQlog
    omega
  calc
    _≤fullQ L*(V38Schedule.fullW L*((fullS L*fullQ₁ L*fullQ₂ L+
        Fintype.card (Items (fullS L) V))*(realMatrix R).rank)) :=
      hS.trans (Nat.mul_le_mul_left _ (hW.trans (Nat.mul_le_mul_left _ hN)))
    _≤fullQ L*(V38Schedule.fullW L*(((fullS L)^2*fullQ₂ L)*(realMatrix R).rank)) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hfactor))
    _=(fullQ L*V38Schedule.fullW L*((fullS L)^2*fullQ₂ L))*(realMatrix R).rank := by ring
    _=_ := by rw [hpow]

#print axioms amplifier
#print axioms upper
#print axioms rank_le

end CurrentAdditive.V39FullAmplifier
