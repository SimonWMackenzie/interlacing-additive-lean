import CurrentAdditive.V42FullAlignment
import CurrentAdditive.V42PublicCutoff
import CurrentAdditive.V42FullIidRestoration
namespace CurrentAdditive.V42FullAmplifier
open Paper2 Paper2.SourceMatrix Workspace.Types.CommComplexity
open V42FullSuccessor V42PublicSchedule V42FullAlignment
set_option maxHeartbeats 2000000

private theorem restore_width {A B : Type*} [Fintype A] [Fintype B]
    [Nonempty A] [Nonempty B] (μ : PositiveRationalLaw A) (ν : PositiveRationalLaw B)
    (F : A → B → Bool) (Q r b : ℕ) (hQ : Q=2^r) (hQ0 : 0<Q) (θ δ : ℝ)
    (hC : 3 ≤ D F) (hb : 1 ≤ b) (hθ : 0<θ) (hδ : 0<δ) (hδ1 : δ≤1/64)
    (hwidth : 80*(b:ℝ)≤(Q:ℝ)*δ) (hscale : (Q:ℝ)*θ≤1/20)
    (hn : RestrictionLowerBound F μ.toFiniteLaw ν.toFiniteLaw θ (1-δ) (D F:ℤ))
    (hp : V38RestrictionProfiles.TwoThresholdProfile F μ.toFiniteLaw ν.toFiniteLaw θ ((D F:ℤ)-1)) :
    D (fun (z : Fin Q → B) (a : Fin Q × A) => F a.2 (z a.1))=D F+r ∧
    V38RestrictionProfiles.TwoThresholdProfile
      (fun (z : Fin Q → B) (a : Fin Q × A) => F a.2 (z a.1))
      (ν.toFiniteLaw.iid Q) ((FiniteLaw.uniformFin Q hQ0).prod μ.toFiniteLaw)
      ((2:ℝ)^(-(b:ℝ))) ((D F+r:ℕ):ℤ) := by
  subst Q
  exact V42FullIidRestoration.rational_restoration μ ν F r b θ δ
    hC hb hθ hδ hδ1 (by exact_mod_cast hwidth) (by exact_mod_cast hscale) hn hp

variable {V E X Y : Type*} [Fintype V] [Nonempty V] [Fintype E]
  [Fintype X] [Fintype Y] [Nonempty X] [Nonempty Y]
  [DecidableEq V] [DecidableEq E] [DecidableEq X] [DecidableEq Y]
open CurrentAdditive.EdgeSourceMatrix

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
    (hk : V42Schedule.commonCutoff (V38Schedule.sourceDeltaV γ Δ (Fintype.card V) (Fintype.card E))
      (V38Schedule.sourceZeta γ) Δ ≤ fullExponent L) (hb : 4*fullExponent L≤L)
    (gap : ∀ colour : V → Fin 3, (γ : ℝ)*Fintype.card E ≤
      ((Finset.univ.filter (fun e => colour (edge e false)=colour (edge e true))).card : ℝ))
    (μ : PositiveRationalLaw X) (ν : PositiveRationalLaw Y)
    (R : X → Y → Bool) (ξ₀ : Tail (fullS L) Y)
    (d : ℕ) (hd : 3 ≤ d)
    (hp : V38RestrictionProfiles.TwoThresholdProfile R μ.toFiniteLaw ν.toFiniteLaw
      (V42Schedule.rho L:ℝ) (d : ℤ)) (hD : D R=d) :
    D (successor L order edge rep hq R ξ₀)=d+overhead L+1 ∧
    V38RestrictionProfiles.TwoThresholdProfile (successor L order edge rep hq R ξ₀)
      (rowLaw ν L).toFiniteLaw (columnLaw (V := V) μ L).toFiniteLaw
      (V42Schedule.rho L:ℝ) ((d+overhead L+1:ℕ):ℤ) := by
  classical
  let k:=fullExponent L
  have hk200 : 200≤k := by unfold V42Schedule.commonCutoff at hk; omega
  have hLpos : 1≤L := by
    have hh : 0<fullExponent L := by
      unfold fullExponent
      omega
    omega
  have g:=V42AlignmentGuards.guards k L hk200 hb
  let μW:=(V38Matrix.columnLaw (q₁:=fullQ₁ L) (q₂:=fullQ₂ L) (s:=fullS L)
    (V:=V) μ (by have := fullS_ge_256 L; omega)).iid (fullW L)
  let νW:=(PositiveRationalLaw.uniform (Fin (fullW L))).prod
    (V38Matrix.taggedLaw (q₁:=fullQ₁ L) (q₂:=fullQ₂ L) (s:=fullS L) ν)
  let θ:ℝ:=(V42Schedule.theta k:ℝ)
  let δ:ℝ:=(V42Schedule.eta k:ℝ)/(16*fullW L)
  have hwpos : (0:ℝ)<fullW L := by unfold fullW V42Schedule.w; positivity
  have hδ : 0<δ := div_pos g.eta_pos (by positivity)
  have hδ1 : δ≤1/64 := by
    dsimp [δ]
    rw [div_le_iff₀ (by positivity)]
    have hw4 : (4:ℝ)≤fullW L := by
      change (4:ℝ)≤(2^(8*k):ℕ)
      exact_mod_cast (show 4≤2^(8*k) by
        calc 4=2^2 := by norm_num
             _≤2^(8*k) := Nat.pow_le_pow_right (by decide) g.r_ge)
    linarith [g.eta_le_one]
  have hdUeq : (V42Schedule.deltaU k:ℝ)=δ := by
    have hh:=congrArg (fun z:ℚ=>(z:ℝ)) (V42Schedule.recipe_exact k L).2.2.2.2.2.2
    push_cast at hh
    exact hh
  have hwidth : 80*(L:ℝ)≤(fullQ L:ℝ)*δ := by
    rw [←hdUeq]
    exact_mod_cast V42PublicCutoff.full_restoration_product L
  have hscale : (fullQ L:ℝ)*θ≤1/20 := by
    have hh : (fullQ L:ℝ)*θ=(1:ℝ)/512 := by
      change (V42Schedule.Q k:ℝ)*(V42Schedule.theta k:ℝ)=1/512
      have hh:=congrArg (fun z:ℚ=>(z:ℝ)) (V42Schedule.Q_theta k)
      push_cast at hh
      exact hh
    linarith
  obtain ⟨hcost,hprof,hnear⟩:=V42FullAlignment.alignment L hL order edge loopless rep Δ hΔ hq
    hdegree γ hγ hE hnm hdeg hlarge hk hb gap μ ν R ξ₀ d hd hp hD
  have hμW : μW.toFiniteLaw=tupleLaw (V:=V) μ L := rfl
  have hνW : νW.toFiniteLaw=copyLaw ν L := rfl
  have hnW : RestrictionLowerBound (internal L order edge rep hq R ξ₀)
      μW.toFiniteLaw νW.toFiniteLaw θ (1-δ) (D (internal L order edge rep hq R ξ₀):ℤ) := by
    intro Z U hZ hU
    rw [hμW] at hZ
    rw [hνW] at hU
    rw [hcost]
    exact_mod_cast hnear U Z hU hZ
  rw [←hμW,←hνW,←hcost] at hprof
  have hr:=restore_width μW νW (internal L order edge rep hq R ξ₀)
    (fullQ L) (fullQlog L) L (fullQ_pow L) (by unfold fullQ V42Schedule.Q; positivity) θ δ
    (by rw [hcost]; unfold internalHeight V42FullNearFull.sourceCost; omega) hLpos
    g.theta_pos hδ hδ1 hwidth hscale hnW hprof
  have hheight : internalHeight d L+fullQlog L=d+overhead L+1 := by
    unfold internalHeight V42FullNearFull.sourceCost fullQlog overhead V42PublicSchedule.fullOverhead
    omega
  have hρ : (2:ℝ)^(-(L:ℝ))=(V42Schedule.rho L:ℝ) := by
    rw [Real.rpow_neg (by norm_num : (0:ℝ)≤2),Real.rpow_natCast]
    simp [V42Schedule.rho]
  rw [hcost,hheight,hρ] at hr
  have huf : FiniteLaw.uniformFin (fullQ L) (by unfold fullQ V42Schedule.Q; positivity)=
      (PositiveRationalLaw.uniform (Fin (fullQ L))).toFiniteLaw := by
    apply FiniteLaw.eq_of_weight_eq
    funext z
    simp [FiniteLaw.uniformFin,PositiveRationalLaw.uniform,PositiveRationalLaw.toFiniteLaw]
  rw [huf] at hr
  simpa only [V42FullSuccessor.successor,V42FullSuccessor.rowLaw,V42FullSuccessor.columnLaw,μW,νW,V38OneStep.successorRowLaw,
    V38OneStep.successorColumnLaw,PositiveRationalLaw.toFiniteLaw_iid,
    PositiveRationalLaw.toFiniteLaw_prod] using hr

#print axioms amplifier
end CurrentAdditive.V42FullAmplifier
