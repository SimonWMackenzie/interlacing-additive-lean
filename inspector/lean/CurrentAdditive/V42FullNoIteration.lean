import CurrentAdditive.V42FullIteration
import CurrentAdditive.V42FullAmplifier
import CurrentAdditive.V42FullCutoff
namespace CurrentAdditive.V42FullIteration
open Paper2 Workspace.Types.CommComplexity
open CurrentAdditive.EdgeSourceMatrix
open V42FullSuccessor V42PublicSchedule
set_option maxHeartbeats 2000000
variable {V E : Type} [Fintype V] [Nonempty V] [Fintype E]
  [DecidableEq V] [DecidableEq E]
theorem no_iteration_at_margins
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
    (k : ℕ) :
    D (iterate L order edge rep hq k).matrix=V42PublicSchedule.H L k ∧
    V38RestrictionProfiles.TwoThresholdProfile (iterate L order edge rep hq k).matrix
      (iterate L order edge rep hq k).rowLaw.toFiniteLaw
      (iterate L order edge rep hq k).colLaw.toFiniteLaw
      (V42Schedule.rho L:ℝ) (V42PublicSchedule.H L k:ℤ) := by
  classical
  induction k with
  | zero => simpa [iterate,V42PublicSchedule.H,V42PublicSchedule.B] using seed_cost_profile L
  | succ k ih =>
    let R := iterate L order edge rep hq k
    have hd : 3≤V42PublicSchedule.H L k := by
      unfold V42PublicSchedule.H V42PublicSchedule.B V42PublicSchedule.seedCost
      omega
    have hh := V42FullAmplifier.amplifier L hL order edge loopless rep Δ hΔ hq hdegree
      γ hγ hE hnm hdeg hlarge hk hb gap R.rowLaw R.colLaw R.matrix
      (fun _ => Classical.choice (inferInstance : Nonempty R.Col))
      (V42PublicSchedule.H L k) hd ih.2 ih.1
    simpa only [iterate,next,V42PublicSchedule.H_succ,V42PublicSchedule.fullOverhead,
      V42FullSuccessor.overhead] using hh


theorem no_iteration
    (L : ℕ) (hL : L=Nat.clog 2 (Fintype.card V))
    (order : Items (fullS L) V ≃ Fin (Fintype.card (Items (fullS L) V)))
    (edge : E → Bool → V) (loopless : ∀ e, edge e false ≠ edge e true)
    (rep Δ : ℕ) (hΔ : 0 < Δ)
    (hq : fullQ₂ L=EdgeSource.sourceQ0 (Fin (4*fullS L)) E*rep)
    (hdegree : ∀ v, SourceItems.degree edge v ≤ Δ)
    (γ : ℚ) (hγ : 0 < γ) (hE : 0 < Fintype.card E)
    (hnm : Fintype.card V ≤ 2*Fintype.card E)
    (hdeg : 2*Fintype.card E ≤ Δ*Fintype.card V)
    (hlarge : V42FullCutoff.sourceCutoff γ Δ ≤ Fintype.card V)
    (gap : ∀ colour : V → Fin 3, (γ : ℝ)*Fintype.card E ≤
      ((Finset.univ.filter (fun e => colour (edge e false)=colour (edge e true))).card : ℝ))
    (k : ℕ) :
    D (iterate L order edge rep hq k).matrix=V42PublicSchedule.H L k ∧
    V38RestrictionProfiles.TwoThresholdProfile (iterate L order edge rep hq k).matrix
      (iterate L order edge rep hq k).rowLaw.toFiniteLaw
      (iterate L order edge rep hq k).colLaw.toFiniteLaw
      (V42Schedule.rho L:ℝ) (V42PublicSchedule.H L k:ℤ) := by
  have hbounds:=V42FullCutoff.bounds γ Δ (Fintype.card V) (Fintype.card E)
    hγ hΔ Fintype.card_pos hnm hlarge
  obtain ⟨hOld,hk,hb,_⟩:=hbounds
  rw [←hL] at hk hb
  exact no_iteration_at_margins L hL order edge loopless rep Δ hΔ hq hdegree
    γ hγ hE hnm hdeg hOld hk hb gap k

#print axioms no_iteration_at_margins
#print axioms no_iteration
end CurrentAdditive.V42FullIteration
