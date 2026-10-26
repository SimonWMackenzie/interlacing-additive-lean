import CurrentAdditive.V42FullAmplifier
import CurrentAdditive.V42FullCutoff
namespace CurrentAdditive.V42FullAmplifier
open Paper2 Paper2.SourceMatrix Workspace.Types.CommComplexity
open V42FullSuccessor V42PublicSchedule
open CurrentAdditive.EdgeSourceMatrix
variable {V E X Y : Type*} [Fintype V] [Nonempty V] [Fintype E]
  [Fintype X] [Fintype Y] [Nonempty X] [Nonempty Y]
  [DecidableEq V] [DecidableEq E] [DecidableEq X] [DecidableEq Y]
theorem amplifier_public
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
    (μ : PositiveRationalLaw X) (ν : PositiveRationalLaw Y)
    (R : X → Y → Bool) (ξ₀ : Tail (fullS L) Y)
    (d : ℕ) (hd : 3 ≤ d)
    (hp : V38RestrictionProfiles.TwoThresholdProfile R μ.toFiniteLaw ν.toFiniteLaw
      (V42Schedule.rho L:ℝ) (d : ℤ)) (hD : D R=d) :
    D (successor L order edge rep hq R ξ₀)=d+overhead L+1 ∧
    V38RestrictionProfiles.TwoThresholdProfile (successor L order edge rep hq R ξ₀)
      (rowLaw ν L).toFiniteLaw (columnLaw (V := V) μ L).toFiniteLaw
      (V42Schedule.rho L:ℝ) ((d+overhead L+1:ℕ):ℤ) := by
  obtain ⟨hOld,hk,hb,_⟩:=V42FullCutoff.bounds γ Δ (Fintype.card V) (Fintype.card E)
    hγ hΔ Fintype.card_pos hnm hlarge
  rw [←hL] at hk hb
  exact amplifier L hL order edge loopless rep Δ hΔ hq hdegree
    γ hγ hE hnm hdeg hOld hk hb gap μ ν R ξ₀ d hd hp hD

#print axioms amplifier_public
end CurrentAdditive.V42FullAmplifier
