import CurrentAdditive.V39FullNearFullAllLarge

/-! Match the proved near-full lower bound with the universal upper
protocol for the very same selected two-family source matrix. -/

namespace CurrentAdditive.V39FullNearFullAllLarge

open Paper2 Paper2.SourceMatrix Paper2.SourceProjection
open Paper2.SourceSurvivingCollisions V38Schedule
open CurrentAdditive.EdgeSourceMatrix CurrentAdditive.V38Matrix
open Workspace.Types.CommComplexity

theorem cost_eq
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
      ((fullRho L : ℚ) : ℝ) (d : ℤ)) (hD : D R=d) :
    D (V38Matrix.matrix (q₁ := fullQ₁ L) order edge
      (by have := fullS_ge_256 L; omega : 3 ≤ fullS L) r hsourceq R ξ₀) = sourceCost d L := by
  classical
  let M := V38Matrix.matrix (q₁ := fullQ₁ L) order edge
    (by have := fullS_ge_256 L; omega : 3 ≤ fullS L) r hsourceq R ξ₀
  have hγR : (0 : ℝ) < γ := by exact_mod_cast hγ
  have hdv := vertexTolerance_pos (V := V) (E := E) (γ : ℝ) Δ hγR hΔ hE
  have hz : (0 : ℝ) < witnessDensity (γ : ℝ) := by unfold witnessDensity; positivity
  have hη : 0 ≤ ((fullEta (fullConstant γ Δ (Fintype.card V) (Fintype.card E)) L : ℚ) : ℝ) := by
    rw [V39NearFullMargins.full_eta_eq_deletionAllowance γ Δ L]
    exact (SourceDeletionParameters.eta_pos (fullS L) (NeZero.pos _)
      (vertexTolerance (V := V) (E := E) (γ : ℝ) Δ) (witnessDensity (γ : ℝ)) hdv hz).le
  have hl := restriction_lower L hL order edge loopless r Δ hΔ hsourceq hdegree
    γ hγ hE hnm hdeg hlarge gap μ ν R ξ₀ d hd hp hD Set.univ Set.univ
    (by simpa only [Set.mem_univ,FiniteLaw.prob_true] using
      (show 1-((fullEta (fullConstant γ Δ (Fintype.card V) (Fintype.card E)) L : ℚ) : ℝ) ≤ 1 by linarith))
    (by simpa only [Set.mem_univ,FiniteLaw.prob_true] using
      (show 1-((fullEta (fullConstant γ Δ (Fintype.card V) (Fintype.card E)) L : ℚ) : ℝ) ≤ 1 by linarith))
  have hsub : Compression.restrictionD M Set.univ Set.univ ≤ D M :=
    Workspace.ProofLemmas.SublemmaPrecompNoIncrease M
      (fun a : (Set.univ : Set (V38Matrix.TaggedColumn (fullQ₁ L) (fullQ₂ L) (fullS L) Y)) => a.val)
      (fun a : (Set.univ : Set (RawRow (fullQ₁ L) (fullQ₂ L) (fullS L) X (Items (fullS L) V))) => a.val)
  have hlower : sourceCost d L ≤ D M := hl.trans hsub
  have hq₁ : fullQ₁ L+2=fullS L := by
    have := fullS_ge_256 L
    unfold fullQ₁
    omega
  have hq₂ : fullQ₂ L=2^(L+2*(16+ell L)) := by
    unfold fullQ₂ fullS
    rw [← pow_mul,← pow_add]
    congr 1
    omega
  have hu := (V38Matrix.matrix_upper_budgets order edge
    (by have := fullS_ge_256 L; omega : 3 ≤ fullS L) r hsourceq R ξ₀
    (16+ell L) (L+2*(16+ell L)) hq₁ rfl hq₂).1
  rw [hD] at hu
  have hupper : D M ≤ sourceCost d L := by
    simpa only [M,sourceCost] using hu
  exact Nat.le_antisymm hupper hlower

end CurrentAdditive.V39FullNearFullAllLarge

#print axioms CurrentAdditive.V39FullNearFullAllLarge.cost_eq
