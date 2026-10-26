import CurrentAdditive.MomentRoundingV35
import CurrentAdditive.LiteralFirstPassing
import CurrentAdditive.IndexedActualNoContract

/-! The literal first-passing v35 dyadic parameter, rather than the later
v27 safe cap, feeds the actual generated W and finite NO induction. -/

namespace FiniteV35Continuation

open CurrentAdditive.DeterministicParameters
open CurrentAdditive.DeterministicAdmissibility
open CurrentAdditive.PublicScheduleExactAdmissibility
open CurrentAdditive.PublicScheduleLiteralFirstPassing
open CurrentAdditive.IndexedSemanticIteration
open CurrentAdditive.IndexedStagePresentation
open CurrentAdditive.DeterministicETHConcreteIteration
open CurrentAdditive.DeterministicIteration
open CurrentAdditive.DeterministicIndexedMatrix.Sources
open Paper2
open Workspace.Types.CommComplexity

theorem first_literal_production_schedule
    (L n m Δ : ℕ) (γ : ℚ)
    (hΔ : 0 < Δ) (hγ : 0 < γ) (hm : 0 < m)
    (hdegree : 2*m ≤ Δ*n)
    (hL : L = exactPublicLog n m Δ γ) :
    n ≤ N L ∧ Admissible L Δ n m sourceC128Ceil γ ∧
    (∀ k < L, literalTest k n m Δ γ = false) ∧
    N L ≤ 2 * max n (sourceCutoffSize Δ γ) := by
  subst L
  have hs := exactPublicLog_spec n m Δ γ hΔ hγ hm hdegree
  have hprod := literalTest_to_Admissible _ _ _ _ _ hΔ hγ hs.1
  exact ⟨hprod.1, hprod.2, hs.2.1, hs.2.2⟩

section Generated

variable (v e L : ℕ) [NeZero v] [NeZero (s L)] [NeZero (s L-3)]
  [NeZero (q₁ L)] [NeZero (q₂ L)] [NeZero (w L)] [NeZero (Q L)]

omit [NeZero (Q L)] in
/-- The selected first-passing schedule supplies `Admissible` to the
existing theorem about the **actual** generated W. The graph/source/profile
premises are the owner's unchanged premises, on the same matrix. -/
theorem first_literal_actual_full_W_at
    (T : Schedule (Fin v) (Fin e) L)
    (inputs : ∀ R : Stage (N L), StepInputs (V := Fin v) (E := Fin e) L R T)
    (G : CurrentAdditive.IndexedSemanticIteration.Graph (Fin v) (Fin e))
    (Δ : ℕ) (γ : ℚ) (hΔ : 0 < Δ) (hγ : 0 < γ)
    (he : 0 < e) (hcount : 2*e ≤ Δ*v)
    (hfirst : L = exactPublicLog v e Δ γ)
    (hloopless : ∀ z, G z false ≠ G z true)
    (hincident : ∀ z, ∃ a b, G a b = z)
    (hdegree : ∀ z, Paper2.SourceItems.degree G z ≤ Δ)
    (hgap : ∀ colour : Fin v → Fin 3,
      (γ : ℝ) * e ≤
      ((Finset.univ.filter (fun z =>
        colour (G z false) = colour (G z true))).card : ℝ))
    (R : Stage (N L)) (hcost : 3 ≤ D R.matrix)
    (hp : RestrictionProfile R.matrix R.rowLaw.toFiniteLaw
      R.colLaw.toFiniteLaw (ρ L : ℝ) (D R.matrix : ℤ)) :
    FullWAt v e L T inputs G Δ γ R := by
  have hadm := (first_literal_production_schedule L v e Δ γ hΔ hγ
    he hcount hfirst).2.1
  exact actual_full_W_at v e L T inputs G Δ γ hΔ hγ
    hloopless hincident hdegree hgap hadm R hcost hp

/-- The same literal first-passing log feeds the existing complete finite
NO induction; no later rounded test or cap is selected. -/
theorem first_literal_actual_no_contract
    (T : Schedule (Fin v) (Fin e) L)
    (inputs : ∀ R : Stage (N L), StepInputs (V := Fin v) (E := Fin e) L R T)
    (G : CurrentAdditive.IndexedSemanticIteration.Graph (Fin v) (Fin e))
    (Δ : ℕ) (γ : ℚ) (hΔ : 0 < Δ) (hγ : 0 < γ)
    (he : 0 < e) (hcount : 2*e ≤ Δ*v)
    (hfirst : L = exactPublicLog v e Δ γ)
    (hloopless : ∀ z, G z false ≠ G z true)
    (hincident : ∀ z, ∃ a b, G a b = z)
    (hdegree : ∀ z, Paper2.SourceItems.degree G z ≤ Δ)
    (hgap : ∀ colour : Fin v → Fin 3,
      (γ : ℝ) * e ≤
      ((Finset.univ.filter (fun z =>
        colour (G z false) = colour (G z true))).card : ℝ)) :
    NoContract (actualConstruction v e L T inputs) G
      (Paper2.LookupSeed.exponent L + 1) (h L) := by
  have hadm := (first_literal_production_schedule L v e Δ γ hΔ hγ
    he hcount hfirst).2.1
  exact actual_no_contract v e L T inputs G Δ γ hΔ hγ
    hloopless hincident hdegree hgap hadm

end Generated

#print axioms first_literal_production_schedule
#print axioms first_literal_actual_full_W_at
#print axioms first_literal_actual_no_contract

end FiniteV35Continuation
