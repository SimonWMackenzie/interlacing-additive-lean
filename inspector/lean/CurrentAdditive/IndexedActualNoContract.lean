import CurrentAdditive.GeneratedWAlignmentActualStage
import CurrentAdditive.IndexedNoContractProd

/-! The checked full-W theorem supplies the only mathematical input to the
literal indexed NO induction.  The graph and schedule promises remain explicit
until this result is specialized to the source graph. -/

namespace CurrentAdditive.IndexedSemanticIteration

open Paper2 Paper2.SourceMatrix Workspace.Types.CommComplexity
open CurrentAdditive.DeterministicParameters
open CurrentAdditive.DeterministicAdmissibility
open CurrentAdditive.DeterministicIndexedMatrix
open CurrentAdditive.DeterministicIndexedMatrix.Sources
open CurrentAdditive.IndexedStagePresentation
open CurrentAdditive.DeterministicIteration
open CurrentAdditive.DeterministicETHConcreteIteration

variable (v e L : ℕ) [NeZero v] [NeZero (s L)] [NeZero (s L-3)]
  [NeZero (q₁ L)] [NeZero (q₂ L)] [NeZero (w L)] [NeZero (Q L)]

omit [NeZero (Q L)] in
/-- The full-W theorem at every profiled predecessor is exactly the
`FullWAt` assertion required by the existing successor restoration. -/
theorem actual_full_W_at
    (T : Schedule (Fin v) (Fin e) L)
    (inputs : ∀ R : Stage (N L), StepInputs (V := Fin v) (E := Fin e) L R T)
    (G : Graph (Fin v) (Fin e))
    (Δ : ℕ) (γ : ℚ) (hΔ : 0 < Δ) (hγ : 0 < γ)
    (hloopless : ∀ z, G z false ≠ G z true)
    (hincident : ∀ z, ∃ a b, G a b = z)
    (hdegree : ∀ z, Paper2.SourceItems.degree G z ≤ Δ)
    (hgap : ∀ colour : Fin v → Fin 3,
      (γ : ℝ) * e ≤
      ((Finset.univ.filter (fun z =>
        colour (G z false) = colour (G z true))).card : ℝ))
    (hadm : Admissible L Δ v e sourceC128Ceil γ)
    (R : Stage (N L)) (hcost : 3 ≤ D R.matrix)
    (hp : RestrictionProfile R.matrix R.rowLaw.toFiniteLaw
      R.colLaw.toFiniteLaw (ρ L : ℝ) (D R.matrix : ℤ)) :
    FullWAt v e L T inputs G Δ γ R := by
  have hadm' : Admissible L Δ (Fintype.card (Fin v))
      (Fintype.card (Fin e)) sourceC128Ceil γ := by
    simpa only [Fintype.card_fin] using hadm
  have hW := actual_stage_W_full L T R (inputs R) G Δ γ hΔ hγ
    hloopless hincident hdegree
    (by simpa only [Fintype.card_fin] using hgap)
    (D R.matrix) hcost rfl hp hadm'
  dsimp [FullWAt]
  refine ⟨hW.1, ?_⟩
  intro A B hA hB
  exact hW.2 B A (by simpa only [indexedFirstRowLaw] using hB) hA

/-- The actual lookup-seeded construction satisfies its NO induction from
the source graph promise and the checked full-W assertion. -/
theorem actual_no_contract
    (T : Schedule (Fin v) (Fin e) L)
    (inputs : ∀ R : Stage (N L), StepInputs (V := Fin v) (E := Fin e) L R T)
    (G : Graph (Fin v) (Fin e))
    (Δ : ℕ) (γ : ℚ) (hΔ : 0 < Δ) (hγ : 0 < γ)
    (hloopless : ∀ z, G z false ≠ G z true)
    (hincident : ∀ z, ∃ a b, G a b = z)
    (hdegree : ∀ z, Paper2.SourceItems.degree G z ≤ Δ)
    (hgap : ∀ colour : Fin v → Fin 3,
      (γ : ℝ) * e ≤
      ((Finset.univ.filter (fun z =>
        colour (G z false) = colour (G z true))).card : ℝ))
    (hadm : Admissible L Δ v e sourceC128Ceil γ) :
    NoContract (actualConstruction v e L T inputs) G
      (Paper2.LookupSeed.exponent L + 1) (h L) := by
  exact actual_no_of_full_W v e L T inputs G Δ sourceC128Ceil γ
    hΔ hγ hadm
    (fun R hcost hp => actual_full_W_at v e L T inputs G Δ γ
      hΔ hγ hloopless hincident hdegree hgap hadm R hcost hp)

#print axioms actual_full_W_at
#print axioms actual_no_contract

end CurrentAdditive.IndexedSemanticIteration
