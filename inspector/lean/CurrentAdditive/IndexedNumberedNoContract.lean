import CurrentAdditive.IndexedActualNoContract
import CurrentAdditive.IndexedActualConstruction

/-! The exact same full-W step proof, now started from the explicit indexed
lookup seed whose row order is the one printed by the physical seed machine. -/

namespace CurrentAdditive.IndexedExecutableStepRecovery

open Paper2 Paper2.SourceMatrix Workspace.Types.CommComplexity
open CurrentAdditive.DeterministicParameters
open CurrentAdditive.DeterministicAdmissibility
open CurrentAdditive.DeterministicIndexedMatrix
open CurrentAdditive.IndexedStagePresentation
open CurrentAdditive.IndexedSemanticIteration
open CurrentAdditive.DeterministicIteration

variable (v e L : ℕ) [NeZero v] [NeZero (s L)] [NeZero (s L-3)]
  [NeZero (q₁ L)] [NeZero (q₂ L)] [NeZero (w L)] [NeZero (Q L)]

/-- The actual indexed-seed construction has the exact NO recurrence on its
literal successor, with no cost or profile assertion built into `StepInputs`. -/
theorem indexed_actual_no_contract
    (T : Schedule (Fin v) (Fin e) L)
    (inputs : ∀ R : Stage (N L), StepInputs (V := Fin v) (E := Fin e) L R T)
    (G : IndexedSemanticIteration.Graph (Fin v) (Fin e))
    (Δ : ℕ) (γ : ℚ) (hΔ : 0 < Δ) (hγ : 0 < γ)
    (hloopless : ∀ z, G z false ≠ G z true)
    (hincident : ∀ z, ∃ a b, G a b = z)
    (hdegree : ∀ z, Paper2.SourceItems.degree G z ≤ Δ)
    (hgap : ∀ colour : Fin v → Fin 3,
      (γ : ℝ) * e ≤
      ((Finset.univ.filter (fun z =>
        colour (G z false) = colour (G z true))).card : ℝ))
    (hadm : Admissible L Δ v e sourceC128Ceil γ) :
    NoContract (indexedActualConstruction v e L T inputs) G
      (Paper2.LookupSeed.exponent L + 1) (h L) := by
  refine {
    seed_exact := indexedActual_seed_cost v e L T inputs G
    seed_profile := indexedActual_seed_profile v e L T inputs G
    seed_cost_ge := actual_seed_cost_ge_three L
    step_exact_profile := ?_
  }
  intro R _ hcost hp
  have hRprofile : RestrictionProfile R.matrix R.rowLaw.toFiniteLaw
      R.colLaw.toFiniteLaw (ρ L : ℝ) (D R.matrix : ℤ) := by
    simpa only [indexedActualConstruction,
      IndexedSemanticIteration.construction] using hp
  obtain ⟨hWcost, hWnear⟩ :=
    actual_full_W_at v e L T inputs G Δ γ hΔ hγ hloopless
      hincident hdegree hgap hadm R hcost hRprofile
  have hadm' : Admissible L Δ (Fintype.card (Fin v))
      (Fintype.card (Fin e)) sourceC128Ceil γ := by
    simpa only [Fintype.card_fin] using hadm
  have hr := next_restored_from_full_W L T inputs G R Δ sourceC128Ceil γ
    hΔ hγ hadm' (D R.matrix) hcost rfl hRprofile
    (by simpa only [FullWAt] using hWcost)
    (by simpa only [FullWAt] using hWnear)
  constructor
  · simpa only [indexedActualConstruction,
      IndexedSemanticIteration.construction] using hr.1
  · have hcost' := hr.1
    rw [← hcost'] at hr
    simpa only [indexedActualConstruction,
      IndexedSemanticIteration.construction] using hr.2

#print axioms indexed_actual_no_contract

end CurrentAdditive.IndexedExecutableStepRecovery
