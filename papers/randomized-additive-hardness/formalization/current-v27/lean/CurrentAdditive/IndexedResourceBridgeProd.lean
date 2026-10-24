import CurrentAdditive.DeterministicETHConcreteIterationProd

/-!
The physical producer interface for the *same* indexed construction used by
the seed, universal, YES, NO, and table bridges.  The numerical hypotheses
below concern the complete encoded output and actual producer clock of each
literal source call.  Establishing them from executable Code_D is separate.
-/

namespace CurrentAdditive.IndexedSemanticIteration

open CurrentAdditive.DeterministicParameters
open CurrentAdditive.IndexedStagePresentation
open CurrentAdditive.DeterministicIteration
open CurrentAdditive.DeterministicETHConcreteIteration
open CurrentAdditive.DeterministicETHSeedStage

variable (v e L : ℕ) [NeZero v] [NeZero (s L)] [NeZero (s L-3)]
  [NeZero (q₁ L)] [NeZero (q₂ L)] [NeZero (w L)] [NeZero (Q L)]

/-- One-step size and clock are precisely the fields of the source-call
producer selected at the *input* stage. -/
theorem actual_next_size_clock
    (T : Schedule (Fin v) (Fin e) L)
    (inputs : ∀ R : Stage (N L), StepInputs (V := Fin v) (E := Fin e) L R T)
    (G : Graph (Fin v) (Fin e)) (R : Stage (N L)) :
    (next L T inputs G R).encodingSize = (inputs R).encodingSize ∧
    (actualConstruction v e L T inputs).stepTime R =
      (inputs R).stepClock := by
  constructor <;> rfl

/-- Numerical full-encoding and physical-clock bounds imply the generic
resource contract for the one literal construction.  The hypotheses contain
no communication-cost or restriction-profile assertion. -/
theorem actual_resources_of_encoded_bounds
    (T : Schedule (Fin v) (Fin e) L)
    (inputs : ∀ R : Stage (N L), StepInputs (V := Fin v) (E := Fin e) L R T)
    (G : Graph (Fin v) (Fin e)) (A C₁ : ℕ)
    (hbase : N L + (seedStage L).encodingSize + 2 ≤ (N L) ^ C₁)
    (houtput : ∀ R : Stage (N L),
      N L + (inputs R).encodingSize + 2 ≤
        (N L + R.encodingSize + 2) ^ A)
    (hclock : ∀ R : Stage (N L),
      (inputs R).stepClock ≤
        (N L + R.encodingSize + 2) ^ A) :
    ResourceContract (actualConstruction v e L T inputs) G
      (N L) A C₁ := by
  refine ⟨?_, ?_, ?_⟩
  · simpa only [envelope, actualConstruction,
      CurrentAdditive.DeterministicETHConcreteIteration.actualConstruction,
      construction] using hbase
  · intro R _
    simpa only [envelope, actualConstruction,
      CurrentAdditive.DeterministicETHConcreteIteration.actualConstruction,
      construction, (actual_next_size_clock v e L T inputs G R).1]
      using houtput R
  · intro R _
    simpa only [envelope, actualConstruction,
      CurrentAdditive.DeterministicETHConcreteIteration.actualConstruction,
      construction, (actual_next_size_clock v e L T inputs G R).2]
      using hclock R

#print axioms actual_next_size_clock
#print axioms actual_resources_of_encoded_bounds

end CurrentAdditive.IndexedSemanticIteration
