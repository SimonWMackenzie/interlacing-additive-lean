import CurrentAdditive.ExplicitRectangleTarget
import CurrentAdditive.DeterministicETHConcreteIterationProd
import CurrentAdditive.DeterministicETHPhysicalSquare

/-! A separate endpoint presentation of the same literal indexed iteration.
The matrix and rational laws are unchanged; the chosen finite orders specify
the Boolean word that a physical producer must print. -/

namespace CurrentAdditive.IndexedExecutableStepRecovery

open CurrentAdditive.DeterministicParameters
open CurrentAdditive.IndexedStagePresentation
open CurrentAdditive.IndexedSemanticIteration
open CurrentAdditive.DeterministicETHConcreteIteration
open CurrentAdditive.DeterministicIteration

variable (v e L : ℕ) [NeZero v] [NeZero (s L)] [NeZero (s L-3)]
  [NeZero (q₁ L)] [NeZero (q₂ L)] [NeZero (w L)] [NeZero (Q L)]

noncomputable def actualNumberedTables
    (T : Schedule (Fin v) (Fin e) L)
    (inputs : ∀ R : Stage (N L), StepInputs (V := Fin v) (E := Fin e) L R T)
    (numberings : ∀ R : Stage (N L), ExplicitNumberings R) :
    CurrentAdditive.DeterministicEndpointAssembly.TablePresentation
      (actualConstruction v e L T inputs) (N L) where
  rows := rows
  cols := cols
  table := fun R => numberedTable R (numberings R)
  rows_pos := rows_pos
  cols_pos := cols_pos
  exact_cost := fun R => numberedTable_cost R (numberings R)
  entries_le_encoding := Stage.entries_le_encoding
  public_side := Stage.public_side

theorem actualNumberedTables_table
    (T : Schedule (Fin v) (Fin e) L)
    (inputs : ∀ R : Stage (N L), StepInputs (V := Fin v) (E := Fin e) L R T)
    (numberings : ∀ R : Stage (N L), ExplicitNumberings R)
    (R : Stage (N L)) :
    (actualNumberedTables v e L T inputs numberings).table R =
      numberedTable R (numberings R) := rfl

theorem successorRectangle_matches_numbered_endpoint
    (T : Schedule (Fin v) (Fin e) L)
    (inputs : ∀ R : Stage (N L), StepInputs (V := Fin v) (E := Fin e) L R T)
    (numberings : ∀ R : Stage (N L), ExplicitNumberings R)
    (G : IndexedSemanticIteration.Graph (Fin v) (Fin e))
    (k b : ℕ) :
    numberedRectangle
      (next L T inputs G (state (actualConstruction v e L T inputs) G k))
      (numberings (next L T inputs G
        (state (actualConstruction v e L T inputs) G k))) b =
    CurrentAdditive.DeterministicETHPhysicalSquare.rectangleInstance
      ((actualNumberedTables v e L T inputs numberings).table
        (state (actualConstruction v e L T inputs) G (k+1))) b := by
  rfl

#print axioms actualNumberedTables
#print axioms successorRectangle_matches_numbered_endpoint

end CurrentAdditive.IndexedExecutableStepRecovery
