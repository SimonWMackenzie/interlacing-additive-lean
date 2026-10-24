import CurrentAdditive.DeterministicETHConcreteIterationProd
import CurrentAdditive.ExplicitStageNumbering

/-! The physical table presentation uses an explicitly supplied row and
column numbering at every generated stage. It is the same indexed successor
object as the earlier semantic endpoint, with only its serialized order
changed. Cost and row/column counts are transferred exactly. -/

namespace CurrentAdditive.DeterministicETHNumberedPresentation

open CurrentAdditive.IndexedStagePresentation
open CurrentAdditive.IndexedSemanticIteration
open CurrentAdditive.IndexedExecutableStepRecovery
open CurrentAdditive.DeterministicETHConcreteIteration
open CurrentAdditive.DeterministicEndpointAssembly
open CurrentAdditive.DeterministicParameters

variable (v e L : ℕ)
  [NeZero v] [NeZero (s L)] [NeZero (s L-3)] [NeZero (q₁ L)]
  [NeZero (q₂ L)] [NeZero (w L)] [NeZero (Q L)]

noncomputable def numberedActualTables
    (T : Schedule (Fin v) (Fin e) L)
    (inputs : ∀ R : Stage (N L),
      StepInputs (V := Fin v) (E := Fin e) L R T)
    (numberings : ∀ R : Stage (N L), ExplicitNumberings R) :
    TablePresentation (actualConstruction v e L T inputs) (N L) :=
  {
    rows := IndexedStagePresentation.rows
    cols := IndexedStagePresentation.cols
    table := fun R => numberedTable R (numberings R)
    rows_pos := IndexedStagePresentation.rows_pos
    cols_pos := IndexedStagePresentation.cols_pos
    exact_cost := fun R => numberedTable_cost R (numberings R)
    entries_le_encoding := Stage.entries_le_encoding
    public_side := Stage.public_side
  }

#print axioms numberedActualTables

end CurrentAdditive.DeterministicETHNumberedPresentation
