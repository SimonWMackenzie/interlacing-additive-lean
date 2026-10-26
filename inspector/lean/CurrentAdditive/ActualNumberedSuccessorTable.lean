import CurrentAdditive.ActualInternalColumnNumbering
import CurrentAdditive.ExplicitStageNumbering
/-! The literal `Sources.successor` matrix, presented in the array-position
row order and nested-product column order of the actual source calls. -/

namespace CurrentAdditive.IndexedExecutableStepRecovery

open Paper2
open CurrentAdditive.DeterministicParameters
open CurrentAdditive.DeterministicIndexedMatrix
open CurrentAdditive.IndexedStagePresentation
open CurrentAdditive.IndexedSemanticIteration
open CurrentAdditive.IndexedExecutableStep
open CurrentAdditive.ExecutableCodeSource
open Workspace.Types.CommComplexity

variable {V E : Type} [Fintype V] [Fintype E] [DecidableEq V]
  (L : ℕ) [Nonempty V] [Nonempty (Fin (4*s L))]
  [Nonempty (Fin (s L-3))]
  [NeZero (q₁ L)] [NeZero (q₂ L)] [NeZero (s L)]
  [NeZero (w L)] [NeZero (Q L)]

noncomputable def actualNumberedSuccessor
    (R : Stage (N L))
    (src : Sources (D := 8192) (q₁ := q₁ L) (q₂ := q₂ L)
      (s := s L) R.rowLaw R.colLaw)
    (baseRow : AlphabetTable R.Row R.rowLaw)
    (tables : GeneratedTables (V := V) L R src)
    (activity : Paper2.SourceConstruction.Items (s L) V →
      Fin (q₂ L) → Option (Fin (s L)))
    (tail : Paper2.SourceMatrix.Tail (s L) R.Col) :=
  fun i j => Sources.successor src
    (internalStreams (V := V) L R src baseRow tables)
    (finalStream (V := V) L R src tables)
    R.matrix activity tail
    (finalStreamArrayNumbering (V := V) L R src tables i)
    (internalStreamColumnNumbering (V := V) L R src baseRow tables j)

theorem actualNumberedSuccessor_cost
    (R : Stage (N L))
    (src : Sources (D := 8192) (q₁ := q₁ L) (q₂ := q₂ L)
      (s := s L) R.rowLaw R.colLaw)
    (baseRow : AlphabetTable R.Row R.rowLaw)
    (tables : GeneratedTables (V := V) L R src)
    (activity : Paper2.SourceConstruction.Items (s L) V →
      Fin (q₂ L) → Option (Fin (s L)))
    (tail : Paper2.SourceMatrix.Tail (s L) R.Col) :
    D (actualNumberedSuccessor (V := V) L R src baseRow tables activity tail) =
      D (Sources.successor src
        (internalStreams (V := V) L R src baseRow tables)
        (finalStream (V := V) L R src tables)
        R.matrix activity tail) := by
  exact NPCC.D_equiv_invariance _
    (finalStreamArrayNumbering (V := V) L R src tables)
    (internalStreamColumnNumbering (V := V) L R src baseRow tables)

#print axioms actualNumberedSuccessor
#print axioms actualNumberedSuccessor_cost

end CurrentAdditive.IndexedExecutableStepRecovery
