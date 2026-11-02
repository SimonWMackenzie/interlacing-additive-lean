import CurrentAdditive.ActualFinalStreamRowNumbering

/-! The literal successor's internal column stream has the arithmetic
product order of its three materialized Code D arrays. -/

namespace CurrentAdditive.IndexedExecutableStepRecovery

open Paper2
open CurrentAdditive.DeterministicParameters
open CurrentAdditive.DeterministicIndexedMatrix
open CurrentAdditive.IndexedStagePresentation
open CurrentAdditive.IndexedExecutableStep
open CurrentAdditive.IndexedSemanticIteration
open CurrentAdditive.ExecutableCodeSource

variable {V E : Type} [Fintype V] [Fintype E] [DecidableEq V]
  (L : ℕ) [Nonempty V] [Nonempty (Fin (4*s L))]
  [Nonempty (Fin (s L-3))]
  [NeZero (q₁ L)] [NeZero (q₂ L)] [NeZero (s L)]
  [NeZero (w L)] [NeZero (Q L)]

noncomputable def internalStreamColumnNumbering
    (R : Stage (N L))
    (src : Sources (D := 8192) (q₁ := q₁ L) (q₂ := q₂ L)
      (s := s L) R.rowLaw R.colLaw)
    (baseRow : AlphabetTable R.Row R.rowLaw)
    (tables : GeneratedTables (V := V) L R src) :
    Fin ((Q L) *
      ((codeDArray 8192 (w L)
          (metadataLaw (actualItemLaw (V := V) L)) tables.metadata).size *
       ((codeDArray 8192 (w L) R.rowLaw baseRow).size *
        (codeDArray 8192 (w L) src.inner.law tables.selector).size))) ≃
      Fin (Q L) ×
        ((internalStreams (V := V) L R src baseRow tables).metadataStream.Label ×
         ((internalStreams (V := V) L R src baseRow tables).baseStream.Label ×
          (internalStreams (V := V) L R src baseRow tables).selectorStream.Label)) :=
  codeDSuccessorColumnNumbering (Q L)
    8192 (w L) 8192 (w L) 8192 (w L)
    (metadataLaw (actualItemLaw (V := V) L)) tables.metadata
    R.rowLaw baseRow src.inner.law tables.selector

#print axioms internalStreamColumnNumbering

end CurrentAdditive.IndexedExecutableStepRecovery
