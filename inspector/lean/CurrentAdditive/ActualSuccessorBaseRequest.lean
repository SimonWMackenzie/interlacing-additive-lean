import CurrentAdditive.ActualNumberedSuccessorProfile
/-! Each numeric successor entry reduces to one precise request to the
predecessor matrix.  This is the target relation for a future physical
entry evaluator; it does not itself execute the request. -/

namespace CurrentAdditive.IndexedExecutableStepRecovery

open Paper2
open CurrentAdditive.DeterministicParameters
open CurrentAdditive.DeterministicIndexedMatrix
open CurrentAdditive.IndexedStagePresentation
open CurrentAdditive.IndexedSemanticIteration
open CurrentAdditive.IndexedExecutableStep
open CurrentAdditive.ExecutableCodeSource

variable {V E : Type} [Fintype V] [Fintype E] [DecidableEq V]
  (L : ℕ) [Nonempty V] [Nonempty (Fin (4*s L))]
  [Nonempty (Fin (s L-3))]
  [NeZero (q₁ L)] [NeZero (q₂ L)] [NeZero (s L)]
  [NeZero (w L)] [NeZero (Q L)]

noncomputable def actualSuccessorBaseRequest
    (R : Stage (N L))
    (src : Sources (D := 8192) (q₁ := q₁ L) (q₂ := q₂ L)
      (s := s L) R.rowLaw R.colLaw)
    (baseRow : AlphabetTable R.Row R.rowLaw)
    (tables : GeneratedTables (V := V) L R src)
    (activity : Paper2.SourceConstruction.Items (s L) V →
      Fin (q₂ L) → Option (Fin (s L)))
    (tail : Paper2.SourceMatrix.Tail (s L) R.Col)
    (i : _root_.Fin (codeDArray 8192 (Q L)
      ((PositiveRationalLaw.uniform (Fin (w L))).prod
        (Sources.columnLaw src)) tables.final).size)
    (j : _root_.Fin ((Q L) *
      ((codeDArray 8192 (w L)
          (metadataLaw (actualItemLaw (V := V) L)) tables.metadata).size *
       ((codeDArray 8192 (w L) R.rowLaw baseRow).size *
        (codeDArray 8192 (w L) src.inner.law tables.selector).size)))) :
    R.Row × R.Col :=
  let streams := internalStreams (V := V) L R src baseRow tables
  let final := finalStream (V := V) L R src tables
  let col := internalStreamColumnNumbering (V := V) L R src baseRow tables j
  let pc := final.decode (finalStreamArrayNumbering (V := V) L R src tables i) col.1
  Paper2.SourceMatrix.baseRequest activity
    (Sources.decodeRow src (Sources.InternalStreams.decode src streams col.2 pc.1))
    (Sources.decodeColumn src tail pc.2)

theorem actualNumberedSuccessor_one_predecessor_entry
    (R : Stage (N L))
    (src : Sources (D := 8192) (q₁ := q₁ L) (q₂ := q₂ L)
      (s := s L) R.rowLaw R.colLaw)
    (baseRow : AlphabetTable R.Row R.rowLaw)
    (tables : GeneratedTables (V := V) L R src)
    (activity : Paper2.SourceConstruction.Items (s L) V →
      Fin (q₂ L) → Option (Fin (s L)))
    (tail : Paper2.SourceMatrix.Tail (s L) R.Col)
    (i : _root_.Fin (codeDArray 8192 (Q L)
      ((PositiveRationalLaw.uniform (Fin (w L))).prod
        (Sources.columnLaw src)) tables.final).size)
    (j : _root_.Fin ((Q L) *
      ((codeDArray 8192 (w L)
          (metadataLaw (actualItemLaw (V := V) L)) tables.metadata).size *
       ((codeDArray 8192 (w L) R.rowLaw baseRow).size *
        (codeDArray 8192 (w L) src.inner.law tables.selector).size)))) :
    actualNumberedSuccessor (V := V) L R src baseRow tables activity tail i j =
      R.matrix (actualSuccessorBaseRequest (V := V) L R src baseRow tables
        activity tail i j).1
        (actualSuccessorBaseRequest (V := V) L R src baseRow tables
          activity tail i j).2 := by
  rfl

#print axioms actualNumberedSuccessor_one_predecessor_entry

end CurrentAdditive.IndexedExecutableStepRecovery
