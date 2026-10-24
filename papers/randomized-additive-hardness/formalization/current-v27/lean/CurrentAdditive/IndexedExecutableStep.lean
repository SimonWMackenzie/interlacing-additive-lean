import CurrentAdditive.IndexedSemanticIterationProd
import CurrentAdditive.SourcesFromBaseTables

/-!
An explicit Code_D preparation of the literal indexed successor.  The
predecessor's two positive rational law tables make the nested gamma, inner,
and outer sources through `sourcesFromBaseTables`.  Three more complete
streams and the final stream are built by `fromTable`.  The remaining
alphabet tables and physical clock must be delivered by the producer; no
source is selected by an existential choice and no successor cost/profile
is stored here.
-/

namespace CurrentAdditive.IndexedExecutableStep

open Paper2
open Paper2.SourceMatrix
open CurrentAdditive.DeterministicParameters
open CurrentAdditive.DeterministicIndexedMatrix
open CurrentAdditive.IndexedStagePresentation
open CurrentAdditive.IndexedSemanticIteration
open CurrentAdditive.ExecutableCodeSource

variable {V E : Type} [Fintype V] [Fintype E] [DecidableEq V]
  (L : ℕ) [Nonempty V] [Nonempty (Fin (4*s L))]
  [Nonempty (Fin (s L-3))]
  [NeZero (q₁ L)] [NeZero (q₂ L)] [NeZero (s L)]
  [NeZero (w L)] [NeZero (Q L)]

/-- The remaining three alphabets are indexed by the *generated* nested
source labels.  Their tables retain every row, including repeated decoded
words, with the original rational point masses. -/
structure GeneratedTables (R : Stage (N L))
    (src : Sources (D := 8192) (q₁ := q₁ L) (q₂ := q₂ L)
      (s := s L) R.rowLaw R.colLaw) where
  metadata : AlphabetTable
    (Fin (s L) ⊕ Paper2.SourceConstruction.Items (s L) V)
    (metadataLaw (actualItemLaw (V := V) L))
  selector : AlphabetTable src.inner.Label src.inner.law
  final : AlphabetTable (Fin (w L) × Sources.Column src)
    ((PositiveRationalLaw.uniform (Fin (w L))).prod
      (Sources.columnLaw src))

/-- These are three independent complete indexed streams, not a source
conditioned on a previously sampled metadata label. -/
noncomputable def internalStreams
    (R : Stage (N L))
    (src : Sources (D := 8192) (q₁ := q₁ L) (q₂ := q₂ L)
      (s := s L) R.rowLaw R.colLaw)
    (baseRow : AlphabetTable R.Row R.rowLaw)
    (tables : GeneratedTables (V := V) L R src) :
    Sources.InternalStreams src (actualItemLaw (V := V) L) (w L) :=
  {
    metadataStream := fromTable 8192 (w L) _ tables.metadata
    baseStream := fromTable 8192 (w L) _ baseRow
    selectorStream := fromTable 8192 (w L) _ tables.selector
  }

/-- The final call uses the original product law of the W-column alphabet,
with its complete index list. -/
noncomputable def finalStream
    (R : Stage (N L))
    (src : Sources (D := 8192) (q₁ := q₁ L) (q₂ := q₂ L)
      (s := s L) R.rowLaw R.colLaw)
    (tables : GeneratedTables (V := V) L R src) :
    CodeSource 8192 (Q L) (Fin (w L) × Sources.Column src)
      ((PositiveRationalLaw.uniform (Fin (w L))).prod
        (Sources.columnLaw src)) :=
  fromTable 8192 (Q L) _ tables.final

/-- The complete source-call data for one predecessor, assembled from its
explicit input-law tables and all generated Code_D alphabet tables.  The
Boolean rectangle is charged exactly, with `otherBytes` reserved for index,
law, and source encodings; `producerClock` must be justified by a machine
proof. -/
noncomputable def stepInputsFromTables
    (R : Stage (N L)) (T : Schedule V E L)
    (baseRow : AlphabetTable R.Row R.rowLaw)
    (baseCol : AlphabetTable R.Col R.colLaw)
    (tables : GeneratedTables (V := V) L R
      (sourcesFromBaseTables 8192 (q₁ L) (q₂ L) (s L)
        R.rowLaw R.colLaw baseRow baseCol))
    (tail : Tail (s L) R.Col)
    (otherBytes producerClock : ℕ) : StepInputs (V := V) (E := E) L R T := by
  let src := sourcesFromBaseTables 8192 (q₁ L) (q₂ L) (s L)
    R.rowLaw R.colLaw baseRow baseCol
  let streams := internalStreams (V := V) L R src baseRow tables
  let final := finalStream (V := V) L R src tables
  exact {
    src := src
    streams := streams
    final := final
    tail := tail
    encodingSize := Fintype.card final.Label *
      Fintype.card (Fin (Q L) ×
        (streams.metadataStream.Label ×
          (streams.baseStream.Label × streams.selectorStream.Label))) +
      otherBytes
    stepClock := producerClock
    entries_le_size := by omega
  }

/-- The actual deterministic producer has to supply the predecessor's two
weighted alphabets and the three dependent generated alphabets at every
iterated stage.  Its output clock is attached to that same input stage. -/
structure TableProvider (T : Schedule V E L) where
  baseRow : (R : Stage (N L)) → AlphabetTable R.Row R.rowLaw
  baseCol : (R : Stage (N L)) → AlphabetTable R.Col R.colLaw
  generated : (R : Stage (N L)) → GeneratedTables (V := V) L R
    (sourcesFromBaseTables 8192 (q₁ L) (q₂ L) (s L)
      R.rowLaw R.colLaw (baseRow R) (baseCol R))
  tail : (R : Stage (N L)) → Tail (s L) R.Col
  otherBytes : Stage (N L) → ℕ
  producerClock : Stage (N L) → ℕ

/-- One fixed graph-independent family of literal Code_D source calls,
ready to be consumed by the one semantic successor function. -/
noncomputable def preparedInputs (T : Schedule V E L)
    (P : TableProvider (V := V) (E := E) L T) :
    ∀ R : Stage (N L), StepInputs (V := V) (E := E) L R T :=
  fun R => stepInputsFromTables (V := V) (E := E) L R T
    (P.baseRow R) (P.baseCol R) (P.generated R)
    (P.tail R) (P.otherBytes R) (P.producerClock R)

#print axioms internalStreams
#print axioms finalStream
#print axioms stepInputsFromTables
#print axioms preparedInputs

end CurrentAdditive.IndexedExecutableStep
