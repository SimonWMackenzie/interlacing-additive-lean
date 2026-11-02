import CurrentAdditive.CodeDArrayPositionDecode
import CurrentAdditive.IndexedExecutableStep

/-! The final Code D call in the literal successor has row labels equal to
the positions of its own materialized array. -/

namespace CurrentAdditive.IndexedExecutableStepRecovery

open Paper2
open CurrentAdditive.DeterministicParameters
open CurrentAdditive.DeterministicIndexedMatrix
open CurrentAdditive.IndexedStagePresentation
open CurrentAdditive.IndexedExecutableStep

variable {V E : Type} [Fintype V] [Fintype E] [DecidableEq V]
  (L : ℕ) [Nonempty V] [Nonempty (Fin (4*s L))]
  [Nonempty (Fin (s L-3))]
  [NeZero (q₁ L)] [NeZero (q₂ L)] [NeZero (s L)]
  [NeZero (w L)] [NeZero (Q L)]

noncomputable def finalStreamArrayNumbering
    (R : Stage (N L))
    (src : Sources (D := 8192) (q₁ := q₁ L) (q₂ := q₂ L)
      (s := s L) R.rowLaw R.colLaw)
    (tables : GeneratedTables (V := V) L R src) :
    Fin (CurrentAdditive.IndexedExecutableStep.codeDArray
      8192 (Q L)
      ((PositiveRationalLaw.uniform (Fin (w L))).prod
        (Sources.columnLaw src)) tables.final).size ≃
      (finalStream (V := V) L R src tables).Label :=
  codeDArrayPosition 8192 (Q L) _ tables.final

#print axioms finalStreamArrayNumbering

end CurrentAdditive.IndexedExecutableStepRecovery
