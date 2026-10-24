import CurrentAdditive.ActualNumberedSuccessorTable
/-! Reindexing the actual generated successor to executable array positions
preserves its full restriction profile as well as deterministic cost. -/

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

noncomputable def actualNumberedRowLaw
    (R : Stage (N L))
    (src : Sources (D := 8192) (q₁ := q₁ L) (q₂ := q₂ L)
      (s := s L) R.rowLaw R.colLaw)
    (tables : GeneratedTables (V := V) L R src) :=
  numberedLaw (finalStream (V := V) L R src tables).law
    (finalStreamArrayNumbering (V := V) L R src tables)

noncomputable def actualNumberedColumnLaw
    (R : Stage (N L))
    (src : Sources (D := 8192) (q₁ := q₁ L) (q₂ := q₂ L)
      (s := s L) R.rowLaw R.colLaw)
    (baseRow : AlphabetTable R.Row R.rowLaw)
    (tables : GeneratedTables (V := V) L R src) :=
  numberedLaw
    ((PositiveRationalLaw.uniform (Fin (Q L))).prod
      (Sources.InternalStreams.law src
        (internalStreams (V := V) L R src baseRow tables)))
    (internalStreamColumnNumbering (V := V) L R src baseRow tables)

theorem actualNumberedSuccessor_profile_iff
    (R : Stage (N L))
    (src : Sources (D := 8192) (q₁ := q₁ L) (q₂ := q₂ L)
      (s := s L) R.rowLaw R.colLaw)
    (baseRow : AlphabetTable R.Row R.rowLaw)
    (tables : GeneratedTables (V := V) L R src)
    (activity : Paper2.SourceConstruction.Items (s L) V →
      Fin (q₂ L) → Option (Fin (s L)))
    (tail : Paper2.SourceMatrix.Tail (s L) R.Col)
    (ρ : ℝ) (d : ℤ) :
    RestrictionProfile
      (actualNumberedSuccessor (V := V) L R src baseRow tables activity tail)
      (actualNumberedRowLaw (V := V) L R src tables).toFiniteLaw
      (actualNumberedColumnLaw (V := V) L R src baseRow tables).toFiniteLaw
      ρ d ↔
    RestrictionProfile
      (Sources.successor src
        (internalStreams (V := V) L R src baseRow tables)
        (finalStream (V := V) L R src tables)
        R.matrix activity tail)
      (finalStream (V := V) L R src tables).law.toFiniteLaw
      (((PositiveRationalLaw.uniform (Fin (Q L))).prod
        (Sources.InternalStreams.law src
          (internalStreams (V := V) L R src baseRow tables))).toFiniteLaw)
      ρ d := by
  exact restrictionProfile_pullback_iff _ _ _ _ _
    (finalStreamArrayNumbering (V := V) L R src tables)
    (internalStreamColumnNumbering (V := V) L R src baseRow tables)
    (numberedLaw_pushesTo _
      (finalStreamArrayNumbering (V := V) L R src tables))
    (numberedLaw_pushesTo _
      (internalStreamColumnNumbering (V := V) L R src baseRow tables))
    (finalStreamArrayNumbering (V := V) L R src tables).surjective
    (internalStreamColumnNumbering (V := V) L R src baseRow tables).surjective
    ρ d

#print axioms actualNumberedSuccessor_profile_iff

end CurrentAdditive.IndexedExecutableStepRecovery
