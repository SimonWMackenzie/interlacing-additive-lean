import CurrentAdditive.ExplicitSuccessorProductIndex

/-! Each of the three column-stream labels is the position of an actual
materialized Code D array.  Their nested product has a fixed arithmetic
decoder; repeated decoded words retain distinct positions. -/

namespace CurrentAdditive.IndexedExecutableStepRecovery

open Paper2
open CurrentAdditive.ExecutableCodeSource
open CurrentAdditive.IndexedExecutableStep

variable {Y : Type} [Fintype Y] [DecidableEq Y]

noncomputable def codeDArrayPosition (D q : ℕ)
    (μ : PositiveRationalLaw Y) (table : AlphabetTable Y μ) :
    Fin (codeDArray D q μ table).size ≃
      (fromTable D q μ table).Label :=
  (finCongr (codeD_label_card D q μ table).symm).trans
    (codeD_label_fin D q μ table)

variable {A B C : Type} [Fintype A] [DecidableEq A]
  [Fintype B] [DecidableEq B] [Fintype C] [DecidableEq C]

noncomputable def codeDSuccessorColumnNumbering
    (Q DA qA DB qB DC qC : ℕ)
    (μA : PositiveRationalLaw A) (tA : AlphabetTable A μA)
    (μB : PositiveRationalLaw B) (tB : AlphabetTable B μB)
    (μC : PositiveRationalLaw C) (tC : AlphabetTable C μC) :
    Fin (Q * ((codeDArray DA qA μA tA).size *
      ((codeDArray DB qB μB tB).size *
        (codeDArray DC qC μC tC).size))) ≃
      Fin Q × ((fromTable DA qA μA tA).Label ×
        ((fromTable DB qB μB tB).Label ×
          (fromTable DC qC μC tC).Label)) :=
  successorColumnNumbering Q _ _ _
    (codeDArrayPosition DA qA μA tA)
    (codeDArrayPosition DB qB μB tB)
    (codeDArrayPosition DC qC μC tC)

theorem codeDSuccessorColumnNumbering_at
    (Q DA qA DB qB DC qC : ℕ)
    (μA : PositiveRationalLaw A) (tA : AlphabetTable A μA)
    (μB : PositiveRationalLaw B) (tB : AlphabetTable B μB)
    (μC : PositiveRationalLaw C) (tC : AlphabetTable C μC)
    (q : Fin Q)
    (i : Fin (codeDArray DA qA μA tA).size)
    (j : Fin (codeDArray DB qB μB tB).size)
    (k : Fin (codeDArray DC qC μC tC).size) :
    codeDSuccessorColumnNumbering Q DA qA DB qB DC qC
      μA tA μB tB μC tC
      (finProdFinEquiv (q,
        finProdFinEquiv (i, finProdFinEquiv (j, k)))) =
      (q, codeDArrayPosition DA qA μA tA i,
        codeDArrayPosition DB qB μB tB j,
        codeDArrayPosition DC qC μC tC k) := by
  exact successorColumnNumbering_at Q _ _ _
    (codeDArrayPosition DA qA μA tA)
    (codeDArrayPosition DB qB μB tB)
    (codeDArrayPosition DC qC μC tC) q i j k

#print axioms codeDArrayPosition
#print axioms codeDSuccessorColumnNumbering_at

end CurrentAdditive.IndexedExecutableStepRecovery
