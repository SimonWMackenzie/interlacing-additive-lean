import CurrentAdditive.CodeDSuccessorColumnNumbering

/-! The explicit numeric label used by the successor reads exactly its
materialized Code D array entry. -/

namespace CurrentAdditive.IndexedExecutableStepRecovery

open Paper2
open CurrentAdditive.ExecutableCodeSource
open CurrentAdditive.IndexedExecutableStep

variable {Y : Type} [Fintype Y] [DecidableEq Y]

theorem codeDArrayPosition_cast (D q : ℕ)
    (μ : PositiveRationalLaw Y) (table : AlphabetTable Y μ)
    (j : Fin (codeDArray D q μ table).size) :
    cast (fromTable_label_type D q μ table)
      (codeDArrayPosition D q μ table j) = j := by
  change (Equiv.cast (fromTable_label_type D q μ table))
    ((Equiv.cast (fromTable_label_type D q μ table)).symm j) = j
  exact (Equiv.cast (fromTable_label_type D q μ table)).apply_symm_apply j

theorem codeDArrayPosition_decode (D q : ℕ)
    (μ : PositiveRationalLaw Y) (table : AlphabetTable Y μ)
    (j : Fin (codeDArray D q μ table).size) (p : Fin q) :
    (fromTable D q μ table).decode
      (codeDArrayPosition D q μ table j) p =
      (codeDArray D q μ table)[j].1 p := by
  simpa only [codeDArrayPosition_cast] using
    (fromTable_decode_array D q μ table
      (codeDArrayPosition D q μ table j) p)

#print axioms codeDArrayPosition_cast
#print axioms codeDArrayPosition_decode

end CurrentAdditive.IndexedExecutableStepRecovery
