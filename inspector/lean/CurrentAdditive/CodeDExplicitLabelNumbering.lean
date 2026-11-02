import CurrentAdditive.IndexedCodeDArrayBinding

/-! The sequential Code D source labels are literal positions of its
materialized output array.  This gives an explicit cardinality and Fin
numbering; it does not assume or certify a physical Code D run. -/

namespace CurrentAdditive.IndexedExecutableStepRecovery

open Paper2
open CurrentAdditive.ExecutableCodeSource
open CurrentAdditive.IndexedExecutableStep

variable {Y : Type} [Fintype Y] [DecidableEq Y]

theorem codeD_label_card (D q : ℕ) (μ : PositiveRationalLaw Y)
    (table : AlphabetTable Y μ) :
    Fintype.card (fromTable D q μ table).Label =
      (codeDArray D q μ table).size := by
  change Fintype.card (Fin (codeDArray D q μ table).size) =
    (codeDArray D q μ table).size
  simp

noncomputable def codeD_label_fin (D q : ℕ)
    (μ : PositiveRationalLaw Y) (table : AlphabetTable Y μ) :
    Fin (Fintype.card (fromTable D q μ table).Label) ≃
      (fromTable D q μ table).Label :=
  (finCongr (codeD_label_card D q μ table)).trans
    (Equiv.cast (fromTable_label_type D q μ table)).symm

#print axioms codeD_label_card
#print axioms codeD_label_fin

end CurrentAdditive.IndexedExecutableStepRecovery
