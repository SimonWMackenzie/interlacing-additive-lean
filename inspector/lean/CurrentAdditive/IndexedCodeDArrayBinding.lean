import CurrentAdditive.ExecutableSources
import CurrentAdditive.CodeDCanonicalSourceV2

/-! Identify the exact materialized array whose indexed positions become
`fromTable` source labels.  This is the target of the developing physical
Code_D machine; decoded words are read from that same array position. -/

namespace CurrentAdditive.IndexedExecutableStep

open Paper2
open CurrentAdditive.ExecutableCodeSource
open CurrentAdditive.SequentialCode
open CurrentAdditive.SequentialSourceCode

variable {Y : Type} [Fintype Y] [DecidableEq Y]

noncomputable def codeDArray (D q : ℕ) (μ : PositiveRationalLaw Y)
    (table : AlphabetTable Y μ) : Array ((Fin q → Y) × ℚ) :=
  (sequentialMaterialized D table.entries q).get (by
    obtain ⟨out, hout, _⟩ := sequentialMaterialized_total D
      table.entries table.positive q
    simp [hout])

theorem fromTable_label_type (D q : ℕ) (μ : PositiveRationalLaw Y)
    (table : AlphabetTable Y μ) :
    (fromTable D q μ table).Label = Fin (codeDArray D q μ table).size := by
  rfl

theorem fromTable_decode_array (D q : ℕ) (μ : PositiveRationalLaw Y)
    (table : AlphabetTable Y μ)
    (j : (fromTable D q μ table).Label) (p : Fin q) :
    (fromTable D q μ table).decode j p =
      (codeDArray D q μ table)[
        cast (by simpa only [fromTable_label_type] using rfl :
          (fromTable D q μ table).Label =
            Fin (codeDArray D q μ table).size) j].1 p := by
  rfl

#print axioms fromTable_label_type
#print axioms fromTable_decode_array

end CurrentAdditive.IndexedExecutableStep
