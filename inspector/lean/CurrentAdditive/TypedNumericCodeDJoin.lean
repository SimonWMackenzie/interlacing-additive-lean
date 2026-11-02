import CurrentAdditive.InjectiveCodeDTransport
import CurrentAdditive.IndexedCodeDArrayBinding
import CurrentAdditive.CodeDArrayPositionDecode
import CurrentAdditive.CodeDTargetV2

/-!
The physical Code D target uses natural-number symbols.  These are the first
positions of the ordered typed alphabet, including when its array contains
repeated entries.  The same sequential materialization is used on both sides.
-/

namespace CurrentAdditive.TypedNumericCodeDJoin

open Paper2
open CurrentAdditive.ExecutableCodeSource
open CurrentAdditive.IndexedExecutableStep
open CurrentAdditive.OrderedAlphabetCodec
open CurrentAdditive.InjectiveCodeDTransport
open CurrentAdditive.SequentialSourceCode
open CurrentAdditive.CodeDCanonicalSourceV2

variable {Y : Type} [Fintype Y] [DecidableEq Y]

theorem typed_array_run (D q : Nat) (μ : PositiveRationalLaw Y)
    (table : AlphabetTable Y μ) :
    sequentialMaterialized D table.entries q =
      some (codeDArray D q μ table) := by
  unfold codeDArray
  obtain ⟨out, hout, _⟩ := sequentialMaterialized_total D
    table.entries table.positive q
  simp [hout]

theorem numeric_array_run (D q : Nat) (μ : PositiveRationalLaw Y)
    (table : AlphabetTable Y μ) :
    sequentialMaterialized D (numericEntries μ table) q =
      some (mapSource (encode μ table) (codeDArray D q μ table)) := by
  rw [show numericEntries μ table =
      table.entries.map (mapEntry (encode μ table)) from rfl]
  rw [sequentialMaterialized_map (encode μ table)
    (encode_injective μ table)]
  rw [typed_array_run]
  rfl

theorem numeric_target_exact (D q : Nat) (μ : PositiveRationalLaw Y)
    (table : AlphabetTable Y μ) :
    CurrentAdditive.CodeDTargetV2.targetBytes D (numericEntries μ table) q =
      some (encodedSource
        (mapSource (encode μ table) (codeDArray D q μ table))) := by
  simp [CurrentAdditive.CodeDTargetV2.targetBytes,
    numeric_array_run]

def numericPosition (D q : Nat) (μ : PositiveRationalLaw Y)
    (table : AlphabetTable Y μ)
    (j : Fin (codeDArray D q μ table).size) :
    Fin (mapSource (encode μ table) (codeDArray D q μ table)).size :=
  ⟨j.val, by simpa [mapSource] using j.isLt⟩

theorem numeric_coordinate_is_typed_position (D q : Nat)
    (μ : PositiveRationalLaw Y) (table : AlphabetTable Y μ)
    (j : Fin (codeDArray D q μ table).size) (p : Fin q) :
    ((mapSource (encode μ table) (codeDArray D q μ table))[numericPosition D q μ table j]).1 p =
      encode μ table ((fromTable D q μ table).decode
        (CurrentAdditive.IndexedExecutableStepRecovery.codeDArrayPosition
          D q μ table j) p) := by
  rw [CurrentAdditive.IndexedExecutableStepRecovery.codeDArrayPosition_decode]
  simp [numericPosition, mapSource, mapWord]

#print axioms typed_array_run
#print axioms numeric_array_run
#print axioms numeric_target_exact
#print axioms numeric_coordinate_is_typed_position

end CurrentAdditive.TypedNumericCodeDJoin
