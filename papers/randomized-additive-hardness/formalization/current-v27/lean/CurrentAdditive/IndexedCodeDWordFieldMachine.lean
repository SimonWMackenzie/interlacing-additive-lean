import CurrentAdditive.IndexedCodeDContextRecord

/-! Physical extraction of the word field from a selected canonical Code D
record. The field is the V2 source for the later coordinate getter. -/

namespace CurrentAdditive.IndexedExecutableStepRecovery

open EthInapproximability.CurrentPaper
open CurrentAdditive.CodeDCanonicalSourceV2
open CurrentAdditive.CodeDSourceCodecV2

noncomputable def codeDWordFieldMachine : BitMachine.Machine :=
  BankFieldProjection.machine (0 : Fin 2)

theorem codeD_word_field_outputs {q : ℕ}
    (out : Array ((Fin q → Nat) × ℚ)) (j : Fin out.size) :
    codeDWordFieldMachine.OutputsWithin
      (encodeEntry (canonicalEntry out[j]))
      (CodeDCodecV2.encodeItems (canonicalEntry out[j]).word)
      ((2*2+4)*((encodeEntry (canonicalEntry out[j])).length+1)) := by
  have h := BankFieldProjection.outputs (0 : Fin 2)
    (encodeEntry (canonicalEntry out[j]))
  change codeDWordFieldMachine.OutputsWithin
    (encodeEntry (canonicalEntry out[j]))
    (BankFieldProjection.result (0 : Fin 2)
      (encodeEntry (canonicalEntry out[j]))) _ at h
  have hr : BankFieldProjection.result (0 : Fin 2)
      (encodeEntry (canonicalEntry out[j])) =
      CodeDCodecV2.encodeItems (canonicalEntry out[j]).word := by
    simp [encodeEntry, BankFieldProjection.result_encode]
  rw [hr] at h
  exact h

#print axioms codeD_word_field_outputs

end CurrentAdditive.IndexedExecutableStepRecovery
