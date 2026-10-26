import CurrentAdditive.IndexedCodeDPackedGetter
import EthInapproximability.CurrentPaper.BankFieldProjection
import EthInapproximability.CurrentPaper.BitMachineComposition

/-! A fixed bit machine selects the exact canonical Code D record from a
packed source-and-index input, including the output-field projection. -/

namespace CurrentAdditive.IndexedExecutableStepRecovery

open EthInapproximability.CurrentPaper
open CurrentAdditive.CodeDCanonicalSourceV2
open CurrentAdditive.CodeDSourceCodecV2
open CurrentAdditive.GaussListContext

noncomputable def codeDSelectedRecordMachine : BitMachine.Machine :=
  BitMachineComposition.composition codeDGetterMachine
    (BankFieldProjection.machine (6 : Fin 10))

theorem codeD_selected_record_machine_outputs {q : ℕ}
    (out : Array ((Fin q → Nat) × ℚ)) (j : Fin out.size) :
    let pre := (codeDRecords out).take j.val
    let word := (codeDRecords out)[codeDRecordIndex out j]
    let suffix := (codeDRecords out).drop (j.val + 1)
    let source := encodedSource out
    let input := codeDGetterPacket source j.val
    let finalBank := codeDGetterFinalBank source suffix word
    let packed := BitMachineBankCodec.encode finalBank
    let getterClock := (2*10+1)*(input.length+1) +
      (2*source.length+5+
        (4*(pre ++ word :: suffix).length.bits.length+6+
          IndexedFieldProgram.fieldCost (pre ++ [word]))) +
      2*packed.length+4
    codeDSelectedRecordMachine.OutputsWithin input
      (encodeEntry (canonicalEntry out[j]))
      (getterClock + 2*packed.length+2 + (2*10+4)*(packed.length+1)) := by
  dsimp only
  let pre := (codeDRecords out).take j.val
  let word := (codeDRecords out)[codeDRecordIndex out j]
  let suffix := (codeDRecords out).drop (j.val + 1)
  let source := encodedSource out
  let input := codeDGetterPacket source j.val
  let finalBank := codeDGetterFinalBank source suffix word
  let packed := BitMachineBankCodec.encode finalBank
  let getterClock := (2*10+1)*(input.length+1) +
    (2*source.length+5+
      (4*(pre ++ word :: suffix).length.bits.length+6+
        IndexedFieldProgram.fieldCost (pre ++ [word]))) +
    2*packed.length+4
  have h1 : codeDGetterMachine.OutputsWithin input packed getterClock :=
    codeD_getter_packed_outputs out j
  have h2 : (BankFieldProjection.machine (6 : Fin 10)).OutputsWithin
      packed (encodeEntry (canonicalEntry out[j]))
      ((2*10+4)*(packed.length+1)) := by
    have h := BankFieldProjection.outputs (6 : Fin 10) packed
    change (BankFieldProjection.machine (6 : Fin 10)).OutputsWithin
      packed (BankFieldProjection.result (6 : Fin 10) packed)
      ((2*10+4)*(packed.length+1)) at h
    have hword : BankFieldProjection.result (6 : Fin 10) packed =
        encodeEntry (canonicalEntry out[j]) := by
      rw [show packed = BitMachineBankCodec.encode finalBank from rfl,
        BankFieldProjection.result_encode,
        show finalBank = codeDGetterFinalBank source suffix word from rfl,
        codeDGetterFinalBank_selected]
      exact codeDRecords_get out j
    rw [hword] at h
    exact h
  have hc := BitMachineComposition.composition_outputsWithin
    codeDGetterMachine (BankFieldProjection.machine (6 : Fin 10)) h1 h2
  exact hc

#print axioms codeD_selected_record_machine_outputs

end CurrentAdditive.IndexedExecutableStepRecovery
