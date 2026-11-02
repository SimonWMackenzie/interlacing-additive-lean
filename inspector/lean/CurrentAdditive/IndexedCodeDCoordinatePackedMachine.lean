import CurrentAdditive.IndexedCodeDWordFieldMachine
import CurrentAdditive.IndexedCodeDCoordinateGetterRun

/-! The same fixed packed V2 getter/projection machine physically selects a
coordinate from a canonical Code D word, once the encoded word and unary
coordinate packet have been constructed. -/

namespace CurrentAdditive.IndexedExecutableStepRecovery

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open CurrentAdditive.CodeDCanonicalSourceV2
open CurrentAdditive.CodeDSourceCodecV2
open CurrentAdditive.GaussListContext
open Turing

theorem codeD_coordinate_machine_outputs {q : ℕ}
    (out : Array ((Fin q → Nat) × ℚ)) (j : Fin out.size)
    (p : Fin q) :
    let pre := (canonicalEntry out[j]).word.take p.val
    let word := (out[j].1 p).bits
    let suffix := (canonicalEntry out[j]).word.drop (p.val + 1)
    let source := CodeDCodecV2.encodeItems (canonicalEntry out[j]).word
    let input := codeDGetterPacket source p.val
    let finalBank := codeDGetterFinalBank source suffix word
    let packed := BitMachineBankCodec.encode finalBank
    let getterClock := (2*10+1)*(input.length+1) +
      (2*source.length+5+
        (4*(pre ++ word :: suffix).length.bits.length+6+
          IndexedFieldProgram.fieldCost (pre ++ [word]))) +
      2*packed.length+4
    codeDSelectedRecordMachine.OutputsWithin input word
      (getterClock + 2*packed.length+2 + (2*10+4)*(packed.length+1)) := by
  dsimp only
  let pre := (canonicalEntry out[j]).word.take p.val
  let word := (out[j].1 p).bits
  let suffix := (canonicalEntry out[j]).word.drop (p.val + 1)
  let source := CodeDCodecV2.encodeItems (canonicalEntry out[j]).word
  let input := codeDGetterPacket source p.val
  let finalBank := codeDGetterFinalBank source suffix word
  let packed := BitMachineBankCodec.encode finalBank
  let getterClock := (2*10+1)*(input.length+1) +
    (2*source.length+5+
      (4*(pre ++ word :: suffix).length.bits.length+6+
        IndexedFieldProgram.fieldCost (pre ++ [word]))) +
    2*packed.length+4
  obtain ⟨t, ht, hr⟩ := indexed_codeD_coordinate_getter_run out j p
  have hdecode : BitMachineBankCodec.decode 10 input =
      some (PreservingV2Program.initialBank source p.val) := by
    simp [input, codeDGetterPacket]
  have hraw : ((advance PreservingV2Program.program)^[t])
      (⟨some (.inl .scan), PreservingV2Program.copyControl ((), none),
        PreservingV2Program.initialBank source p.val⟩ :
        PreservingV2Program.Config) =
      ⟨none,
        PreservingV2Program.v2Control
          (IndexedV2Program.indexControl
            (SourceListMachineFields.coreControl (some true, false), none)),
        finalBank⟩ := by
    simpa only [PreservingV2Program.run, finalBank,
      codeDGetterFinalBank] using hr
  obtain ⟨u, S', hu, hpacked⟩ := BitMachineBankWrapper.packed_run
    PreservingV2Program.program (.inl .scan)
    (PreservingV2Program.copyControl ((), none)) input
    (PreservingV2Program.initialBank source p.val) hdecode t
    (⟨none,
      PreservingV2Program.v2Control
        (IndexedV2Program.indexControl
          (SourceListMachineFields.coreControl (some true, false), none)),
      finalBank⟩ : PreservingV2Program.Config)
    hraw rfl
  have hencode : BitMachineBankSerialize.encode (List.ofFn finalBank) =
      packed := by
    change BitMachineBankSerialize.encode (List.ofFn finalBank) =
      BitMachineBankCodec.encode finalBank
    rw [BitMachineBankCodec.encode_eq_list]
    rfl
  rw [hencode] at hu hpacked
  have ht' : t ≤ 2*source.length+5+
      (4*(pre ++ word :: suffix).length.bits.length+6+
        IndexedFieldProgram.fieldCost (pre ++ [word])) := by
    simpa only [source, pre, word, suffix] using ht
  have hclock : u ≤ getterClock := by
    dsimp [getterClock]
    omega
  have h1 : codeDGetterMachine.OutputsWithin input packed getterClock := by
    change (BitMachineBankWrapper.machine PreservingV2Program.program
        (.inl .scan) (PreservingV2Program.copyControl ((), none))).OutputsWithin
      input packed _
    apply outputsWithin_of_raw_run (.inr 0) (.inr 2)
      (.inr (.parse (.scan 0)))
      (PreservingV2Program.copyControl ((), none), none)
      (BitMachineBankWrapper.program PreservingV2Program.program
        (.inl .scan) (PreservingV2Program.copyControl ((), none)))
      input packed u _ hclock
    · rw [BitMachineBankWrapper.initial_cfg]
      change (BitMachineBankWrapper.run PreservingV2Program.program
        (.inl .scan) (PreservingV2Program.copyControl ((), none)) u _).l = none
      rw [hpacked]
      rfl
    · rw [BitMachineBankWrapper.initial_cfg]
      change (BitMachineBankWrapper.run PreservingV2Program.program
        (.inl .scan) (PreservingV2Program.copyControl ((), none)) u _).stk
          (.inr 2) = packed
      rw [hpacked]
      rfl
  have h2 : (BankFieldProjection.machine (6 : Fin 10)).OutputsWithin
      packed word ((2*10+4)*(packed.length+1)) := by
    have h := BankFieldProjection.outputs (6 : Fin 10) packed
    change (BankFieldProjection.machine (6 : Fin 10)).OutputsWithin
      packed (BankFieldProjection.result (6 : Fin 10) packed)
      ((2*10+4)*(packed.length+1)) at h
    have hword : BankFieldProjection.result (6 : Fin 10) packed = word := by
      rw [show packed = BitMachineBankCodec.encode finalBank from rfl,
        BankFieldProjection.result_encode,
        show finalBank = codeDGetterFinalBank source suffix word from rfl,
        codeDGetterFinalBank_selected]
    rw [hword] at h
    exact h
  exact BitMachineComposition.composition_outputsWithin
    codeDGetterMachine (BankFieldProjection.machine (6 : Fin 10)) h1 h2

#print axioms codeD_coordinate_machine_outputs

end CurrentAdditive.IndexedExecutableStepRecovery
