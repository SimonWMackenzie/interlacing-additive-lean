import CurrentAdditive.IndexedCodeDSelectedRecord
import EthInapproximability.CurrentPaper.BitMachineBankWrapper

/-! One fixed bit machine runs the V2 indexed getter on a packed source-and-
index bank and returns the entire final bank packet.  Its cell 6 contains
the exact selected canonical Code D record. -/

namespace CurrentAdditive.IndexedExecutableStepRecovery

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open CurrentAdditive.CodeDCanonicalSourceV2
open CurrentAdditive.GaussListContext
open Turing

noncomputable def codeDGetterMachine : BitMachine.Machine :=
  BitMachineBankWrapper.machine PreservingV2Program.program
    (.inl .scan) (PreservingV2Program.copyControl ((), none))

def codeDGetterPacket (source : List Bool) (index : ℕ) : List Bool :=
  BitMachineBankCodec.encode (PreservingV2Program.initialBank source index)

def codeDGetterFinalBank (source : List Bool)
    (suffix : List (List Bool)) (word : List Bool) :
    Fin 10 → List Bool :=
  ![SourceListEncoding.fields suffix, [], [], [], [],
    List.replicate word.length true, word, [], source, []]

theorem codeDGetterFinalBank_selected (source : List Bool)
    (suffix : List (List Bool)) (word : List Bool) :
    codeDGetterFinalBank source suffix word 6 = word := rfl

theorem codeD_getter_packed_outputs {q : ℕ}
    (out : Array ((Fin q → Nat) × ℚ)) (j : Fin out.size) :
    let pre := (codeDRecords out).take j.val
    let word := (codeDRecords out)[codeDRecordIndex out j]
    let suffix := (codeDRecords out).drop (j.val + 1)
    let source := encodedSource out
    let input := codeDGetterPacket source j.val
    let finalBank := codeDGetterFinalBank source suffix word
    codeDGetterMachine.OutputsWithin input
      (BitMachineBankCodec.encode finalBank)
      ((2*10+1)*(input.length+1) +
        (2*source.length+5+
          (4*(pre ++ word :: suffix).length.bits.length+6+
            IndexedFieldProgram.fieldCost (pre ++ [word]))) +
        2*(BitMachineBankCodec.encode finalBank).length+4) := by
  dsimp only
  let pre := (codeDRecords out).take j.val
  let word := (codeDRecords out)[codeDRecordIndex out j]
  let suffix := (codeDRecords out).drop (j.val + 1)
  let source := encodedSource out
  let input := codeDGetterPacket source j.val
  let finalBank := codeDGetterFinalBank source suffix word
  obtain ⟨t, ht, hr⟩ := indexed_codeD_getter_run out j
  have hdecode : BitMachineBankCodec.decode 10 input =
      some (PreservingV2Program.initialBank source j.val) := by
    simp [input, codeDGetterPacket]
  have hraw : ((advance PreservingV2Program.program)^[t])
      (⟨some (.inl .scan), PreservingV2Program.copyControl ((), none),
        PreservingV2Program.initialBank source j.val⟩ :
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
    (PreservingV2Program.initialBank source j.val) hdecode t
    (⟨none,
      PreservingV2Program.v2Control
        (IndexedV2Program.indexControl
          (SourceListMachineFields.coreControl (some true, false), none)),
      finalBank⟩ : PreservingV2Program.Config)
    hraw rfl
  have hencode : BitMachineBankSerialize.encode (List.ofFn finalBank) =
      BitMachineBankCodec.encode finalBank := by
    rw [BitMachineBankCodec.encode_eq_list]
    rfl
  rw [hencode] at hu hpacked
  have ht' : t ≤ 2*source.length+5+
      (4*(pre ++ word :: suffix).length.bits.length+6+
        IndexedFieldProgram.fieldCost (pre ++ [word])) := by
    simpa only [source, pre, word, suffix] using ht
  have hclock : u ≤ (2*10+1)*(input.length+1) +
      (2*source.length+5+
        (4*(pre ++ word :: suffix).length.bits.length+6+
          IndexedFieldProgram.fieldCost (pre ++ [word]))) +
      2*(BitMachineBankCodec.encode finalBank).length+4 := by
    omega
  change (BitMachineBankWrapper.machine PreservingV2Program.program
      (.inl .scan) (PreservingV2Program.copyControl ((), none))).OutputsWithin
    input (BitMachineBankCodec.encode finalBank) _
  apply outputsWithin_of_raw_run (.inr 0) (.inr 2)
    (.inr (.parse (.scan 0)))
    (PreservingV2Program.copyControl ((), none), none)
    (BitMachineBankWrapper.program PreservingV2Program.program
      (.inl .scan) (PreservingV2Program.copyControl ((), none)))
    input (BitMachineBankCodec.encode finalBank) u _ hclock
  · rw [BitMachineBankWrapper.initial_cfg]
    change (BitMachineBankWrapper.run PreservingV2Program.program
      (.inl .scan) (PreservingV2Program.copyControl ((), none)) u _).l = none
    rw [hpacked]
    rfl
  · rw [BitMachineBankWrapper.initial_cfg]
    change (BitMachineBankWrapper.run PreservingV2Program.program
      (.inl .scan) (PreservingV2Program.copyControl ((), none)) u _).stk
        (.inr 2) = BitMachineBankCodec.encode finalBank
    rw [hpacked]
    rfl

#print axioms codeD_getter_packed_outputs

end CurrentAdditive.IndexedExecutableStepRecovery
