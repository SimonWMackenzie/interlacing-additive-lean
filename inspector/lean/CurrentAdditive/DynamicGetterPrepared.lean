import CurrentAdditive.IndexedCodeDSelectedRecordMachine
import CurrentAdditive.IndexedV2Clock

set_option maxHeartbeats 1000000
namespace CurrentAdditive.DynamicGetterPrepared
open Turing EthInapproximability.CurrentPaper BitMachineEncoding
open GaussListContext IndexedExecutableStepRecovery
noncomputable section

theorem packed_outputs (pre : List (List Bool)) (word : List Bool)
    (suffix : List (List Bool)) :
    let source := SourceListEncoding.encode (pre ++ word :: suffix)
    let input := codeDGetterPacket source pre.length
    let packed := BitMachineBankCodec.encode (codeDGetterFinalBank source suffix word)
    codeDGetterMachine.OutputsWithin input packed
      (21*(input.length+1)+50*(source.length+1)^3+2*packed.length+4) := by
  dsimp only
  let source := SourceListEncoding.encode (pre ++ word :: suffix)
  let input := codeDGetterPacket source pre.length
  let finalBank := codeDGetterFinalBank source suffix word
  let packed := BitMachineBankCodec.encode finalBank
  obtain ⟨t,ht,hr⟩ := IndexedV2Clock.preserving_lookup_cubic pre word suffix
  have hd : BitMachineBankCodec.decode 10 input =
      some (PreservingV2Program.initialBank source pre.length) := by
    simp [input,codeDGetterPacket]
  have hraw : ((advance PreservingV2Program.program)^[t])
      (⟨some (.inl .scan),PreservingV2Program.copyControl ((),none),
       PreservingV2Program.initialBank source pre.length⟩ : PreservingV2Program.Config) =
      ⟨none,PreservingV2Program.v2Control
        (IndexedV2Program.indexControl
         (SourceListMachineFields.coreControl (some true,false),none)),finalBank⟩ := by
    simpa only [PreservingV2Program.run,PreservingV2Program.initial,
      finalBank,codeDGetterFinalBank] using hr
  obtain ⟨u,S',hu,hpacked⟩ := BitMachineBankWrapper.packed_run
    PreservingV2Program.program (.inl .scan)
    (PreservingV2Program.copyControl ((),none)) input
    (PreservingV2Program.initialBank source pre.length) hd t
    (⟨none,PreservingV2Program.v2Control
        (IndexedV2Program.indexControl
         (SourceListMachineFields.coreControl (some true,false),none)),finalBank⟩ :
       PreservingV2Program.Config) hraw rfl
  have he : BitMachineBankSerialize.encode (List.ofFn finalBank) = packed := by
    dsimp only [packed]
    rw [BitMachineBankCodec.encode_eq_list]; rfl
  rw [he] at hu hpacked
  apply outputsWithin_of_raw_run (.inr 0) (.inr 2) (.inr (.parse (.scan 0)))
    (PreservingV2Program.copyControl ((),none),none)
    (BitMachineBankWrapper.program PreservingV2Program.program (.inl .scan)
      (PreservingV2Program.copyControl ((),none))) input packed u _ (by
        dsimp only [input,packed,finalBank,source] at hu ht ⊢
        omega)
  · rw [BitMachineBankWrapper.initial_cfg]
    change (BitMachineBankWrapper.run _ _ _ u _).l = none
    rw [hpacked]; rfl
  · rw [BitMachineBankWrapper.initial_cfg]
    change (BitMachineBankWrapper.run _ _ _ u _).stk (.inr 2) = packed
    rw [hpacked]; rfl

theorem outputs (pre : List (List Bool)) (word : List Bool)
    (suffix : List (List Bool)) :
    let source := SourceListEncoding.encode (pre ++ word :: suffix)
    let input := codeDGetterPacket source pre.length
    codeDSelectedRecordMachine.OutputsWithin input word (5000*(input.length+1)^3) := by
  dsimp only
  let source := SourceListEncoding.encode (pre ++ word :: suffix)
  let input := codeDGetterPacket source pre.length
  let packed := BitMachineBankCodec.encode (codeDGetterFinalBank source suffix word)
  have h1 := packed_outputs pre word suffix
  have h2 : (BankFieldProjection.machine (6 : Fin 10)).OutputsWithin packed word
      (24*(packed.length+1)) := by
    simpa only [packed,BankFieldProjection.result_encode,codeDGetterFinalBank_selected] using
      BankFieldProjection.outputs (6 : Fin 10) packed
  have hs : source.length ≤ input.length := by
    change source.length ≤ (BitMachineBankCodec.encode _).length
    rw [BitMachineBankCodec.encode_length]
    simp [PreservingV2Program.initialBank,Fin.sum_univ_succ]
    omega
  have hf : (SourceListEncoding.fields suffix).length ≤ source.length := by
    dsimp [source,SourceListEncoding.encode]
    rw [IndexedV2Clock.fields_append]
    simp only [SourceListEncoding.fields,List.length_append]
    omega
  have hw : word.length ≤ source.length := by
    have h := IndexedV2Clock.fields_item_length_le (pre ++ word :: suffix) word (by simp)
    dsimp [source,SourceListEncoding.encode]
    simp only [List.length_append]
    omega
  have hp : packed.length ≤ 8*source.length+10 := by
    dsimp [packed]
    rw [BitMachineBankCodec.encode_length]
    simp [codeDGetterFinalBank,Fin.sum_univ_succ]
    omega
  apply BitMachine.outputsWithin_mono _
    (BitMachineComposition.composition_outputsWithin codeDGetterMachine
      (BankFieldProjection.machine (6 : Fin 10)) h1 h2)
  have hc := Nat.pow_le_pow_left (Nat.add_le_add_right hs 1) 3
  have hl : input.length+1 ≤ (input.length+1)^3 := by
    simpa using Nat.pow_le_pow_right (show 1 ≤ input.length+1 by omega)
      (show 1 ≤ 3 by omega)
  change 21*(input.length+1)+50*(source.length+1)^3+2*packed.length+4+
    2*packed.length+2+24*(packed.length+1) ≤ _
  nlinarith

#print axioms outputs
end
end CurrentAdditive.DynamicGetterPrepared
