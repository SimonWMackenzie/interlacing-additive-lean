import CurrentAdditive.IndexedCodeDWordFieldMachine

/-! Two concrete disjoint machine regions in one scheduler bank. The first
selects a Code D record; the second extracts its word field. A caller can keep
the coordinate and predecessor table in every other cell. -/

namespace CurrentAdditive.IndexedExecutableStepRecovery

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open CurrentAdditive.CodeDCanonicalSourceV2
open CurrentAdditive.CodeDSourceCodecV2
open CurrentAdditive.GaussListContext
open CurrentAdditive.MinimumRatioContext.MachineInvokeCore
open CurrentAdditive.MinimumRatioContext.MachineInvokeFull
open Turing

noncomputable abbrev contextTwoSize : ℕ :=
  codeDSelectedRecordMachine.stackCount + codeDWordFieldMachine.stackCount

noncomputable def recordSlots : Slots codeDSelectedRecordMachine contextTwoSize where
  machine := ⟨fun k => ⟨32 + k.val, by dsimp [contextTwoSize]; omega⟩, by
    intro x y h
    apply Fin.ext
    have hv := congrArg Fin.val h
    dsimp at hv
    omega⟩
  source := ⟨0, by omega⟩
  target := ⟨1, by omega⟩
  scratch := ⟨2, by omega⟩
  source_target := by intro h; have hv := congrArg Fin.val h; norm_num at hv
  source_scratch := by intro h; have hv := congrArg Fin.val h; norm_num at hv
  target_scratch := by intro h; have hv := congrArg Fin.val h; norm_num at hv
  source_machine := by
    intro k h
    have hv := congrArg Fin.val h
    dsimp at hv
    omega
  target_machine := by
    intro k h
    have hv := congrArg Fin.val h
    dsimp at hv
    omega
  scratch_machine := by
    intro k h
    have hv := congrArg Fin.val h
    dsimp at hv
    omega

noncomputable def wordSlots : Slots codeDWordFieldMachine contextTwoSize where
  machine := ⟨fun k => ⟨32 + codeDSelectedRecordMachine.stackCount + k.val,
    by dsimp [contextTwoSize]; omega⟩, by
    intro x y h
    apply Fin.ext
    have hv := congrArg Fin.val h
    dsimp at hv
    omega⟩
  source := ⟨1, by omega⟩
  target := ⟨3, by omega⟩
  scratch := ⟨2, by omega⟩
  source_target := by intro h; have hv := congrArg Fin.val h; norm_num at hv
  source_scratch := by intro h; have hv := congrArg Fin.val h; norm_num at hv
  target_scratch := by intro h; have hv := congrArg Fin.val h; norm_num at hv
  source_machine := by
    intro k h
    have hv := congrArg Fin.val h
    dsimp at hv
    omega
  target_machine := by
    intro k h
    have hv := congrArg Fin.val h
    dsimp at hv
    omega
  scratch_machine := by
    intro k h
    have hv := congrArg Fin.val h
    dsimp at hv
    omega

theorem slots_join (S : StackN contextTwoSize → List Bool)
    (record : List Bool)
    (hwordtarget : S wordSlots.target = [])
    (hscratch : S recordSlots.scratch = [])
    (hblank : ∀ k, S (wordSlots.machine k) = []) :
    let S' := Function.update S recordSlots.target record
    S' wordSlots.source = record ∧
    S' wordSlots.target = [] ∧
    S' wordSlots.scratch = [] ∧
    (∀ k, S' (wordSlots.machine k) = []) := by
  dsimp only
  constructor
  · change (Function.update S (1 : StackN contextTwoSize) record) 1 = record
    simp
  constructor
  · change (Function.update S (1 : StackN contextTwoSize) record) 3 = []
    simpa using hwordtarget
  constructor
  · change (Function.update S (1 : StackN contextTwoSize) record) 2 = []
    simpa using hscratch
  · intro k
    have hne : wordSlots.machine k ≠ recordSlots.target := by
      intro h
      have hv := congrArg Fin.val h
      dsimp [wordSlots, recordSlots] at hv
      omega
    simpa [Function.update_of_ne hne] using hblank k

theorem codeD_record_then_word_runs {q : ℕ}
    (out : Array ((Fin q → Nat) × ℚ)) (j : Fin out.size)
    (S : StackN contextTwoSize → List Bool)
    (hsource : S recordSlots.source =
      codeDGetterPacket (encodedSource out) j.val)
    (htarget1 : S recordSlots.target = [])
    (htarget2 : S wordSlots.target = [])
    (hscratch : S recordSlots.scratch = [])
    (hblank1 : ∀ k, S (recordSlots.machine k) = [])
    (hblank2 : ∀ k, S (wordSlots.machine k) = []) :
    let pre := (codeDRecords out).take j.val
    let selected := (codeDRecords out)[codeDRecordIndex out j]
    let suffix := (codeDRecords out).drop (j.val + 1)
    let source := encodedSource out
    let input := codeDGetterPacket source j.val
    let finalBank := codeDGetterFinalBank source suffix selected
    let packed := BitMachineBankCodec.encode finalBank
    let getterClock := (2*10+1)*(input.length+1) +
      (2*source.length+5+
        (4*(pre ++ selected :: suffix).length.bits.length+6+
          IndexedFieldProgram.fieldCost (pre ++ [selected]))) +
      2*packed.length+4
    let T1 := getterClock + 2*packed.length+2 + (2*10+4)*(packed.length+1)
    let record := encodeEntry (canonicalEntry out[j])
    let word := CodeDCodecV2.encodeItems (canonicalEntry out[j]).word
    let T2 := (2*2+4)*(record.length+1)
    let S1 := Function.update S recordSlots.target record
    let S2 := Function.update S1 wordSlots.target word
    ∃ u1 ≤ uniformBound codeDSelectedRecordMachine input T1,
      ∃ u2 ≤ uniformBound codeDWordFieldMachine record T2,
        ((advance (CurrentAdditive.MinimumRatioContext.MachineInvokeFull.program
          recordSlots))^[u1])
          (⟨some (CurrentAdditive.MinimumRatioContext.MachineInvokeFull.start
            recordSlots),
            CurrentAdditive.MinimumRatioContext.MachineInvokeFull.control
              recordSlots, S⟩ :
            TM2.Cfg (fun _ : StackN contextTwoSize => Bool) _ _) =
          ⟨none,
            CurrentAdditive.MinimumRatioContext.MachineInvokeFull.control
              recordSlots, S1⟩ ∧
        ((advance (CurrentAdditive.MinimumRatioContext.MachineInvokeFull.program
          wordSlots))^[u2])
          (⟨some (CurrentAdditive.MinimumRatioContext.MachineInvokeFull.start
            wordSlots),
            CurrentAdditive.MinimumRatioContext.MachineInvokeFull.control
              wordSlots, S1⟩ :
            TM2.Cfg (fun _ : StackN contextTwoSize => Bool) _ _) =
          ⟨none,
            CurrentAdditive.MinimumRatioContext.MachineInvokeFull.control
              wordSlots, S2⟩ := by
  dsimp only
  let record := encodeEntry (canonicalEntry out[j])
  let word := CodeDCodecV2.encodeItems (canonicalEntry out[j]).word
  let S1 := Function.update S recordSlots.target record
  have hM1 := codeD_selected_record_machine_outputs out j
  obtain ⟨u1, hu1, hr1⟩ := invoke_run_uniform recordSlots S
    (codeDGetterPacket (encodedSource out) j.val) record _
    hsource htarget1 hscratch hblank1 hM1
  have hjoin := slots_join S record htarget2 hscratch hblank2
  change S1 wordSlots.source = record ∧
    S1 wordSlots.target = [] ∧
    S1 wordSlots.scratch = [] ∧
    (∀ k, S1 (wordSlots.machine k) = []) at hjoin
  obtain ⟨hsource2, htarget2', hscratch2, hblank2'⟩ := hjoin
  have hM2 := codeD_word_field_outputs out j
  obtain ⟨u2, hu2, hr2⟩ := invoke_run_uniform wordSlots S1
    record word _ hsource2 htarget2' hscratch2 hblank2' hM2
  exact ⟨u1, hu1, u2, hu2, hr1, hr2⟩

#print axioms recordSlots
#print axioms wordSlots
#print axioms slots_join
#print axioms codeD_record_then_word_runs

end CurrentAdditive.IndexedExecutableStepRecovery
