import CurrentAdditive.IndexedCodeDCoordinateContext
import EthInapproximability.CurrentPaper.BitMachineRawSequence

/-! One fixed TM2 program runs the actual indexed record selector followed by
the canonical word-field projection, preserving the full scheduler bank. -/

namespace CurrentAdditive.IndexedExecutableStepRecovery

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open CurrentAdditive.CodeDCanonicalSourceV2
open CurrentAdditive.CodeDSourceCodecV2
open CurrentAdditive.GaussListContext
open CurrentAdditive.MinimumRatioContext.MachineInvokeCore
open CurrentAdditive.MinimumRatioContext.MachineInvokeFull
open Turing

noncomputable def recordWordProgram :=
  BitMachineRawSequence.program
    (CurrentAdditive.MinimumRatioContext.MachineInvokeFull.program recordSlots)
    (CurrentAdditive.MinimumRatioContext.MachineInvokeFull.program wordSlots)
    (CurrentAdditive.MinimumRatioContext.MachineInvokeFull.start wordSlots)
    (CurrentAdditive.MinimumRatioContext.MachineInvokeFull.control recordSlots)
    (CurrentAdditive.MinimumRatioContext.MachineInvokeFull.control wordSlots)

theorem codeD_record_word_stitched {q : ℕ}
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
    ∃ t ≤ uniformBound codeDSelectedRecordMachine input T1 +
        uniformBound codeDWordFieldMachine record T2 + 1,
      ((advance recordWordProgram)^[t])
        (⟨some (BitMachineRawSequence.leftLabel
          (CurrentAdditive.MinimumRatioContext.MachineInvokeFull.start
            recordSlots)),
          (CurrentAdditive.MinimumRatioContext.MachineInvokeFull.control
            recordSlots,
           CurrentAdditive.MinimumRatioContext.MachineInvokeFull.control
            wordSlots), S⟩ : TM2.Cfg
          (fun _ : StackN contextTwoSize => Bool) _ _) =
        ⟨none,
          (CurrentAdditive.MinimumRatioContext.MachineInvokeFull.control
            recordSlots,
           CurrentAdditive.MinimumRatioContext.MachineInvokeFull.control
            wordSlots), S2⟩ := by
  dsimp only
  obtain ⟨t1, ht1, t2, ht2, hr1, hr2⟩ :=
    codeD_record_then_word_runs out j S
      hsource htarget1 htarget2 hscratch hblank1 hblank2
  obtain ⟨t, ht, hr⟩ := BitMachineRawSequence.runs
    (CurrentAdditive.MinimumRatioContext.MachineInvokeFull.program recordSlots)
    (CurrentAdditive.MinimumRatioContext.MachineInvokeFull.program wordSlots)
    (CurrentAdditive.MinimumRatioContext.MachineInvokeFull.start recordSlots)
    (CurrentAdditive.MinimumRatioContext.MachineInvokeFull.start wordSlots)
    (CurrentAdditive.MinimumRatioContext.MachineInvokeFull.control recordSlots)
    (CurrentAdditive.MinimumRatioContext.MachineInvokeFull.control recordSlots)
    (CurrentAdditive.MinimumRatioContext.MachineInvokeFull.control wordSlots)
    (CurrentAdditive.MinimumRatioContext.MachineInvokeFull.control wordSlots)
    S _ _ t1 t2 hr1 hr2
  refine ⟨t, by omega, ?_⟩
  exact hr

#print axioms codeD_record_word_stitched

end CurrentAdditive.IndexedExecutableStepRecovery
