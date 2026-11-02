import CurrentAdditive.IndexedCodeDSelectedRecordMachine
import CurrentAdditive.MachineInvokeFull

/-! A fixed Code D record getter can be invoked inside a larger scheduler bank.
The other scheduler cells, in particular a later coordinate and predecessor
table, are retained exactly. This is a local callback, not a stage producer. -/

namespace CurrentAdditive.IndexedExecutableStepRecovery

open EthInapproximability.CurrentPaper
open CurrentAdditive.CodeDCanonicalSourceV2
open CurrentAdditive.CodeDSourceCodecV2
open CurrentAdditive.GaussListContext
open CurrentAdditive.MinimumRatioContext.MachineInvokeCore
open CurrentAdditive.MinimumRatioContext.MachineInvokeFull
open Turing
open EthInapproximability.CurrentPaper.BitMachineEncoding

def contextSlots (M : BitMachine.Machine) : Slots M M.stackCount where
  machine := ⟨fun k => ⟨32 + k.val, by omega⟩, by
    intro x y h
    apply Fin.ext
    have hv := congrArg Fin.val h
    dsimp at hv
    omega⟩
  source := ⟨0, by omega⟩
  target := ⟨1, by omega⟩
  scratch := ⟨2, by omega⟩
  source_target := by
    intro h
    have hv := congrArg Fin.val h
    norm_num at hv
  source_scratch := by
    intro h
    have hv := congrArg Fin.val h
    norm_num at hv
  target_scratch := by
    intro h
    have hv := congrArg Fin.val h
    norm_num at hv
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

noncomputable def codeDContextRecordProgram :=
  CurrentAdditive.MinimumRatioContext.MachineInvokeFull.program
    (contextSlots codeDSelectedRecordMachine)

theorem codeD_context_record_run {q : ℕ}
    (out : Array ((Fin q → Nat) × ℚ)) (j : Fin out.size)
    (S : StackN codeDSelectedRecordMachine.stackCount → List Bool)
    (hsource : S (contextSlots codeDSelectedRecordMachine).source =
      codeDGetterPacket (encodedSource out) j.val)
    (htarget : S (contextSlots codeDSelectedRecordMachine).target = [])
    (hscratch : S (contextSlots codeDSelectedRecordMachine).scratch = [])
    (hblank : ∀ k, S ((contextSlots codeDSelectedRecordMachine).machine k) = []) :
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
    let T := getterClock + 2*packed.length+2 + (2*10+4)*(packed.length+1)
    ∃ u ≤ uniformBound codeDSelectedRecordMachine input T,
      ((advance codeDContextRecordProgram)^[u])
        (⟨some (CurrentAdditive.MinimumRatioContext.MachineInvokeFull.start
          (contextSlots codeDSelectedRecordMachine)),
          CurrentAdditive.MinimumRatioContext.MachineInvokeFull.control
            (contextSlots codeDSelectedRecordMachine), S⟩ :
          TM2.Cfg
            (fun _ : StackN codeDSelectedRecordMachine.stackCount => Bool) _ _) =
        ⟨none, CurrentAdditive.MinimumRatioContext.MachineInvokeFull.control
          (contextSlots codeDSelectedRecordMachine),
          Function.update S (contextSlots codeDSelectedRecordMachine).target
            (encodeEntry (canonicalEntry out[j]))⟩ := by
  dsimp only
  have hM := codeD_selected_record_machine_outputs out j
  exact invoke_run_uniform (contextSlots codeDSelectedRecordMachine)
    S (codeDGetterPacket (encodedSource out) j.val)
    (encodeEntry (canonicalEntry out[j])) _
    hsource htarget hscratch hblank hM

#print axioms contextSlots
#print axioms codeD_context_record_run

end CurrentAdditive.IndexedExecutableStepRecovery
