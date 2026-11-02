import CurrentAdditive.IndexedCodeDPacketAmbientSerializer

/-! The fixed coordinate getter consumes the physically serialized V2 packet
from low scheduler cell 5 and writes the actual Code D symbol bits to cell 6.
It reuses the cleared machine region of the earlier record getter. -/

namespace CurrentAdditive.IndexedExecutableStepRecovery

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open CurrentAdditive.CodeDCanonicalSourceV2
open CurrentAdditive.CodeDSourceCodecV2
open CurrentAdditive.GaussListContext
open CurrentAdditive.MinimumRatioContext.MachineInvokeCore
open CurrentAdditive.MinimumRatioContext.MachineInvokeFull
open Turing

noncomputable def coordinateSlots :
    Slots codeDSelectedRecordMachine contextTwoSize where
  machine := recordSlots.machine
  source := ⟨5, by omega⟩
  target := ⟨6, by omega⟩
  scratch := ⟨2, by omega⟩
  source_target := by intro h; have hv := congrArg Fin.val h; norm_num at hv
  source_scratch := by intro h; have hv := congrArg Fin.val h; norm_num at hv
  target_scratch := by intro h; have hv := congrArg Fin.val h; norm_num at hv
  source_machine := by
    intro k h
    have hv := congrArg Fin.val h
    dsimp [recordSlots] at hv
    omega
  target_machine := by
    intro k h
    have hv := congrArg Fin.val h
    dsimp [recordSlots] at hv
    omega
  scratch_machine := by
    intro k h
    have hv := congrArg Fin.val h
    dsimp [recordSlots] at hv
    omega

theorem codeD_coordinate_context_run {q : ℕ}
    (out : Array ((Fin q → Nat) × ℚ)) (j : Fin out.size)
    (p : Fin q)
    (S : StackN contextTwoSize → List Bool)
    (hsource : S coordinateSlots.source =
      codeDGetterPacket
        (CodeDCodecV2.encodeItems (canonicalEntry out[j]).word) p.val)
    (htarget : S coordinateSlots.target = [])
    (hscratch : S coordinateSlots.scratch = [])
    (hblank : ∀ k, S (coordinateSlots.machine k) = []) :
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
    let T := getterClock + 2*packed.length+2 + (2*10+4)*(packed.length+1)
    ∃ u ≤ uniformBound codeDSelectedRecordMachine input T,
      ((advance (CurrentAdditive.MinimumRatioContext.MachineInvokeFull.program
        coordinateSlots))^[u])
        (⟨some (CurrentAdditive.MinimumRatioContext.MachineInvokeFull.start
          coordinateSlots),
          CurrentAdditive.MinimumRatioContext.MachineInvokeFull.control
            coordinateSlots, S⟩ :
          TM2.Cfg (fun _ : StackN contextTwoSize => Bool) _ _) =
        ⟨none, CurrentAdditive.MinimumRatioContext.MachineInvokeFull.control
          coordinateSlots,
          Function.update S coordinateSlots.target (out[j].1 p).bits⟩ := by
  dsimp only
  have hM := codeD_coordinate_machine_outputs out j p
  exact invoke_run_uniform coordinateSlots S
    (codeDGetterPacket
      (CodeDCodecV2.encodeItems (canonicalEntry out[j]).word) p.val)
    (out[j].1 p).bits _ hsource htarget hscratch hblank hM

#print axioms coordinateSlots
#print axioms codeD_coordinate_context_run

end CurrentAdditive.IndexedExecutableStepRecovery
