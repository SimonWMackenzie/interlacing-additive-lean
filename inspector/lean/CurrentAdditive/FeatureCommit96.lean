import CurrentAdditive.FeatureOutputTransfer96
import CurrentAdditive.FeatureClearInner96
import EthInapproximability.CurrentPaper.ExactParameterBranchInstall

/-! Exact whole-bank output and count updates for an eligible descriptor.
These proofs retain the scratch-cell facts needed by the next traversal. -/

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 500000
namespace CurrentAdditive.FeatureCommit96
open Turing EthInapproximability.CurrentPaper BitMachineEncoding

theorem transfer_exact (S : Fin 96 → List Bool) (output : List Bool)
    (h41 : S 41=output) (h16 : S 16=[]) :
    ∃ t ≤ (S 9).length+2+2*output.length+2+1,
      ((advance FeatureOutputTransfer96.transferProgram)^[t])
        (⟨some (BitMachineRawSequence.leftLabel FeatureOutputTransfer96.ClearLabel.scan),
          (((),none),none),S⟩ : TM2.Cfg (fun _ : Fin 96 => Bool) _ _) =
      ⟨none,(((),none),none),Function.update S 9 output⟩ := by
  let U := Function.update S (9 : Fin 96) []
  have hc := FeatureOutputTransfer96.clear_output S
  obtain ⟨b,hb,hr⟩ := ExactParameterBranchInstall.copy_run
    FeatureOutputTransfer96.copySlot U output
    (by simpa [U,FeatureOutputTransfer96.copySlot] using h41)
    (by simp [U,FeatureOutputTransfer96.copySlot])
    (by simpa [U,FeatureOutputTransfer96.copySlot] using h16)
  obtain ⟨t,ht,he⟩ := BitMachineRawSequence.runs
    FeatureOutputTransfer96.clearProgram FeatureOutputTransfer96.copyProgram
    FeatureOutputTransfer96.ClearLabel.scan BitMachineCopy.Label.scan
    (((),none) : Unit × Option Bool) (((),none) : Unit × Option Bool)
    (none : Option Bool) (none : Option Bool)
    S U (Function.update S 9 output) ((S 9).length+2) b
    (by simpa only [FeatureOutputTransfer96.clearRun,U] using hc)
    (by simpa [FeatureOutputTransfer96.copyProgram,
      ExactParameterBranchInstall.copyProgram,U,FeatureOutputTransfer96.copySlot] using hr)
  exact ⟨t,by omega,by simpa only [FeatureOutputTransfer96.transferProgram] using he⟩

theorem count_finished (S : Fin 96 → List Bool) (alphabetCount count : List Bool)
    (h31 : S 31=alphabetCount) (h12 : S 12=count) (h16 : S 16=[]) :
    (FeatureCountAppend96.finished S alphabetCount count).stk =
      Function.update S 12 (alphabetCount++count) := by
  have hi := FeatureCountAppend96.prepared_eq S alphabetCount count h31 h12 h16
  have hbank := congrArg TM2.Cfg.stk hi
  change BitMachineStackEmbedding.bank FeatureCountAppend96.slot S
    (BitMachineCopy.stackContents alphabetCount count []) = S at hbank
  change BitMachineStackEmbedding.bank FeatureCountAppend96.slot S
    (BitMachineCopy.stackContents alphabetCount (alphabetCount++count) []) = _
  have hl : BitMachineCopy.stackContents alphabetCount (alphabetCount++count) [] =
      Function.update (BitMachineCopy.stackContents alphabetCount count [])
        1 (alphabetCount++count) := by
    funext k
    fin_cases k <;> rfl
  rw [hl,BitMachineStackEmbedding.bank_update,hbank]
  rfl

theorem count_exact (S : Fin 96 → List Bool) (alphabetCount count : List Bool)
    (h31 : S 31=alphabetCount) (h12 : S 12=count) (h16 : S 16=[]) :
    ∃ t ≤ 2*alphabetCount.length+2,
      ((advance FeatureCountAppend96.program)^[t])
        (⟨some .scan,none,S⟩ : TM2.Cfg (fun _ : Fin 96 => Bool) _ _) =
      ⟨none,none,Function.update S 12 (alphabetCount++count)⟩ := by
  obtain ⟨t,ht,hr⟩ := FeatureCountAppend96.append_run S alphabetCount count
  rw [FeatureCountAppend96.prepared_eq S alphabetCount count h31 h12 h16] at hr
  have hb := count_finished S alphabetCount count h31 h12 h16
  change FeatureCountAppend96.run t _ =
    ⟨none,none,(FeatureCountAppend96.finished S alphabetCount count).stk⟩ at hr
  rw [hb] at hr
  exact ⟨t,ht,hr⟩

#print axioms transfer_exact
#print axioms count_exact
end CurrentAdditive.FeatureCommit96
