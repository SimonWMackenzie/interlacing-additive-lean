import CurrentAdditive.MachineInvokeFull
import EthInapproximability.CurrentPaper.SourceListMachineWriter

/-! A literal V2 item field writer on an ambient bank. The target, copy
scratch, and eight embedded writer banks are physically cleared first. -/

namespace CurrentAdditive.V2ItemFrameCore

open Turing Turing.TM2 EthInapproximability.CurrentPaper
open CurrentAdditive.MinimumRatioContext
open MachineInvokeCore BitMachineEncoding

private noncomputable abbrev W := SourceListMachineWriter.framingMachine true

private theorem eight_stacks : W.stackCount = 8 := rfl

abbrev Slots (N : ℕ) := MachineInvokeCore.Slots W N

noncomputable def clearBank {N : ℕ} (C : Slots N) (i : Fin 10) : StackN N :=
  if i.val = 0 then C.target else if i.val = 1 then C.scratch else
    C.machine ⟨i.val - 2, by
      have hi := i.isLt
      rw [eight_stacks]
      omega⟩

theorem clearBank_injective {N : ℕ} (C : Slots N) :
    Function.Injective (clearBank C) := by
  intro i j h
  by_cases hi0 : i.val = 0
  · by_cases hj0 : j.val = 0
    · exact Fin.ext (by omega)
    · by_cases hj1 : j.val = 1
      · have hh : C.target = C.scratch := by simpa [clearBank, hi0, hj0, hj1] using h
        exact (C.target_scratch hh).elim
      · have hh : C.target = C.machine ⟨j.val - 2, by rw [eight_stacks]; omega⟩ := by
          simpa [clearBank, hi0, hj0, hj1] using h
        exact (C.target_machine _ hh).elim
  · by_cases hj0 : j.val = 0
    · by_cases hi1 : i.val = 1
      · have hh : C.scratch = C.target := by simpa [clearBank, hi0, hi1, hj0] using h
        exact (C.target_scratch hh.symm).elim
      · have hh : C.machine ⟨i.val - 2, by rw [eight_stacks]; omega⟩ = C.target := by
          simpa [clearBank, hi0, hi1, hj0] using h
        exact (C.target_machine _ hh.symm).elim
    · by_cases hi1 : i.val = 1
      · by_cases hj1 : j.val = 1
        · exact Fin.ext (by omega)
        · have hh : C.scratch = C.machine ⟨j.val - 2, by rw [eight_stacks]; omega⟩ := by
            simpa [clearBank, hi0, hi1, hj0, hj1] using h
          exact (C.scratch_machine _ hh).elim
      · by_cases hj1 : j.val = 1
        · have hh : C.machine ⟨i.val - 2, by rw [eight_stacks]; omega⟩ = C.scratch := by
            simpa [clearBank, hi0, hi1, hj0, hj1] using h
          exact (C.scratch_machine _ hh.symm).elim
        · have hh : C.machine ⟨i.val - 2, by rw [eight_stacks]; omega⟩ =
              C.machine ⟨j.val - 2, by rw [eight_stacks]; omega⟩ := by
            simpa [clearBank, hi0, hi1, hj0, hj1] using h
          have hv : i.val - 2 = j.val - 2 := by
            simpa only [Fin.val_mk] using congrArg Fin.val (C.machine.injective hh)
          exact Fin.ext (by omega)

theorem clearBank_foreign {N : ℕ} (C : Slots N) :
    ∀ i, clearBank C i ≠ C.source := by
  intro i
  by_cases hi0 : i.val = 0
  · simpa [clearBank, hi0] using C.source_target.symm
  by_cases hi1 : i.val = 1
  · simpa [clearBank, hi0, hi1] using C.source_scratch.symm
  simpa [clearBank, hi0, hi1] using (C.source_machine
    ⟨i.val - 2, by rw [eight_stacks]; omega⟩).symm

abbrev ClearLabel := MachineInvokeClear.Label 10
abbrev ClearControl := MachineInvokeClear.Control

noncomputable def clearProgram {N : ℕ} (C : Slots N) :
    ClearLabel → TM2.Stmt (fun _ : StackN N => Bool) ClearLabel ClearControl
  | .clear i => BitMachineClearBank.clearStep (clearBank C i)
      (.clear i) (MachineInvokeClear.nextClear i)
  | .finish => BitMachineClearBank.finishStep id .done
  | .done => .halt

noncomputable def clearTime {N : ℕ} (C : Slots N) (S : StackN N → List Bool) : ℕ :=
  (∑ i : Fin 10, (S (clearBank C i)).length) + 12

theorem clearRun {N : ℕ} (C : Slots N) (S : StackN N → List Bool) :
    ((advance (clearProgram C))^[clearTime C S])
      (⟨some (MachineInvokeClear.clearLabel 10 0),
        ((), none), S⟩ : TM2.Cfg (fun _ : StackN N => Bool) _ _) =
      ⟨none, ((), none), BitMachineClearBank.cleared (clearBank C) S⟩ := by
  have hr := BitMachineClearBank.clear_bank_run (clearProgram C) id .done
    10 (clearBank C) (clearBank_injective C)
    (MachineInvokeClear.clearLabel 10)
    (by
      intro i
      obtain ⟨h1, h2⟩ := MachineInvokeClear.clearLabel_step 10 i
      rw [h1, h2]
      rfl)
    (by rw [MachineInvokeClear.clearLabel_finish]; rfl) () S
  have hd : advance (clearProgram C)
      (⟨some .done, ((), none), BitMachineClearBank.cleared (clearBank C) S⟩ :
        TM2.Cfg (fun _ : StackN N => Bool) ClearLabel ClearControl) =
      ⟨none, ((), none), BitMachineClearBank.cleared (clearBank C) S⟩ := rfl
  simp only [clearTime]
  rw [show (∑ i : Fin 10, (S (clearBank C i)).length) + 12 =
      ((∑ i : Fin 10, (S (clearBank C i)).length) + 10 + 1) + 1 by omega,
    Function.iterate_succ_apply', hr, hd]

noncomputable def program {N : ℕ} (C : Slots N) :=
  BitMachineRawSequence.program (clearProgram C) (MachineInvokeFull.program C)
    (MachineInvokeFull.start C) ((), none) (MachineInvokeFull.control C)

noncomputable def start {N : ℕ} (C : Slots N) :
    BitMachineRawSequence.Label ClearLabel (MachineInvokeFull.LabelFull W) :=
  BitMachineRawSequence.leftLabel
    (MachineInvokeClear.clearLabel 10 0)

noncomputable def control {N : ℕ} (C : Slots N) :
    BitMachineRawSequence.Control ClearControl (MachineInvokeFull.ControlFull W) :=
  (((), none), MachineInvokeFull.control C)

noncomputable def cleared {N : ℕ} (C : Slots N) (S : StackN N → List Bool) :=
  BitMachineClearBank.cleared (clearBank C) S

theorem cleared_source {N : ℕ} (C : Slots N) (S : StackN N → List Bool) :
    cleared C S C.source = S C.source := by
  exact BitMachineClearBank.cleared_foreign (clearBank C) S C.source
    (clearBank_foreign C)

theorem cleared_target {N : ℕ} (C : Slots N) (S : StackN N → List Bool) :
    cleared C S C.target = [] := by
  exact BitMachineClearBank.cleared_bank (clearBank C) S 0

theorem cleared_scratch {N : ℕ} (C : Slots N) (S : StackN N → List Bool) :
    cleared C S C.scratch = [] := by
  exact BitMachineClearBank.cleared_bank (clearBank C) S 1

theorem cleared_machine {N : ℕ} (C : Slots N) (S : StackN N → List Bool) (i) :
    cleared C S (C.machine i) = [] := by
  have hi : i.val < 8 := by simpa only [eight_stacks] using i.isLt
  simpa [clearBank, hi] using
    (BitMachineClearBank.cleared_bank (clearBank C) S
      ⟨i.val + 2, by omega⟩)

noncomputable def writerTime (raw : List Bool) : ℕ :=
  (UnaryBinaryEncoding.coefficient + 7) * (raw.length + 1)^2

noncomputable def time {N : ℕ} (C : Slots N) (S : StackN N → List Bool) (raw : List Bool) : ℕ :=
  clearTime C S + MachineInvokeFull.uniformBound W raw (writerTime raw) + 1

theorem run {N : ℕ} (C : Slots N) (S : StackN N → List Bool)
    (raw : List Bool) (hsource : S C.source = raw) :
    ∃ u ≤ time C S raw,
      ((advance (program C))^[u])
        (⟨some (start C), control C, S⟩ :
          TM2.Cfg (fun _ : StackN N => Bool) _ _) =
        ⟨none, control C,
          Function.update (cleared C S) C.target
            (EncodedCommunication.natField raw.length ++ raw)⟩ := by
  let S' := cleared C S
  have hs : S' C.source = raw := by simpa only [S'] using (cleared_source C S).trans hsource
  obtain ⟨u, hu, hr⟩ := MachineInvokeFull.invoke_run_uniform C S' raw
    (SourceListMachineWriter.result true raw) (writerTime raw)
    hs (cleared_target C S) (cleared_scratch C S)
    (cleared_machine C S) (SourceListMachineWriter.outputs true raw)
  obtain ⟨v, hv, hrun⟩ := BitMachineRawSequence.runs
    (clearProgram C) (MachineInvokeFull.program C)
    (MachineInvokeClear.clearLabel 10 0)
    (MachineInvokeFull.start C) ((), none) ((), none)
    (MachineInvokeFull.control C) (MachineInvokeFull.control C)
    S S' (Function.update S' C.target (SourceListMachineWriter.result true raw))
    (clearTime C S) u (clearRun C S) hr
  refine ⟨v, by simpa only [time] using Nat.le_trans hv (by omega), ?_⟩
  simpa only [program, start, control, S', SourceListMachineWriter.result,
    Bool.true_eq, ↓reduceIte] using hrun

#print axioms run

end CurrentAdditive.V2ItemFrameCore
