import EthInapproximability.CurrentPaper.ExactParameterBranchInstall
import EthInapproximability.CurrentPaper.ExactParameterMachineFrame
import EthInapproximability.CurrentPaper.BitMachineClearBank

/-! A disjoint ambient slot layout for invoking one fixed Boolean-stack
machine without changing its source or any foreign bank. -/

namespace CurrentAdditive.MinimumRatioContext.MachineInvokeCore

open Turing EthInapproximability.CurrentPaper
open BitMachineEncoding BitMachineStackEmbedding

abbrev StackN (N : ℕ) := Fin (32 + N)

structure Slots (M : BitMachine.Machine) (N : ℕ) where
  machine : Fin M.stackCount ↪ StackN N
  source : StackN N
  target : StackN N
  scratch : StackN N
  source_target : source ≠ target
  source_scratch : source ≠ scratch
  target_scratch : target ≠ scratch
  source_machine : ∀ k, source ≠ machine k
  target_machine : ∀ k, target ≠ machine k
  scratch_machine : ∀ k, scratch ≠ machine k

def inputSlots {M : BitMachine.Machine} {N : ℕ} (C : Slots M N) :
    Fin 3 ↪ StackN N :=
  ⟨![C.source, C.machine M.input, C.scratch], by
    intro x y h
    fin_cases x <;> fin_cases y <;> simp_all
    all_goals
      first
      | exact (C.source_machine M.input h).elim
      | exact (C.source_machine M.input h.symm).elim
      | exact (C.scratch_machine M.input h).elim
      | exact (C.scratch_machine M.input h.symm).elim
      | exact (C.source_scratch h).elim
      | exact (C.source_scratch h.symm).elim⟩

def outputSlots {M : BitMachine.Machine} {N : ℕ} (C : Slots M N) :
    Fin 3 ↪ StackN N :=
  ⟨![C.machine M.output, C.target, C.scratch], by
    intro x y h
    fin_cases x <;> fin_cases y <;> simp_all
    all_goals
      first
      | exact (C.target_machine M.output h).elim
      | exact (C.target_machine M.output h.symm).elim
      | exact (C.scratch_machine M.output h).elim
      | exact (C.scratch_machine M.output h.symm).elim
      | exact (C.target_scratch h).elim
      | exact (C.target_scratch h.symm).elim⟩

def inputProgram {M : BitMachine.Machine} {N : ℕ} (C : Slots M N) :=
  ExactParameterBranchInstall.copyProgram (inputSlots C)

def machineProgram {M : BitMachine.Machine} {N : ℕ} (C : Slots M N) :=
  ExactParameterMachineFrame.program M C.machine

def outputProgram {M : BitMachine.Machine} {N : ℕ} (C : Slots M N) :=
  ExactParameterBranchInstall.copyProgram (outputSlots C)

theorem input_run {M : BitMachine.Machine} {N : ℕ} (C : Slots M N)
    (S : StackN N → List Bool) (bits : List Bool)
    (hsource : S C.source = bits)
    (hblank : ∀ k, S (C.machine k) = [])
    (hscratch : S C.scratch = []) :
    ∃ u ≤ 2 * bits.length + 2,
      ((advance (inputProgram C))^[u])
        (⟨some .scan, none, S⟩ : TM2.Cfg (fun _ : StackN N => Bool)
          BitMachineCopy.Label (Option Bool)) =
      ⟨none, none, Function.update S (C.machine M.input) bits⟩ := by
  have hsource' : S ((inputSlots C) 0) = bits := by
    simpa [inputSlots] using hsource
  have htarget' : S ((inputSlots C) 1) = [] := by
    simpa [inputSlots] using hblank M.input
  have hscratch' : S ((inputSlots C) 2) = [] := by
    simpa [inputSlots] using hscratch
  simpa [inputProgram, inputSlots] using
    ExactParameterBranchInstall.copy_run (inputSlots C) S bits
      hsource' htarget' hscratch'

theorem input_bank_eq {M : BitMachine.Machine} {N : ℕ} (C : Slots M N)
    (S : StackN N → List Bool) (bits : List Bool)
    (hblank : ∀ k, S (C.machine k) = []) :
    ExactParameterMachineFrame.inputBank M C.machine S bits =
      Function.update S (C.machine M.input) bits := by
  have hloc : (M.init bits).stk =
      Function.update (fun k => S (C.machine k)) M.input bits := by
    funext k
    by_cases hk : k = M.input
    · subst k
      simp [BitMachine.Machine.init]
    · simp [BitMachine.Machine.init, hk, hblank k]
  unfold ExactParameterMachineFrame.inputBank
  rw [hloc, bank_update, bank_restrict]

theorem machine_run {M : BitMachine.Machine} {N : ℕ} (C : Slots M N)
    (S : StackN N → List Bool) (bits result : List Bool) (T : ℕ)
    (hblank : ∀ k, S (C.machine k) = [])
    (hM : M.OutputsWithin bits result T) :
    ((advance (machineProgram C))^[T])
      (⟨some M.start, M.initial,
        Function.update S (C.machine M.input) bits⟩ :
          TM2.Cfg (fun _ : StackN N => Bool) _ _) =
      ⟨none, (M.run T (M.init bits)).var,
        ExactParameterMachineFrame.terminalBank M C.machine S bits T⟩ := by
  have hr := ExactParameterMachineFrame.run M C.machine S bits T
  rw [input_bank_eq C S bits hblank] at hr
  rw [(BitMachine.outputsWithin_at_bound M hM).1] at hr
  exact hr

theorem output_run {M : BitMachine.Machine} {N : ℕ} (C : Slots M N)
    (S : StackN N → List Bool) (bits result : List Bool) (T : ℕ)
    (htarget : S C.target = [])
    (hscratch : S C.scratch = [])
    (hM : M.OutputsWithin bits result T) :
    ∃ u ≤ 2 * result.length + 2,
      ((advance (outputProgram C))^[u])
        (⟨some .scan, none,
          ExactParameterMachineFrame.terminalBank M C.machine S bits T⟩ :
          TM2.Cfg (fun _ : StackN N => Bool)
            BitMachineCopy.Label (Option Bool)) =
      ⟨none, none,
        Function.update
          (ExactParameterMachineFrame.terminalBank M C.machine S bits T)
          C.target result⟩ := by
  let U := ExactParameterMachineFrame.terminalBank M C.machine S bits T
  have hsrc : U ((outputSlots C) 0) = result := by
    simpa [U, outputSlots] using
      ExactParameterMachineFrame.output M C.machine S bits result T hM
  have htgt : U ((outputSlots C) 1) = [] := by
    rw [show (outputSlots C) 1 = C.target by simp [outputSlots]]
    change ExactParameterMachineFrame.terminalBank M C.machine S bits T C.target = []
    rw [ExactParameterMachineFrame.foreign_at M C.machine S bits T C.target
      (by intro ⟨k, he⟩; exact C.target_machine k he.symm)]
    exact htarget
  have hscr : U ((outputSlots C) 2) = [] := by
    rw [show (outputSlots C) 2 = C.scratch by simp [outputSlots]]
    change ExactParameterMachineFrame.terminalBank M C.machine S bits T C.scratch = []
    rw [ExactParameterMachineFrame.foreign_at M C.machine S bits T C.scratch
      (by intro ⟨k, he⟩; exact C.scratch_machine k he.symm)]
    exact hscratch
  simpa [outputProgram, outputSlots, U] using
    ExactParameterBranchInstall.copy_run (outputSlots C) U result
      hsrc htgt hscr

#print axioms input_run
#print axioms machine_run
#print axioms output_run

end CurrentAdditive.MinimumRatioContext.MachineInvokeCore
