import EthInapproximability.CurrentPaper.BitMachineStackRun

/-!
# Full-bank execution of a fixed scalar subroutine

This adapter does not provide arithmetic for free: its premise is a verified
run of a concrete finite `BitMachine.Machine`. It embeds that machine's whole
stack file into selected ambient stacks and proves every unselected stack is
unchanged. It is useful for assembling source-derived scalar branches around
the exact sampler's persistent writer cells.
-/

namespace EthInapproximability.CurrentPaper.ExactParameterMachineFrame

open Turing BitMachineEncoding BitMachineStackEmbedding

variable {J : Type*} [DecidableEq J]

def program (M : BitMachine.Machine) (ι : Fin M.stackCount ↪ J) :
    Fin M.labelCount → TM2.Stmt (fun _ : J => Bool) (Fin M.labelCount)
      (Fin M.controlCount) :=
  fun l => stackStmt ι (M.program l)

noncomputable def inputBank (M : BitMachine.Machine)
    (ι : Fin M.stackCount ↪ J) (foreign : J → List Bool) (bits : List Bool) :
    J → List Bool := bank ι foreign (M.init bits).stk

noncomputable def terminalBank (M : BitMachine.Machine)
    (ι : Fin M.stackCount ↪ J) (foreign : J → List Bool)
    (bits : List Bool) (T : ℕ) : J → List Bool :=
  bank ι foreign (M.run T (M.init bits)).stk

theorem run (M : BitMachine.Machine) (ι : Fin M.stackCount ↪ J)
    (foreign : J → List Bool) (bits : List Bool) (T : ℕ) :
    ((advance (program M ι))^[T])
      (⟨some M.start, M.initial, inputBank M ι foreign bits⟩ :
        TM2.Cfg (fun _ : J => Bool) _ _) =
      ⟨(M.run T (M.init bits)).l, (M.run T (M.init bits)).var,
        terminalBank M ι foreign bits T⟩ := by
  simpa only [program, inputBank, terminalBank, stackCfg,
    BitMachine.Machine.run, BitMachine.Machine.step, advance] using
    BitMachineStackRun.run ι foreign M.program (M.init bits) T

theorem output (M : BitMachine.Machine) (ι : Fin M.stackCount ↪ J)
    (foreign : J → List Bool) (bits result : List Bool) (T : ℕ)
    (h : M.OutputsWithin bits result T) :
    terminalBank M ι foreign bits T (ι M.output) = result := by
  rw [terminalBank, bank_at]
  exact (BitMachine.outputsWithin_at_bound M h).2

theorem halted (M : BitMachine.Machine) (ι : Fin M.stackCount ↪ J)
    (foreign : J → List Bool) (bits result : List Bool) (T : ℕ)
    (h : M.OutputsWithin bits result T) :
    (((advance (program M ι))^[T])
      (⟨some M.start, M.initial, inputBank M ι foreign bits⟩ :
        TM2.Cfg (fun _ : J => Bool) _ _)).l = none := by
  rw [run]
  exact (BitMachine.outputsWithin_at_bound M h).1

theorem foreign_at (M : BitMachine.Machine) (ι : Fin M.stackCount ↪ J)
    (foreign : J → List Bool) (bits : List Bool) (T : ℕ)
    (j : J) (hj : ¬ ∃ k, ι k = j) :
    terminalBank M ι foreign bits T j = foreign j :=
  bank_outside ι foreign _ j hj

end EthInapproximability.CurrentPaper.ExactParameterMachineFrame
