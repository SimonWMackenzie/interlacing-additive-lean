import CurrentAdditive.MachineInvokeCore
import EthInapproximability.CurrentPaper.BitMachineRawSequence

/-! A literal sweep of every embedded machine bank, charging every pop. -/

namespace CurrentAdditive.MinimumRatioContext.MachineInvokeClear

open Turing EthInapproximability.CurrentPaper
open MachineInvokeCore BitMachineEncoding

inductive Label (n : ℕ) where
  | clear : Fin n → Label n
  | finish | done
  deriving DecidableEq, Fintype

abbrev Control := Unit × Option Bool

def nextClear {n : ℕ} (i : Fin n) : Label n :=
  if h : i.val + 1 < n then .clear ⟨i.val + 1, h⟩ else .finish

def clearLabel (n : ℕ) (i : Fin (n + 1)) : Label n :=
  if h : i.val < n then .clear ⟨i.val, h⟩ else .finish

def program {M : BitMachine.Machine} {N : ℕ} (C : Slots M N) :
    Label M.stackCount → TM2.Stmt (fun _ : StackN N => Bool)
      (Label M.stackCount) Control
  | .clear i => BitMachineClearBank.clearStep (C.machine i)
      (.clear i) (nextClear i)
  | .finish => BitMachineClearBank.finishStep id .done
  | .done => .halt

theorem clearLabel_step (n : ℕ) (i : Fin n) :
    clearLabel n i.castSucc = .clear i ∧
    clearLabel n i.succ = nextClear i := by
  constructor
  · simp [clearLabel]
  · unfold clearLabel nextClear
    by_cases h : i.val + 1 < n <;> simp [h]

theorem clearLabel_finish (n : ℕ) :
    clearLabel n (Fin.last n) = .finish := by
  simp [clearLabel]

def time {M : BitMachine.Machine} {N : ℕ} (C : Slots M N)
    (S : StackN N → List Bool) : ℕ :=
  (∑ i : Fin M.stackCount, (S (C.machine i)).length) + M.stackCount + 2

theorem run {M : BitMachine.Machine} {N : ℕ} (C : Slots M N)
    (S : StackN N → List Bool) :
    ((advance (program C))^[time C S])
      (⟨some (clearLabel M.stackCount 0), ((), none), S⟩ :
        TM2.Cfg (fun _ : StackN N => Bool) (Label M.stackCount) Control) =
      ⟨none, ((), none), BitMachineClearBank.cleared C.machine S⟩ := by
  have hr := BitMachineClearBank.clear_bank_run (program C) id .done
    M.stackCount C.machine C.machine.injective (clearLabel M.stackCount)
    (by
      intro i
      obtain ⟨h1, h2⟩ := clearLabel_step M.stackCount i
      rw [h1, h2]
      rfl)
    (by rw [clearLabel_finish]; rfl) () S
  have hd : advance (program C)
      (⟨some .done, ((), none), BitMachineClearBank.cleared C.machine S⟩ :
        TM2.Cfg (fun _ : StackN N => Bool) (Label M.stackCount) Control) =
      ⟨none, ((), none), BitMachineClearBank.cleared C.machine S⟩ := rfl
  simp only [time]
  rw [show (∑ i : Fin M.stackCount, (S (C.machine i)).length) +
      M.stackCount + 2 =
      ((∑ i : Fin M.stackCount, (S (C.machine i)).length) +
      M.stackCount + 1) + 1 by omega,
    Function.iterate_succ_apply', hr, hd]

#print axioms run

end CurrentAdditive.MinimumRatioContext.MachineInvokeClear
