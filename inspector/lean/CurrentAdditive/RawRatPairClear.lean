import CurrentAdditive.RawRatPairLift
import CurrentAdditive.MachineInvokeClear

/-! A charged physical sweep of the pair assembler's four temporary cells. -/

namespace CurrentAdditive.MinimumRatioContext.RawRatPairClear

open Turing EthInapproximability.CurrentPaper BitMachineEncoding
open MachineInvokeCore RawRatPairLift

def scratch {N : ℕ} (i : Fin 4) : StackN N :=
  localSlot N ⟨i.val + 2, by omega⟩

theorem scratch_injective {N : ℕ} : Function.Injective (scratch (N := N)) := by
  intro a b h
  have he := (localSlot N).injective h
  apply Fin.ext
  have hv := congrArg Fin.val he
  simp only at hv
  omega

abbrev Label := MachineInvokeClear.Label 4
abbrev Control := MachineInvokeClear.Control

def program (N : ℕ) : Label →
    TM2.Stmt (fun _ : StackN N => Bool) Label Control
  | .clear i => BitMachineClearBank.clearStep (scratch i)
      (.clear i) (MachineInvokeClear.nextClear i)
  | .finish => BitMachineClearBank.finishStep id .done
  | .done => .halt

def time {N : ℕ} (S : StackN N → List Bool) : ℕ :=
  (∑ i : Fin 4, (S (scratch i)).length) + 6

theorem run {N : ℕ} (S : StackN N → List Bool) :
    ((advance (program N))^[time S])
      (⟨some (MachineInvokeClear.clearLabel 4 0), ((), none), S⟩ :
        TM2.Cfg (fun _ : StackN N => Bool) Label Control) =
      ⟨none, ((), none), BitMachineClearBank.cleared scratch S⟩ := by
  have hr := BitMachineClearBank.clear_bank_run (program N) id .done
    4 scratch scratch_injective (MachineInvokeClear.clearLabel 4)
    (by
      intro i
      obtain ⟨h1, h2⟩ := MachineInvokeClear.clearLabel_step 4 i
      rw [h1, h2]
      rfl)
    (by rw [MachineInvokeClear.clearLabel_finish]; rfl) () S
  have hd : advance (program N)
      (⟨some .done, ((), none), BitMachineClearBank.cleared scratch S⟩ :
        TM2.Cfg (fun _ : StackN N => Bool) Label Control) =
      ⟨none, ((), none), BitMachineClearBank.cleared scratch S⟩ := rfl
  unfold time
  rw [show (∑ i : Fin 4, (S (scratch i)).length) + 6 =
      ((∑ i : Fin 4, (S (scratch i)).length) + 4 + 1) + 1 by omega,
    Function.iterate_succ_apply', hr, hd]

#print axioms run

end CurrentAdditive.MinimumRatioContext.RawRatPairClear
