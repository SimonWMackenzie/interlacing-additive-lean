import CurrentAdditive.FeatureBoundedLift96
import CurrentAdditive.MachineInvokeClear

/-! Literal cleanup of the embedded inner scanner's banks 32--95. -/

namespace CurrentAdditive.FeatureClearInner96

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open CurrentAdditive.MinimumRatioContext
open Turing

abbrev Bank := Fin 96
abbrev Label := MachineInvokeClear.Label 64
abbrev Control := MachineInvokeClear.Control

def high : Fin 64 ↪ Bank := FeatureBoundedLift96.slot

def program : Label → TM2.Stmt (fun _ : Bank => Bool) Label Control
  | .clear i => BitMachineClearBank.clearStep (high i)
      (.clear i) (MachineInvokeClear.nextClear i)
  | .finish => BitMachineClearBank.finishStep id .done
  | .done => .halt

def time (S : Bank → List Bool) : Nat :=
  (∑ i : Fin 64, (S (high i)).length) + 66

def cleaned (S : Bank → List Bool) : Bank → List Bool :=
  BitMachineClearBank.cleared high S

theorem run (S : Bank → List Bool) :
    ((advance program)^[time S])
      (⟨some (MachineInvokeClear.clearLabel 64 0), ((),none), S⟩ :
        TM2.Cfg (fun _ : Bank => Bool) Label Control) =
      ⟨none, ((),none), cleaned S⟩ := by
  have hr := BitMachineClearBank.clear_bank_run program id .done
    64 high high.injective (MachineInvokeClear.clearLabel 64)
    (by
      intro i
      obtain ⟨h1,h2⟩ := MachineInvokeClear.clearLabel_step 64 i
      rw [h1,h2]
      rfl)
    (by rw [MachineInvokeClear.clearLabel_finish]; rfl) () S
  simp only [time, cleaned]
  rw [show (∑ i : Fin 64, (S (high i)).length) + 66 =
      ((∑ i : Fin 64, (S (high i)).length) + 64 + 1) + 1 by omega,
    Function.iterate_succ_apply', hr]
  rfl

theorem cleaned_low (S : Bank → List Bool) (k : Bank)
    (hk : k.val < 32) : cleaned S k = S k := by
  exact BitMachineClearBank.cleared_foreign high S k (by
    intro i h
    have hv := congrArg Fin.val h
    change 32+i.val = k.val at hv
    omega)

theorem cleaned_high (S : Bank → List Bool) (k : Bank)
    (hk : 32 ≤ k.val) : cleaned S k = [] := by
  have hi : k = high ⟨k.val-32, by have := k.isLt; omega⟩ := by
    apply Fin.ext
    simp [high, FeatureBoundedLift96.slot]
    omega
  rw [hi]
  exact BitMachineClearBank.cleared_bank high S _

#print axioms run
#print axioms cleaned_low
#print axioms cleaned_high

end CurrentAdditive.FeatureClearInner96
