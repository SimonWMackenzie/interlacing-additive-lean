import CurrentAdditive.FeaturePairRaw64
import CurrentAdditive.MachineInvokeClear
import EthInapproximability.CurrentPaper.BitMachineStackGrowth

/-! Literal final cleanup of every disposable feature-callback bank. -/

namespace CurrentAdditive.FeatureClearHigh64

open EthInapproximability.CurrentPaper
open CurrentAdditive.MinimumRatioContext
open Turing BitMachineEncoding

abbrev Bank := FeatureContext64.Bank
abbrev Label := MachineInvokeClear.Label 48
abbrev Control := MachineInvokeClear.Control

def high : Fin 48 ↪ Bank :=
  ⟨fun i => ⟨16 + i.val, by omega⟩, by
    intro i j h
    exact Fin.ext (by have := congrArg Fin.val h; simp at this; omega)⟩

def program : Label → TM2.Stmt (fun _ : Bank => Bool) Label Control
  | .clear i => BitMachineClearBank.clearStep (high i)
      (.clear i) (MachineInvokeClear.nextClear i)
  | .finish => BitMachineClearBank.finishStep id .done
  | .done => .halt

def time (S : Bank → List Bool) : Nat :=
  (∑ i : Fin 48, (S (high i)).length) + 50

def cleaned (S : Bank → List Bool) : Bank → List Bool :=
  BitMachineClearBank.cleared high S

theorem run (S : Bank → List Bool) :
    ((advance program)^[time S])
      (⟨some (MachineInvokeClear.clearLabel 48 0), ((),none), S⟩ :
        TM2.Cfg (fun _ : Bank => Bool) Label Control) =
      ⟨none, ((),none), cleaned S⟩ := by
  have hr := BitMachineClearBank.clear_bank_run program id .done
    48 high high.injective (MachineInvokeClear.clearLabel 48)
    (by
      intro i
      obtain ⟨h1,h2⟩ := MachineInvokeClear.clearLabel_step 48 i
      rw [h1,h2]
      rfl)
    (by rw [MachineInvokeClear.clearLabel_finish]; rfl) () S
  simp only [time, cleaned]
  rw [show (∑ i : Fin 48, (S (high i)).length) + 50 =
      ((∑ i : Fin 48, (S (high i)).length) + 48 + 1) + 1 by omega,
    Function.iterate_succ_apply', hr]
  rfl

theorem cleaned_low (S : Bank → List Bool) (k : Bank)
    (hk : k.val < 16) : cleaned S k = S k := by
  exact BitMachineClearBank.cleared_foreign high S k (by
    intro i h
    have hv := congrArg Fin.val h
    change 16+i.val = k.val at hv
    omega)

theorem cleaned_high (S : Bank → List Bool) (k : Bank)
    (hk : 16 ≤ k.val) : cleaned S k = [] := by
  have hi : k = high ⟨k.val-16, by have := k.isLt; omega⟩ := by
    apply Fin.ext
    simp [high]
    omega
  rw [hi]
  exact BitMachineClearBank.cleared_bank high S _

theorem time_after_run_le {L V : Type*} [DecidableEq L] [Fintype L]
    (P : L → TM2.Stmt (fun _ : Bank => Bool) L V)
    (z : TM2.Cfg (fun _ : Bank => Bool) L V)
    (T t : Nat) (ht : t ≤ T)
    (hblank : ∀ i : Fin 48, z.stk (high i) = []) :
    time ((((advance P)^[t]) z).stk) ≤
      48 * BitMachineStackGrowth.perStep P * T + 50 := by
  have hi (i : Fin 48) :
      (((((advance P)^[t]) z).stk (high i)).length) ≤
        BitMachineStackGrowth.perStep P * T := by
    have hg := BitMachineStackGrowth.run_growth P z t (high i)
    rw [hblank i, List.length_nil, Nat.zero_add] at hg
    exact hg.trans (Nat.mul_le_mul_left _ ht)
  have hsum := Finset.sum_le_sum
    (s := Finset.univ) (fun i (_ : i ∈ Finset.univ) => hi i)
  simp only [time, Finset.sum_const, Finset.card_fin,
    nsmul_eq_mul] at hsum ⊢
  nlinarith

#print axioms run
#print axioms cleaned_low
#print axioms cleaned_high
#print axioms time_after_run_le

end CurrentAdditive.FeatureClearHigh64
