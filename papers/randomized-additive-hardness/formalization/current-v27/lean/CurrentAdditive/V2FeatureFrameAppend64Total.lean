import CurrentAdditive.V2FeatureFrameAppend64
import CurrentAdditive.V2ItemFrameClock

/-! The row-body V2 item callback with charged clearing of residual append
scratch banks 11 and 14.  No blank-bank hypothesis remains. -/

namespace CurrentAdditive.V2FeatureFrameAppend64Total

open Turing Turing.TM2 EthInapproximability.CurrentPaper BitMachineEncoding
open CurrentAdditive.MinimumRatioContext
open V2ItemFrameCore V2FeatureFrameLayout64 V2ItemFrameClock

def clearSlot (i : Fin 2) : Fin 64 := if i.val = 0 then 11 else 14

theorem clearSlot_injective : Function.Injective clearSlot := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [clearSlot]

abbrev ClearLabel := MachineInvokeClear.Label 2
abbrev ClearControl := MachineInvokeClear.Control

def clearProgram : ClearLabel → TM2.Stmt (fun _ : Fin 64 => Bool)
    ClearLabel ClearControl
  | .clear i => BitMachineClearBank.clearStep (clearSlot i)
      (.clear i) (MachineInvokeClear.nextClear i)
  | .finish => BitMachineClearBank.finishStep id .done
  | .done => .halt

def clearTime (S : Fin 64 → List Bool) : ℕ :=
  (∑ i : Fin 2, (S (clearSlot i)).length) + 4

def cleared (S : Fin 64 → List Bool) :=
  BitMachineClearBank.cleared clearSlot S

theorem clearRun (S : Fin 64 → List Bool) :
    ((advance clearProgram)^[clearTime S])
      (⟨some (MachineInvokeClear.clearLabel 2 0), ((), none), S⟩ :
        TM2.Cfg (fun _ : Fin 64 => Bool) _ _) =
      ⟨none, ((), none), cleared S⟩ := by
  have hr := BitMachineClearBank.clear_bank_run clearProgram id .done
    2 clearSlot clearSlot_injective (MachineInvokeClear.clearLabel 2)
    (by
      intro i
      obtain ⟨h1,h2⟩ := MachineInvokeClear.clearLabel_step 2 i
      rw [h1,h2]
      rfl)
    (by rw [MachineInvokeClear.clearLabel_finish]; rfl) () S
  have hd : advance clearProgram
      (⟨some .done, ((), none), cleared S⟩ :
        TM2.Cfg (fun _ : Fin 64 => Bool) ClearLabel ClearControl) =
      ⟨none, ((), none), cleared S⟩ := rfl
  simp only [clearTime, cleared]
  rw [show (∑ i : Fin 2, (S (clearSlot i)).length) + 4 =
      ((∑ i : Fin 2, (S (clearSlot i)).length) + 2 + 1) + 1 by omega,
    Function.iterate_succ_apply', hr]
  simpa [cleared] using hd

theorem cleared_foreign (S : Fin 64 → List Bool) (j : Fin 64)
    (h11 : j ≠ 11) (h14 : j ≠ 14) : cleared S j = S j := by
  apply BitMachineClearBank.cleared_foreign clearSlot S
  intro i
  fin_cases i
  · simpa [clearSlot] using h11.symm
  · simpa [clearSlot] using h14.symm

theorem cleared_11 (S : Fin 64 → List Bool) : cleared S 11 = [] := by
  exact BitMachineClearBank.cleared_bank clearSlot S 0

theorem cleared_14 (S : Fin 64 → List Bool) : cleared S 14 = [] := by
  exact BitMachineClearBank.cleared_bank clearSlot S 1

theorem inputSize_le (S : Fin 64 → List Bool) (raw : List Bool) :
    inputSize V2FeatureFrameLayout64.slots (cleared S) raw ≤ inputSize V2FeatureFrameLayout64.slots S raw := by
  unfold inputSize
  apply Nat.add_le_add_left
  apply Finset.sum_le_sum
  intro i _
  unfold cleared BitMachineClearBank.cleared
  by_cases h : ∃ j, clearSlot j = clearBank V2FeatureFrameLayout64.slots i
  · simp [h]
  · simp [h]

noncomputable def program := BitMachineRawSequence.program
  clearProgram V2FeatureFrameAppend64.program
  (BitMachineRawSequence.leftLabel (V2ItemFrameCore.start V2FeatureFrameLayout64.slots))
  ((), none) (V2ItemFrameCore.control V2FeatureFrameLayout64.slots, ((), none))

noncomputable def bound (S : Fin 64 → List Bool)
    (raw body : List Bool) : ℕ :=
  clearTime S + coefficient*(inputSize V2FeatureFrameLayout64.slots S raw+1)^2 +
    (4*body.length + 2*(EncodedCommunication.natField raw.length ++ raw).length+7)+2

theorem run (S : Fin 64 → List Bool) (raw body : List Bool)
    (hs : S 36 = raw) (hb : S 9 = body) :
    ∃ t ≤ bound S raw body,
      ∃ (v : GaussV2BodyAppend64.Control) (U : Fin 64 → List Bool),
        ((advance program)^[t])
          (⟨some (BitMachineRawSequence.leftLabel
              (MachineInvokeClear.clearLabel 2 0)),
            (((), none), (V2ItemFrameCore.control V2FeatureFrameLayout64.slots, ((), none))), S⟩ :
            TM2.Cfg (fun _ : Fin 64 => Bool) _ _) =
          ⟨none, (((), none), (V2ItemFrameCore.control V2FeatureFrameLayout64.slots,v)), U⟩ ∧
        U 9 = body ++ (EncodedCommunication.natField raw.length ++ raw) ∧
        U 5 = [] ∧
        U 7 = [] ∧
        (∀ j : Fin 64, j ≠ 5 → j ≠ 9 → j ≠ 11 → j ≠ 14 →
          j ≠ 7 → (∀ i, j ≠ V2FeatureFrameLayout64.slots.machine i) → U j = S j) := by
  let S' := cleared S
  have hs' : S' 36 = raw := by
    exact (cleared_foreign S 36 (by decide) (by decide)).trans hs
  have hb' : S' 9 = body := by
    exact (cleared_foreign S 9 (by decide) (by decide)).trans hb
  obtain ⟨b, hbnd, v, U, hbrun, h9, h5, h7, hforeign⟩ :=
    V2FeatureFrameAppend64.run S' raw body hs' hb' (cleared_11 S) (cleared_14 S)
  obtain ⟨t, ht, hrun⟩ := BitMachineRawSequence.runs
    clearProgram V2FeatureFrameAppend64.program
    (MachineInvokeClear.clearLabel 2 0)
    (BitMachineRawSequence.leftLabel (V2ItemFrameCore.start V2FeatureFrameLayout64.slots))
    ((), none) ((), none)
    (V2ItemFrameCore.control V2FeatureFrameLayout64.slots, ((), none))
    (V2ItemFrameCore.control V2FeatureFrameLayout64.slots, v)
    S S' U (clearTime S) b (clearRun S) hbrun
  have hinput := inputSize_le S raw
  have hpow : (inputSize V2FeatureFrameLayout64.slots S' raw+1)^2 ≤
      (inputSize V2FeatureFrameLayout64.slots S raw+1)^2 := by nlinarith
  have hframe := time_le V2FeatureFrameLayout64.slots S' raw
  have hcost := Nat.mul_le_mul_left coefficient hpow
  have hbudget : t ≤ bound S raw body := by
    unfold bound
    omega
  refine ⟨t, hbudget, v, U, ?_, h9, h5, h7, ?_⟩
  · simpa only [program] using hrun
  · intro j hj5 hj9 hj11 hj14 hj7 hjm
    exact (hforeign j hj5 hj9 hj11 hj14 hj7 hjm).trans
      (cleared_foreign S j hj11 hj14)

#print axioms run

end CurrentAdditive.V2FeatureFrameAppend64Total
