import CurrentAdditive.FeatureCountAppend96
import EthInapproximability.CurrentPaper.BitMachineClearBank
import EthInapproximability.CurrentPaper.BitMachineRawSequence

/-! Literal clear-and-copy primitives for moving the finished inner body
from bank 41 into the outer accumulator bank 9. -/

namespace CurrentAdditive.FeatureOutputTransfer96

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open Turing

abbrev Stack := Fin 96

inductive ClearLabel where
  | scan | done
  deriving DecidableEq, Fintype

def clearProgram : ClearLabel →
    TM2.Stmt (fun _ : Stack => Bool) ClearLabel (Unit × Option Bool)
  | .scan => BitMachineClearBank.clearStep 9 .scan .done
  | .done => .halt

def clearRun (t : Nat)
    (S : Stack → List Bool) :=
  ((advance clearProgram)^[t])
    (⟨some .scan, ((),none), S⟩ :
      TM2.Cfg (fun _ : Stack => Bool) ClearLabel (Unit × Option Bool))

theorem clear_output (S : Stack → List Bool) :
    clearRun ((S 9).length+2) S =
      ⟨none, ((),none), Function.update S 9 []⟩ := by
  have h := BitMachineClearBank.clear_one_run clearProgram
    (9 : Stack) .scan .done rfl () S
  unfold clearRun
  rw [show (S 9).length+2 = ((S 9).length+1)+1 by omega,
    Function.iterate_succ_apply', h]
  rfl

def copySlot : Fin 3 ↪ Stack where
  toFun
    | 0 => 41
    | 1 => 9
    | _ => 16
  inj' := by
    intro a b h
    fin_cases a <;> fin_cases b <;> simp_all

def copyProgram (l : BitMachineCopy.Label) :
    TM2.Stmt (fun _ : Stack => Bool) BitMachineCopy.Label
      (Option Bool) :=
  BitMachineStackEmbedding.stmt copySlot id id id none
    (BitMachineCopy.program l)

def copyRun (t : Nat)
    (c : TM2.Cfg (fun _ : Stack => Bool)
      BitMachineCopy.Label (Option Bool)) :=
  ((advance copyProgram)^[t]) c

noncomputable def copyStart (foreign : Stack → List Bool)
    (output : List Bool) :=
  BitMachineStackEmbedding.cfg copySlot foreign id id none
    (BitMachineCopy.cfg (some .scan) none output [] [])

noncomputable def copyFinish (foreign : Stack → List Bool)
    (output : List Bool) :=
  BitMachineStackEmbedding.cfg copySlot foreign id id none
    (BitMachineCopy.cfg none none output output [])

theorem copy_output (foreign : Stack → List Bool)
    (output : List Bool) :
    ∃ t ≤ 2*output.length+2,
      copyRun t (copyStart foreign output) =
        copyFinish foreign output := by
  have hlocal := BitMachineCopy.run_correct none output ([] : List Bool)
  have hhalt :
      (((advance BitMachineCopy.program)^[2*output.length+2])
        (BitMachineCopy.cfg (some .scan) none output [] [])).l = none := by
    rw [← BitMachineCopy.run, hlocal]
    rfl
  obtain ⟨t, ht, he⟩ := BitMachineStackEmbedding.outputs
    copySlot foreign id id id (by intro; rfl) none
    BitMachineCopy.program copyProgram (by intro; rfl)
    (BitMachineCopy.cfg (some .scan) none output [] [])
    (2*output.length+2) hhalt
  refine ⟨t, ht, ?_⟩
  rw [← BitMachineCopy.run, hlocal] at he
  simpa only [copyRun, copyStart, copyFinish,
    List.append_nil] using he

theorem copy_output_bank9 (foreign : Stack → List Bool)
    (output : List Bool) :
    (copyFinish foreign output).stk 9 = output := by
  exact BitMachineStackEmbedding.bank_at copySlot foreign
    (BitMachineCopy.cfg none none output output []).stk 1

theorem copy_preserves_bank41 (foreign : Stack → List Bool)
    (output : List Bool) :
    (copyFinish foreign output).stk 41 = output := by
  exact BitMachineStackEmbedding.bank_at copySlot foreign
    (BitMachineCopy.cfg none none output output []).stk 0

theorem copy_foreign (foreign : Stack → List Bool)
    (output : List Bool) (k : Stack)
    (hk41 : k ≠ 41) (hk9 : k ≠ 9) (hk16 : k ≠ 16) :
    (copyFinish foreign output).stk k = foreign k := by
  apply BitMachineStackEmbedding.bank_outside
  rintro ⟨i, hi⟩
  fin_cases i <;> simp [copySlot] at hi <;> simp_all

theorem copyStart_eq (S : Stack → List Bool)
    (output : List Bool)
    (h41 : S 41 = output) (h9 : S 9 = [])
    (h16 : S 16 = []) :
    copyStart S output =
      (⟨some .scan, none, S⟩ :
        TM2.Cfg (fun _ : Stack => Bool) BitMachineCopy.Label
          (Option Bool)) := by
  change (⟨some .scan, none,
      BitMachineStackEmbedding.bank copySlot S
        (BitMachineCopy.stackContents output [] [])⟩ :
      TM2.Cfg (fun _ : Stack => Bool) BitMachineCopy.Label
        (Option Bool)) = ⟨some .scan, none, S⟩
  congr 1
  · change BitMachineStackEmbedding.bank copySlot S
        (BitMachineCopy.stackContents output [] []) = S
    have hlocal : BitMachineCopy.stackContents output [] [] =
        fun k => S (copySlot k) := by
      funext k
      fin_cases k <;>
        simp [BitMachineCopy.stackContents, copySlot, h41, h9, h16]
    rw [hlocal]
    exact BitMachineStackEmbedding.bank_restrict copySlot S

noncomputable def transferProgram := BitMachineRawSequence.program
  clearProgram copyProgram BitMachineCopy.Label.scan
  (((), none) : Unit × Option Bool) (none : Option Bool)

theorem physical_transfer (S : Stack → List Bool)
    (output : List Bool)
    (h41 : S 41 = output) (h16 : S 16 = []) :
    ∃ t ≤ ((S 9).length+2) + (2*output.length+2) + 1,
      let z := ((advance transferProgram)^[t])
        (⟨some (BitMachineRawSequence.leftLabel ClearLabel.scan),
          (((),none),none), S⟩ :
          TM2.Cfg (fun _ : Stack => Bool) _ _)
      z.l = none ∧ z.stk 9 = output ∧ z.stk 12 = S 12 ∧
      z.stk 41 = output ∧
      (∀ k : Stack, k.val < 32 → k ≠ 9 → k ≠ 16 →
        z.stk k = S k) := by
  let U := Function.update S (9 : Stack) []
  have hclear := clear_output S
  have h41U : U 41 = output := by simpa [U] using h41
  have h9U : U 9 = [] := by simp [U]
  have h16U : U 16 = [] := by simpa [U] using h16
  obtain ⟨b, hb, hcopy⟩ := copy_output U output
  have hstart := copyStart_eq U output h41U h9U h16U
  rw [hstart] at hcopy
  change copyRun b ⟨some .scan, none, U⟩ =
    ⟨none, none, (copyFinish U output).stk⟩ at hcopy
  obtain ⟨t, ht, hseq⟩ := BitMachineRawSequence.runs
    clearProgram copyProgram ClearLabel.scan BitMachineCopy.Label.scan
    (((),none) : Unit × Option Bool) (((),none) : Unit × Option Bool)
    (none : Option Bool) (none : Option Bool)
    S U (copyFinish U output).stk ((S 9).length+2) b
    (by simpa only [clearRun, U] using hclear)
    (by simpa only [copyRun] using hcopy)
  have hseq' :
      ((advance transferProgram)^[t])
        (⟨some (BitMachineRawSequence.leftLabel ClearLabel.scan),
          (((),none),none), S⟩ :
          TM2.Cfg (fun _ : Stack => Bool) _ _) =
      ⟨none, (((),none),none), (copyFinish U output).stk⟩ := by
    simpa only [transferProgram] using hseq
  refine ⟨t, by omega, ?_, ?_, ?_, ?_, ?_⟩
  · exact congrArg TM2.Cfg.l hseq'
  · have h := congrArg (fun z => z.stk (9 : Stack)) hseq'
    exact h.trans (copy_output_bank9 U output)
  · have h := congrArg (fun z => z.stk (12 : Stack)) hseq'
    exact (h.trans (copy_foreign U output 12 (by decide)
      (by decide) (by decide))).trans (by simp [U])
  · have h := congrArg (fun z => z.stk (41 : Stack)) hseq'
    exact h.trans (copy_preserves_bank41 U output)
  · intro k hk hk9 hk16
    have h := congrArg (fun z => z.stk k) hseq'
    exact (h.trans (copy_foreign U output k
      (by intro he; have hv := congrArg Fin.val he; omega)
      hk9 hk16)).trans
      (by simp [U, hk9])

#print axioms clear_output
#print axioms copy_output
#print axioms copy_output_bank9
#print axioms copy_preserves_bank41
#print axioms copy_foreign
#print axioms copyStart_eq
#print axioms physical_transfer

end CurrentAdditive.FeatureOutputTransfer96
