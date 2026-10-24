import Paper2.CodeRowsPreparation
import EthInapproximability.CurrentPaper.BitMachineCopy

/-! The first graph-row branch is a fixed, physical prefix-and-copy compiler.
The nine prefix bits are the append tag followed by the exact serialization
of `emit [false]`. The variable template-row code is copied, not supplied
as an assembled branch. -/

namespace Paper2.CodeRowsArmA

open Turing Turing.TM2.Stmt
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open Paper2.GeneratorCode Paper2.GeneratorSerialization
open Paper2.GeneratorSource Paper2.CodeRowsJoin
open Paper2.CodeRowsPreparation

abbrev FinalBank := Fin 31

def embedPrep : PrepBank ↪ FinalBank where
  toFun i := ⟨i.val, by omega⟩
  inj' := by
    intro a b h
    exact Fin.ext (Fin.mk.inj h)

noncomputable def armBefore (n s q₁ q₂ : Nat) (child : Code) :
    FinalBank → List Bool :=
  BitMachineStackEmbedding.bank embedPrep (fun _ => [])
    (prepAfterArith n s q₁ q₂ child)

def firstArm (q₁ q₂ s : Nat) (child : Code) : Code :=
  .append (.emit [false]) (templateRowCode q₁ q₂ s child)

noncomputable def armAfterCopy (n s q₁ q₂ : Nat) (child : Code) :
    FinalBank → List Bool :=
  Function.update (armBefore n s q₁ q₂ child) 22
    (encodeCode (templateRowCode q₁ q₂ s child))

noncomputable def armAfterA (n s q₁ q₂ : Nat) (child : Code) :
    FinalBank → List Bool :=
  Function.update (armBefore n s q₁ q₂ child) 22
    (encodeCode (firstArm q₁ q₂ s child))

def aCopyIndex : Fin 3 ↪ FinalBank where
  toFun i := ![14,22,30] i
  inj' := by
    intro a b h
    fin_cases a <;> fin_cases b <;> simp_all

theorem arm_template_at (n s q₁ q₂ : Nat) (child : Code) :
    armBefore n s q₁ q₂ child 14 =
      encodeCode (templateRowCode q₁ q₂ s child) := by
  change BitMachineStackEmbedding.bank embedPrep (fun _ => [])
    (prepAfterArith n s q₁ q₂ child) (embedPrep 14) = _
  rw [BitMachineStackEmbedding.bank_at]
  simp only [prepAfterArith, prepAfterTerm,
    Function.update_of_ne (by decide : (14 : PrepBank) ≠ 21),
    Function.update_of_ne (by decide : (14 : PrepBank) ≠ 20),
    Function.update_of_ne (by decide : (14 : PrepBank) ≠ 19)]
  change BitMachineStackEmbedding.bank embedTemplate (prepForeign n)
    (templateAfterAppend s q₁ q₂ child) (embedTemplate 14) = _
  rw [BitMachineStackEmbedding.bank_at]
  exact template_row_output s q₁ q₂ child

theorem arm_outside (n s q₁ q₂ : Nat) (child : Code)
    (i : FinalBank) (hi : 22 ≤ i.val) :
    armBefore n s q₁ q₂ child i = [] := by
  have hnot : ¬ ∃ j : PrepBank, embedPrep j = i := by
    rintro ⟨j,hj⟩
    have hv : j.val = i.val := by
      simpa [embedPrep] using congrArg Fin.val hj
    omega
  rw [armBefore,
    BitMachineStackEmbedding.bank_outside embedPrep
      (fun _ => []) _ i hnot]

theorem arm_initial_bank (n s q₁ q₂ : Nat) (child : Code) :
    BitMachineStackEmbedding.bank aCopyIndex
      (armBefore n s q₁ q₂ child)
      (BitMachineCopy.cfg (some .scan) none
        (encodeCode (templateRowCode q₁ q₂ s child)) [] []).stk =
    armBefore n s q₁ q₂ child := by
  apply BitMachineStackEmbedding.bank_eq_self
  intro i
  fin_cases i
  · change encodeCode (templateRowCode q₁ q₂ s child) =
      armBefore n s q₁ q₂ child 14
    exact (arm_template_at n s q₁ q₂ child).symm
  · change ([] : List Bool) = armBefore n s q₁ q₂ child 22
    exact (arm_outside n s q₁ q₂ child 22 (by decide)).symm
  · change ([] : List Bool) = armBefore n s q₁ q₂ child 30
    exact (arm_outside n s q₁ q₂ child 30 (by decide)).symm

theorem arm_result_bank (n s q₁ q₂ : Nat) (child : Code) :
    BitMachineStackEmbedding.bank aCopyIndex
      (armBefore n s q₁ q₂ child)
      (BitMachineCopy.cfg none none
        (encodeCode (templateRowCode q₁ q₂ s child))
        (encodeCode (templateRowCode q₁ q₂ s child)) []).stk =
    armAfterCopy n s q₁ q₂ child := by
  have hstk :
      (BitMachineCopy.cfg none none
        (encodeCode (templateRowCode q₁ q₂ s child))
        (encodeCode (templateRowCode q₁ q₂ s child)) []).stk =
      Function.update
        (BitMachineCopy.cfg (some .scan) none
          (encodeCode (templateRowCode q₁ q₂ s child)) [] []).stk
        (1 : Fin 3) (encodeCode (templateRowCode q₁ q₂ s child)) := by
    funext i
    fin_cases i <;> rfl
  rw [hstk, BitMachineStackEmbedding.bank_update,
    arm_initial_bank]
  rfl

def copyAProgram : BitMachineCopy.Label →
    TM2.Stmt (fun _ : FinalBank => Bool)
      BitMachineCopy.Label (Option Bool) :=
  fun l => BitMachineStackEmbedding.stackStmt aCopyIndex
    (BitMachineCopy.program l)

theorem copy_a_run (n s q₁ q₂ : Nat) (child : Code) :
    ((advance copyAProgram)^[2*codeSize
      (templateRowCode q₁ q₂ s child)+2])
      (⟨some .scan, none, armBefore n s q₁ q₂ child⟩ :
        TM2.Cfg (fun _ : FinalBank => Bool)
          BitMachineCopy.Label (Option Bool)) =
      ⟨none, none, armAfterCopy n s q₁ q₂ child⟩ := by
  have h := BitMachineStackRun.run aCopyIndex
    (armBefore n s q₁ q₂ child) BitMachineCopy.program
    (BitMachineCopy.cfg (some .scan) none
      (encodeCode (templateRowCode q₁ q₂ s child)) [] [])
    (2*codeSize (templateRowCode q₁ q₂ s child)+2)
  rw [← BitMachineCopy.run,
    ← encodeCode_length (templateRowCode q₁ q₂ s child),
    BitMachineCopy.run_correct none
      (encodeCode (templateRowCode q₁ q₂ s child)) []] at h
  simpa only [copyAProgram, BitMachineStackEmbedding.stackCfg,
    arm_initial_bank, arm_result_bank, List.append_nil,
    encodeCode_length] using h

inductive PrefixLabel where
  | write | accept
  deriving DecidableEq, Fintype

/-- Push in reverse order: `011` (append), then `000100` (emit false). -/
def prefixAProgram : PrefixLabel →
    TM2.Stmt (fun _ : FinalBank => Bool) PrefixLabel Unit
  | .write =>
      push 22 (fun _ => false)
        (push 22 (fun _ => false)
          (push 22 (fun _ => true)
            (push 22 (fun _ => false)
              (push 22 (fun _ => false)
                (push 22 (fun _ => false)
                  (push 22 (fun _ => true)
                    (push 22 (fun _ => true)
                      (push 22 (fun _ => false)
                        (goto (fun _ => .accept))))))))))
  | .accept => halt

theorem prefix_a_run (n s q₁ q₂ : Nat) (child : Code) :
    ((advance prefixAProgram)^[2])
      (⟨some .write, (), armAfterCopy n s q₁ q₂ child⟩ :
        TM2.Cfg (fun _ : FinalBank => Bool) PrefixLabel Unit) =
      ⟨none, (), armAfterA n s q₁ q₂ child⟩ := by
  simp [advance, TM2.step, TM2.stepAux, prefixAProgram,
    armAfterCopy, armAfterA, firstArm, encodeCode, unary,
    Function.update]

def armAProgram :=
  BitMachineRawSequence.program copyAProgram prefixAProgram
    PrefixLabel.write (none : Option Bool) ()

theorem arm_a_run (n s q₁ q₂ : Nat) (child : Code) :
    ∃ t ≤ 2*codeSize (templateRowCode q₁ q₂ s child)+5,
      ((advance armAProgram)^[t])
        (⟨some (BitMachineRawSequence.leftLabel
            BitMachineCopy.Label.scan),
          (none,()), armBefore n s q₁ q₂ child⟩ :
          TM2.Cfg (fun _ : FinalBank => Bool) _ _) =
        ⟨none, (none,()), armAfterA n s q₁ q₂ child⟩ := by
  obtain ⟨t,ht,hr⟩ := BitMachineRawSequence.runs
    copyAProgram prefixAProgram BitMachineCopy.Label.scan
    PrefixLabel.write none none () ()
    (armBefore n s q₁ q₂ child)
    (armAfterCopy n s q₁ q₂ child)
    (armAfterA n s q₁ q₂ child)
    (2*codeSize (templateRowCode q₁ q₂ s child)+2) 2
    (copy_a_run n s q₁ q₂ child)
    (prefix_a_run n s q₁ q₂ child)
  exact ⟨t, by omega, hr⟩

end Paper2.CodeRowsArmA
