import Paper2.CodeRowsArmA
import Paper2.CodeRowArms

set_option maxHeartbeats 1000000

/-! Embed the independently checked two-arm physical compiler into the
retained graph-row operand bank. Its `true^n` count input is not confused with
the terminated unary code fields on its other two inputs. -/

namespace Paper2.CodeRowsArmsEmbed

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open Paper2.GeneratorCode Paper2.GeneratorSerialization
open Paper2.GeneratorSource Paper2.CodeRowsJoin
open Paper2.CodeRowsPreparation Paper2.CodeRowsArmA

def armsIndex : CodeRowArms.Stack ↪ FinalBank where
  toFun i := ![18,20,21,2,23,24,6] i
  inj' := by
    intro a b h
    fin_cases a <;> fin_cases b <;> simp_all

noncomputable def afterBoth (n s q₁ q₂ : Nat) (child : Code) :
    FinalBank → List Bool :=
  Function.update
    (Function.update (armAfterA n s q₁ q₂ child) 23
      (encodeCode (CodeRowArms.vertexArm n s child)))
    24 (encodeCode (CodeRowArms.auxiliaryArm s child))

theorem arm_inputs_18 (n s q₁ q₂ : Nat) (child : Code) :
    armAfterA n s q₁ q₂ child 18 = List.replicate n true := by
  simp only [armAfterA, Function.update_of_ne
    (by decide : (18 : FinalBank) ≠ 22)]
  change BitMachineStackEmbedding.bank embedPrep (fun _ => [])
    (prepAfterArith n s q₁ q₂ child) (embedPrep 18) = _
  rw [BitMachineStackEmbedding.bank_at]
  simp only [prepAfterArith, prepAfterTerm,
    Function.update_of_ne (by decide : (18 : PrepBank) ≠ 21),
    Function.update_of_ne (by decide : (18 : PrepBank) ≠ 20),
    Function.update_of_ne (by decide : (18 : PrepBank) ≠ 19)]
  have hnot : ¬ ∃ i : TemplateBank, embedTemplate i = (18 : PrepBank) := by
    rintro ⟨i,hi⟩
    have hv : i.val = 18 := by
      simpa [embedTemplate] using congrArg Fin.val hi
    omega
  rw [prepAfterTemplate,
    BitMachineStackEmbedding.bank_outside embedTemplate
      (prepForeign n) _ 18 hnot]
  rfl

theorem arm_inputs_20 (n s q₁ q₂ : Nat) (child : Code) :
    armAfterA n s q₁ q₂ child 20 = unary (4*s) := by
  simp only [armAfterA, Function.update_of_ne
    (by decide : (20 : FinalBank) ≠ 22)]
  change BitMachineStackEmbedding.bank embedPrep (fun _ => [])
    (prepAfterArith n s q₁ q₂ child) (embedPrep 20) = _
  rw [BitMachineStackEmbedding.bank_at]
  simp [prepAfterArith]

theorem arm_inputs_21 (n s q₁ q₂ : Nat) (child : Code) :
    armAfterA n s q₁ q₂ child 21 = unary (s-3) := by
  simp only [armAfterA, Function.update_of_ne
    (by decide : (21 : FinalBank) ≠ 22)]
  change BitMachineStackEmbedding.bank embedPrep (fun _ => [])
    (prepAfterArith n s q₁ q₂ child) (embedPrep 21) = _
  rw [BitMachineStackEmbedding.bank_at]
  simp [prepAfterArith]

theorem arm_inputs_2 (n s q₁ q₂ : Nat) (child : Code) :
    armAfterA n s q₁ q₂ child 2 = encodeCode child := by
  simp only [armAfterA, Function.update_of_ne
    (by decide : (2 : FinalBank) ≠ 22)]
  change BitMachineStackEmbedding.bank embedPrep (fun _ => [])
    (prepAfterArith n s q₁ q₂ child) (embedPrep 2) = _
  rw [BitMachineStackEmbedding.bank_at]
  simp only [prepAfterArith, prepAfterTerm,
    Function.update_of_ne (by decide : (2 : PrepBank) ≠ 21),
    Function.update_of_ne (by decide : (2 : PrepBank) ≠ 20),
    Function.update_of_ne (by decide : (2 : PrepBank) ≠ 19)]
  change BitMachineStackEmbedding.bank embedTemplate (prepForeign n)
    (templateAfterAppend s q₁ q₂ child) (embedTemplate 2) = _
  rw [BitMachineStackEmbedding.bank_at]
  exact template_row_retains_child s q₁ q₂ child

theorem arm_inputs_6 (n s q₁ q₂ : Nat) (child : Code) :
    armAfterA n s q₁ q₂ child 6 = [] := by
  simp only [armAfterA, Function.update_of_ne
    (by decide : (6 : FinalBank) ≠ 22)]
  change BitMachineStackEmbedding.bank embedPrep (fun _ => [])
    (prepAfterArith n s q₁ q₂ child) (embedPrep 6) = _
  rw [BitMachineStackEmbedding.bank_at]
  simp only [prepAfterArith, prepAfterTerm,
    Function.update_of_ne (by decide : (6 : PrepBank) ≠ 21),
    Function.update_of_ne (by decide : (6 : PrepBank) ≠ 20),
    Function.update_of_ne (by decide : (6 : PrepBank) ≠ 19)]
  exact prep_scratch_at n s q₁ q₂ child

theorem arm_inputs_23 (n s q₁ q₂ : Nat) (child : Code) :
    armAfterA n s q₁ q₂ child 23 = [] := by
  simp [armAfterA, arm_outside n s q₁ q₂ child 23 (by decide)]

theorem arm_inputs_24 (n s q₁ q₂ : Nat) (child : Code) :
    armAfterA n s q₁ q₂ child 24 = [] := by
  simp [armAfterA, arm_outside n s q₁ q₂ child 24 (by decide)]

theorem arms_initial_bank (n s q₁ q₂ : Nat) (child : Code) :
    BitMachineStackEmbedding.bank armsIndex
      (armAfterA n s q₁ q₂ child)
      (CodeRowArms.initial n s child).stk =
    armAfterA n s q₁ q₂ child := by
  apply BitMachineStackEmbedding.bank_eq_self
  intro i
  fin_cases i
  · exact (arm_inputs_18 n s q₁ q₂ child).symm
  · exact (arm_inputs_20 n s q₁ q₂ child).symm
  · exact (arm_inputs_21 n s q₁ q₂ child).symm
  · exact (arm_inputs_2 n s q₁ q₂ child).symm
  · exact (arm_inputs_23 n s q₁ q₂ child).symm
  · exact (arm_inputs_24 n s q₁ q₂ child).symm
  · exact (arm_inputs_6 n s q₁ q₂ child).symm

theorem arms_result_bank (n s q₁ q₂ : Nat) (child : Code) :
    BitMachineStackEmbedding.bank armsIndex
      (armAfterA n s q₁ q₂ child)
      (CodeRowArms.final n s child).stk =
    afterBoth n s q₁ q₂ child := by
  have hstk : (CodeRowArms.final n s child).stk =
      Function.update
        (Function.update (CodeRowArms.initial n s child).stk
          (4 : CodeRowArms.Stack)
          (encodeCode (CodeRowArms.vertexArm n s child)))
        (5 : CodeRowArms.Stack)
        (encodeCode (CodeRowArms.auxiliaryArm s child)) := by
    funext i
    fin_cases i <;> rfl
  rw [hstk, BitMachineStackEmbedding.bank_update,
    BitMachineStackEmbedding.bank_update, arms_initial_bank]
  rfl

def embeddedArmsProgram : CodeRowArms.Label →
    TM2.Stmt (fun _ : FinalBank => Bool)
      CodeRowArms.Label CodeRowArms.Control :=
  fun l => BitMachineStackEmbedding.stackStmt armsIndex
    (CodeRowArms.program l)

theorem embedded_arms_run (n s q₁ q₂ : Nat) (child : Code) :
    ((advance embeddedArmsProgram)^[CodeRowArms.clock n s child])
      (⟨some .childCopy, none, armAfterA n s q₁ q₂ child⟩ :
        TM2.Cfg (fun _ : FinalBank => Bool)
          CodeRowArms.Label CodeRowArms.Control) =
      ⟨none, none, afterBoth n s q₁ q₂ child⟩ := by
  have h := BitMachineStackRun.run armsIndex
    (armAfterA n s q₁ q₂ child)
    CodeRowArms.program (CodeRowArms.initial n s child)
    (CodeRowArms.clock n s child)
  rw [← CodeRowArms.run, CodeRowArms.run_exact n s child] at h
  simpa only [embeddedArmsProgram,
    BitMachineStackEmbedding.stackCfg,
    arms_initial_bank, arms_result_bank] using h

end Paper2.CodeRowsArmsEmbed
