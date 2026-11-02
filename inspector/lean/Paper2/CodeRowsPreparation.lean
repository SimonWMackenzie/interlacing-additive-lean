import Paper2.CodeRowsJoin
import EthInapproximability.CurrentPaper.BitMachineRawSequence
import EthInapproximability.CurrentPaper.BitMachineStackRun
import EthInapproximability.CurrentPaper.BitMachineCopy

/-! Physical preparation of the graph-row operands not used by the already
checked template-row controller. Public scalar banks contain delimiter-free
`List.replicate v true`; serialized ticket fields contain terminated
`GeneratorSerialization.unary v`. The transition between them is charged. -/

namespace Paper2.CodeRowsPreparation

open Turing Turing.TM2.Stmt
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open Paper2.GeneratorCode Paper2.GeneratorSerialization
open Paper2.CodeRowsJoin

abbrev PrepBank := Fin 22

def embedTemplate : TemplateBank ↪ PrepBank where
  toFun i := ⟨i.val, by omega⟩
  inj' := by
    intro a b h
    exact Fin.ext (Fin.mk.inj h)

def prepForeign (n : Nat) : PrepBank → List Bool :=
  fun i => if i = 18 then List.replicate n true else []

noncomputable def prepBefore (n s q₁ q₂ : Nat) (child : Code) :
    PrepBank → List Bool :=
  BitMachineStackEmbedding.bank embedTemplate (prepForeign n)
    (templateBefore s q₁ q₂ child)

noncomputable def prepAfterTemplate (n s q₁ q₂ : Nat) (child : Code) :
    PrepBank → List Bool :=
  BitMachineStackEmbedding.bank embedTemplate (prepForeign n)
    (templateAfterAppend s q₁ q₂ child)

noncomputable def prepAfterTerm (n s q₁ q₂ : Nat) (child : Code) :
    PrepBank → List Bool :=
  Function.update (prepAfterTemplate n s q₁ q₂ child)
    (19 : PrepBank) (unary s)

noncomputable def prepAfterArith (n s q₁ q₂ : Nat) (child : Code) :
    PrepBank → List Bool :=
  Function.update
    (Function.update (prepAfterTerm n s q₁ q₂ child)
      (20 : PrepBank) (unary (4*s)))
    (21 : PrepBank) (unary (s-3))

def sCopyIndex : Fin 3 ↪ PrepBank where
  toFun i := ![17,19,6] i
  inj' := by
    intro a b h
    fin_cases a <;> fin_cases b <;> simp_all

def sArithIndex : Fin 4 ↪ PrepBank where
  toFun i := ![19,20,21,6] i
  inj' := by
    intro a b h
    fin_cases a <;> fin_cases b <;> simp_all

inductive TermLabel where
  | write | accept
  deriving DecidableEq, Fintype

def termProgram : TermLabel → TM2.Stmt (fun _ : PrepBank => Bool)
    TermLabel Unit
  | .write => push 19 (fun _ => false) (goto (fun _ => .accept))
  | .accept => halt

noncomputable def prepAfterDelimiter (n s q₁ q₂ : Nat) (child : Code) :
    PrepBank → List Bool :=
  Function.update (prepAfterTemplate n s q₁ q₂ child)
    (19 : PrepBank) [false]

theorem prep_s_at (n s q₁ q₂ : Nat) (child : Code) :
    prepAfterTemplate n s q₁ q₂ child 17 = List.replicate s true := by
  change BitMachineStackEmbedding.bank embedTemplate (prepForeign n)
    (templateAfterAppend s q₁ q₂ child) (embedTemplate 17) = _
  rw [BitMachineStackEmbedding.bank_at]
  exact template_row_retains_s s q₁ q₂ child

theorem prep_scratch_at (n s q₁ q₂ : Nat) (child : Code) :
    prepAfterTemplate n s q₁ q₂ child 6 = [] := by
  change BitMachineStackEmbedding.bank embedTemplate (prepForeign n)
    (templateAfterAppend s q₁ q₂ child) (embedTemplate 6) = _
  rw [BitMachineStackEmbedding.bank_at]
  exact template_row_clears_scratch s q₁ q₂ child

theorem prep_blank19 (n s q₁ q₂ : Nat) (child : Code) :
    prepAfterTemplate n s q₁ q₂ child 19 = [] := by
  have hnot : ¬ ∃ i : TemplateBank, embedTemplate i = (19 : PrepBank) := by
    rintro ⟨i,hi⟩
    have hv : i.val = 19 := by
      simpa [embedTemplate] using congrArg Fin.val hi
    omega
  rw [prepAfterTemplate,
    BitMachineStackEmbedding.bank_outside embedTemplate
      (prepForeign n) _ 19 hnot]
  rfl

theorem delimiter_run (n s q₁ q₂ : Nat) (child : Code) :
    ((advance termProgram)^[2])
      (⟨some .write, (), prepAfterTemplate n s q₁ q₂ child⟩ :
        TM2.Cfg (fun _ : PrepBank => Bool) TermLabel Unit) =
      ⟨none, (), prepAfterDelimiter n s q₁ q₂ child⟩ := by
  simp [advance, TM2.step, TM2.stepAux, termProgram,
    prepAfterDelimiter]
  rw [prep_blank19]

theorem copy_s_initial_bank (n s q₁ q₂ : Nat) (child : Code) :
    BitMachineStackEmbedding.bank sCopyIndex
      (prepAfterDelimiter n s q₁ q₂ child)
      (BitMachineCopy.cfg (some .scan) none
        (List.replicate s true) [false] []).stk =
      prepAfterDelimiter n s q₁ q₂ child := by
  apply BitMachineStackEmbedding.bank_eq_self
  intro i
  fin_cases i
  · change List.replicate s true = prepAfterDelimiter n s q₁ q₂ child 17
    simp [prepAfterDelimiter, prep_s_at]
  · change [false] = prepAfterDelimiter n s q₁ q₂ child 19
    simp [prepAfterDelimiter]
  · change ([] : List Bool) = prepAfterDelimiter n s q₁ q₂ child 6
    simp [prepAfterDelimiter, prep_scratch_at]

theorem copy_s_result_bank (n s q₁ q₂ : Nat) (child : Code) :
    BitMachineStackEmbedding.bank sCopyIndex
      (prepAfterDelimiter n s q₁ q₂ child)
      (BitMachineCopy.cfg none none
        (List.replicate s true) (unary s) []).stk =
      prepAfterTerm n s q₁ q₂ child := by
  have hstk :
      (BitMachineCopy.cfg none none
        (List.replicate s true) (unary s) []).stk =
      Function.update
        (BitMachineCopy.cfg (some .scan) none
          (List.replicate s true) [false] []).stk
        (1 : Fin 3) (unary s) := by
    funext i
    fin_cases i <;> rfl
  rw [hstk, BitMachineStackEmbedding.bank_update,
    copy_s_initial_bank]
  change Function.update
      (Function.update (prepAfterTemplate n s q₁ q₂ child) 19 [false])
      19 (unary s) =
    Function.update (prepAfterTemplate n s q₁ q₂ child) 19 (unary s)
  simp

def copySProgram : BitMachineCopy.Label →
    TM2.Stmt (fun _ : PrepBank => Bool) BitMachineCopy.Label (Option Bool) :=
  fun l => BitMachineStackEmbedding.stackStmt sCopyIndex
    (BitMachineCopy.program l)

theorem copy_s_run (n s q₁ q₂ : Nat) (child : Code) :
    ((advance copySProgram)^[2*s+2])
      (⟨some .scan, none, prepAfterDelimiter n s q₁ q₂ child⟩ :
        TM2.Cfg (fun _ : PrepBank => Bool)
          BitMachineCopy.Label (Option Bool)) =
      ⟨none, none, prepAfterTerm n s q₁ q₂ child⟩ := by
  have h := BitMachineStackRun.run sCopyIndex
    (prepAfterDelimiter n s q₁ q₂ child) BitMachineCopy.program
    (BitMachineCopy.cfg (some .scan) none
      (List.replicate s true) [false] []) (2*s+2)
  have hc := BitMachineCopy.run_correct none (List.replicate s true) [false]
  simp only [List.length_replicate] at hc
  rw [← BitMachineCopy.run, hc] at h
  have hword : List.replicate s true ++ [false] = unary s := rfl
  rw [hword] at h
  simpa only [copySProgram, BitMachineStackEmbedding.stackCfg,
    copy_s_initial_bank, copy_s_result_bank] using h

def termCopyProgram :=
  BitMachineRawSequence.program termProgram copySProgram
    BitMachineCopy.Label.scan () none

theorem term_copy_run (n s q₁ q₂ : Nat) (child : Code) :
    ∃ t ≤ 2*s+5,
      ((advance termCopyProgram)^[t])
        (⟨some (BitMachineRawSequence.leftLabel TermLabel.write),
          ((),none), prepAfterTemplate n s q₁ q₂ child⟩ :
          TM2.Cfg (fun _ : PrepBank => Bool) _ _) =
        ⟨none, ((),none), prepAfterTerm n s q₁ q₂ child⟩ := by
  obtain ⟨t,ht,hr⟩ := BitMachineRawSequence.runs
    termProgram copySProgram TermLabel.write BitMachineCopy.Label.scan
    () () none none
    (prepAfterTemplate n s q₁ q₂ child)
    (prepAfterDelimiter n s q₁ q₂ child)
    (prepAfterTerm n s q₁ q₂ child)
    2 (2*s+2) (delimiter_run n s q₁ q₂ child)
    (copy_s_run n s q₁ q₂ child)
  exact ⟨t, by omega, hr⟩

private theorem prep_blank20 (n s q₁ q₂ : Nat) (child : Code) :
    prepAfterTerm n s q₁ q₂ child 20 = [] := by
  have hnot : ¬ ∃ i : TemplateBank, embedTemplate i = (20 : PrepBank) := by
    rintro ⟨i,hi⟩
    have hv : i.val = 20 := by
      simpa [embedTemplate] using congrArg Fin.val hi
    omega
  simp only [prepAfterTerm, Function.update_of_ne
    (by decide : (20 : PrepBank) ≠ 19)]
  rw [prepAfterTemplate,
    BitMachineStackEmbedding.bank_outside embedTemplate
      (prepForeign n) _ 20 hnot]
  rfl

private theorem prep_blank21 (n s q₁ q₂ : Nat) (child : Code) :
    prepAfterTerm n s q₁ q₂ child 21 = [] := by
  have hnot : ¬ ∃ i : TemplateBank, embedTemplate i = (21 : PrepBank) := by
    rintro ⟨i,hi⟩
    have hv : i.val = 21 := by
      simpa [embedTemplate] using congrArg Fin.val hi
    omega
  simp only [prepAfterTerm, Function.update_of_ne
    (by decide : (21 : PrepBank) ≠ 19)]
  rw [prepAfterTemplate,
    BitMachineStackEmbedding.bank_outside embedTemplate
      (prepForeign n) _ 21 hnot]
  rfl

theorem arith_initial_bank (n s q₁ q₂ : Nat) (child : Code) :
    BitMachineStackEmbedding.bank sArithIndex
      (prepAfterTerm n s q₁ q₂ child)
      (CodeRowsCompiler.arithCfg (some .init) none
        (unary s) [] [] []).stk =
      prepAfterTerm n s q₁ q₂ child := by
  apply BitMachineStackEmbedding.bank_eq_self
  intro i
  fin_cases i
  · change unary s = prepAfterTerm n s q₁ q₂ child 19
    simp [prepAfterTerm]
  · change ([] : List Bool) = prepAfterTerm n s q₁ q₂ child 20
    exact (prep_blank20 n s q₁ q₂ child).symm
  · change ([] : List Bool) = prepAfterTerm n s q₁ q₂ child 21
    exact (prep_blank21 n s q₁ q₂ child).symm
  · change ([] : List Bool) = prepAfterTerm n s q₁ q₂ child 6
    simp [prepAfterTerm, prep_scratch_at]

theorem arith_result_bank (n s q₁ q₂ : Nat) (child : Code) :
    BitMachineStackEmbedding.bank sArithIndex
      (prepAfterTerm n s q₁ q₂ child)
      (CodeRowsCompiler.arithCfg none none
        (unary s) (unary (4*s)) (unary (s-3)) []).stk =
      prepAfterArith n s q₁ q₂ child := by
  have hstk :
      (CodeRowsCompiler.arithCfg none none
        (unary s) (unary (4*s)) (unary (s-3)) []).stk =
      Function.update
        (Function.update
          (CodeRowsCompiler.arithCfg (some .init) none
            (unary s) [] [] []).stk
          (1 : Fin 4) (unary (4*s)))
        (2 : Fin 4) (unary (s-3)) := by
    funext i
    fin_cases i <;> rfl
  rw [hstk, BitMachineStackEmbedding.bank_update,
    BitMachineStackEmbedding.bank_update, arith_initial_bank]
  rfl

def arithEmbeddedProgram : CodeRowsCompiler.ArithLabel →
    TM2.Stmt (fun _ : PrepBank => Bool)
      CodeRowsCompiler.ArithLabel CodeRowsCompiler.ArithControl :=
  fun l => BitMachineStackEmbedding.stackStmt sArithIndex
    (CodeRowsCompiler.arithProgram l)

theorem arith_embedded_run (n s q₁ q₂ : Nat) (child : Code)
    (hs : 3 ≤ s) :
    ((advance arithEmbeddedProgram)^[2*s+4])
      (⟨some .init, none, prepAfterTerm n s q₁ q₂ child⟩ :
        TM2.Cfg (fun _ : PrepBank => Bool)
          CodeRowsCompiler.ArithLabel CodeRowsCompiler.ArithControl) =
      ⟨none, none, prepAfterArith n s q₁ q₂ child⟩ := by
  have h := BitMachineStackRun.run sArithIndex
    (prepAfterTerm n s q₁ q₂ child)
    CodeRowsCompiler.arithProgram
    (CodeRowsCompiler.arithCfg (some .init) none
      (unary s) [] [] []) (2*s+4)
  rw [← CodeRowsCompiler.arithRun,
    CodeRowsCompiler.arith_run s hs] at h
  simpa only [arithEmbeddedProgram, BitMachineStackEmbedding.stackCfg,
    arith_initial_bank, arith_result_bank] using h

def scalarPrepProgram :=
  BitMachineRawSequence.program termCopyProgram arithEmbeddedProgram
    CodeRowsCompiler.ArithLabel.init
    (((),none) : BitMachineRawSequence.Control Unit (Option Bool))
    (none : CodeRowsCompiler.ArithControl)

theorem scalar_prep_run (n s q₁ q₂ : Nat) (child : Code)
    (hs : 3 ≤ s) :
    ∃ t ≤ (2*s+5) + (2*s+4) + 1,
      ((advance scalarPrepProgram)^[t])
        (⟨some (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel TermLabel.write)),
          (((),none),none), prepAfterTemplate n s q₁ q₂ child⟩ :
          TM2.Cfg (fun _ : PrepBank => Bool) _ _) =
        ⟨none, (((),none),none), prepAfterArith n s q₁ q₂ child⟩ := by
  obtain ⟨ta,hta,ha⟩ := term_copy_run n s q₁ q₂ child
  obtain ⟨t,ht,hr⟩ := BitMachineRawSequence.runs
    termCopyProgram arithEmbeddedProgram
    (BitMachineRawSequence.leftLabel TermLabel.write)
    CodeRowsCompiler.ArithLabel.init
    ((),none) ((),none) none none
    (prepAfterTemplate n s q₁ q₂ child)
    (prepAfterTerm n s q₁ q₂ child)
    (prepAfterArith n s q₁ q₂ child) ta (2*s+4)
    ha (arith_embedded_run n s q₁ q₂ child hs)
  exact ⟨t, by omega, hr⟩

abbrev TemplateLabel :=
  BitMachineRawSequence.Label
    (BitMachineRawSequence.Label CoreLabel CodeAtomCountInput.Label)
    CodeConstructorMachine.Label

abbrev TemplateControl :=
  BitMachineRawSequence.Control
    (BitMachineRawSequence.Control CoreControl CodeAtomCountInput.Control)
    CodeConstructorMachine.Control

def templateStart : TemplateLabel :=
  BitMachineRawSequence.leftLabel
    (BitMachineRawSequence.leftLabel coreStart)

def templateControl : TemplateControl := (coreTicketControl,none)

def liftedTemplateProgram :=
  fun l => BitMachineStackEmbedding.stackStmt embedTemplate
    (templateRowProgram l)

theorem lifted_template_run (n s q₁ q₂ : Nat) (child : Code) :
    ∃ t ≤ templateRowClock s q₁ q₂ child,
      ((advance liftedTemplateProgram)^[t])
        (⟨some templateStart, templateControl,
          prepBefore n s q₁ q₂ child⟩ :
          TM2.Cfg (fun _ : PrepBank => Bool)
            TemplateLabel TemplateControl) =
        ⟨none, templateControl,
          prepAfterTemplate n s q₁ q₂ child⟩ := by
  obtain ⟨t,ht,hr⟩ := template_row_run s q₁ q₂ child
  have h := BitMachineStackRun.run embedTemplate (prepForeign n)
    templateRowProgram
    (⟨some templateStart, templateControl,
      templateBefore s q₁ q₂ child⟩ :
      TM2.Cfg (fun _ : TemplateBank => Bool)
        TemplateLabel TemplateControl) t
  simp only [templateStart, templateControl] at h
  rw [hr] at h
  exact ⟨t, ht, by simpa [liftedTemplateProgram,
    BitMachineStackEmbedding.stackCfg, prepBefore,
    prepAfterTemplate, templateStart, templateControl] using h⟩

abbrev ScalarPrepLabel :=
  BitMachineRawSequence.Label
    (BitMachineRawSequence.Label TermLabel BitMachineCopy.Label)
    CodeRowsCompiler.ArithLabel

abbrev ScalarPrepControl :=
  BitMachineRawSequence.Control
    (BitMachineRawSequence.Control Unit (Option Bool))
    CodeRowsCompiler.ArithControl

def scalarStart : ScalarPrepLabel :=
  BitMachineRawSequence.leftLabel
    (BitMachineRawSequence.leftLabel TermLabel.write)

def scalarControl : ScalarPrepControl := (((),none),none)

def templateThenScalarsProgram :=
  BitMachineRawSequence.program liftedTemplateProgram scalarPrepProgram
    scalarStart templateControl scalarControl

theorem template_then_scalars_run (n s q₁ q₂ : Nat) (child : Code)
    (hs : 3 ≤ s) :
    ∃ t ≤ templateRowClock s q₁ q₂ child +
      ((2*s+5)+(2*s+4)+1)+1,
      ((advance templateThenScalarsProgram)^[t])
        (⟨some (BitMachineRawSequence.leftLabel templateStart),
          (templateControl,scalarControl),
          prepBefore n s q₁ q₂ child⟩ :
          TM2.Cfg (fun _ : PrepBank => Bool) _ _) =
        ⟨none, (templateControl,scalarControl),
          prepAfterArith n s q₁ q₂ child⟩ := by
  obtain ⟨ta,hta,ha⟩ := lifted_template_run n s q₁ q₂ child
  obtain ⟨tb,htb,hb⟩ := scalar_prep_run n s q₁ q₂ child hs
  obtain ⟨t,ht,hr⟩ := BitMachineRawSequence.runs
    liftedTemplateProgram scalarPrepProgram templateStart scalarStart
    templateControl templateControl scalarControl scalarControl
    (prepBefore n s q₁ q₂ child)
    (prepAfterTemplate n s q₁ q₂ child)
    (prepAfterArith n s q₁ q₂ child) ta tb ha hb
  exact ⟨t, by omega, hr⟩

end Paper2.CodeRowsPreparation
