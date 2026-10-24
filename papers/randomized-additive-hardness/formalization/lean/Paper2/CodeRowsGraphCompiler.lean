import Paper2.CodeRowsArmsEmbed
import Paper2.CodeRowsBranchAssembly

/-! A single fixed TM2 controller for the actual production graph-rows
syntax. Initial operands are exactly four delimiter-free count cells and the
serialized recursive child. Every other word is built by preceding physical
phases; the output is the literal `encodeCode (graphRowsCode ...)`. -/

set_option maxHeartbeats 1000000

namespace Paper2.CodeRowsGraphCompiler

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open Paper2.GeneratorCode Paper2.GeneratorSerialization
open Paper2.GeneratorSource Paper2.CodeRowsJoin
open Paper2.CodeRowsPreparation Paper2.CodeRowsArmA
open Paper2.CodeRowsArmsEmbed Paper2.CodeRowsBranchAssembly
open Paper2.CodeRowsLiteralPrefix (branchPrefix)

abbrev PrepLabel :=
  BitMachineRawSequence.Label TemplateLabel ScalarPrepLabel
abbrev PrepControl :=
  BitMachineRawSequence.Control TemplateControl ScalarPrepControl

noncomputable def initialBank (n s q₁ q₂ : Nat) (child : Code) :
    FinalBank → List Bool :=
  BitMachineStackEmbedding.bank embedPrep (fun _ => [])
    (prepBefore n s q₁ q₂ child)

theorem initial_n (n s q₁ q₂ : Nat) (child : Code) :
    initialBank n s q₁ q₂ child 18 = List.replicate n true := by
  change BitMachineStackEmbedding.bank embedPrep (fun _ => [])
    (prepBefore n s q₁ q₂ child) (embedPrep 18) = _
  rw [BitMachineStackEmbedding.bank_at]
  have hnot : ¬ ∃ i : TemplateBank, embedTemplate i = (18 : PrepBank) := by
    rintro ⟨i,hi⟩
    have hv : i.val = 18 := by
      simpa [embedTemplate] using congrArg Fin.val hi
    omega
  rw [prepBefore, BitMachineStackEmbedding.bank_outside
    embedTemplate (prepForeign n) _ 18 hnot]
  rfl

theorem initial_s (n s q₁ q₂ : Nat) (child : Code) :
    initialBank n s q₁ q₂ child 17 = List.replicate s true := by
  change BitMachineStackEmbedding.bank embedPrep (fun _ => [])
    (prepBefore n s q₁ q₂ child) (embedPrep 17) = _
  rw [BitMachineStackEmbedding.bank_at]
  change BitMachineStackEmbedding.bank embedTemplate (prepForeign n)
    (templateBefore s q₁ q₂ child) (embedTemplate 17) = _
  rw [BitMachineStackEmbedding.bank_at]
  have hnot : ¬ ∃ i : TicketBank, embedTicketBank i = (17 : TemplateBank) := by
    rintro ⟨i,hi⟩
    have hv : i.val = 17 := by
      simpa [embedTicketBank] using congrArg Fin.val hi
    omega
  rw [templateBefore, BitMachineStackEmbedding.bank_outside
    embedTicketBank (templateForeign s) _ 17 hnot]
  rfl

theorem initial_q₁ (n s q₁ q₂ : Nat) (child : Code) :
    initialBank n s q₁ q₂ child 16 = List.replicate q₁ true := by
  change BitMachineStackEmbedding.bank embedPrep (fun _ => [])
    (prepBefore n s q₁ q₂ child) (embedPrep 16) = _
  rw [BitMachineStackEmbedding.bank_at]
  change BitMachineStackEmbedding.bank embedTemplate (prepForeign n)
    (templateBefore s q₁ q₂ child) (embedTemplate 16) = _
  rw [BitMachineStackEmbedding.bank_at]
  change BitMachineStackEmbedding.bank embedTicketBank (templateForeign s)
    (ticketBefore q₁ q₂ child) (embedTicketBank 16) = _
  rw [BitMachineStackEmbedding.bank_at]
  have hnot : ¬ ∃ i : Bank, embedOld i = (16 : TicketBank) := by
    rintro ⟨i,hi⟩
    have hv : i.val = 16 := by
      simpa [embedOld] using congrArg Fin.val hi
    omega
  rw [ticketBefore, BitMachineStackEmbedding.bank_outside
    embedOld (ticketForeign q₁) _ 16 hnot]
  rfl

theorem initial_q₂ (n s q₁ q₂ : Nat) (child : Code) :
    initialBank n s q₁ q₂ child 12 = List.replicate q₂ true := by
  change BitMachineStackEmbedding.bank embedPrep (fun _ => [])
    (prepBefore n s q₁ q₂ child) (embedPrep 12) = _
  rw [BitMachineStackEmbedding.bank_at]
  change BitMachineStackEmbedding.bank embedTemplate (prepForeign n)
    (templateBefore s q₁ q₂ child) (embedTemplate 12) = _
  rw [BitMachineStackEmbedding.bank_at]
  change BitMachineStackEmbedding.bank embedTicketBank (templateForeign s)
    (ticketBefore q₁ q₂ child) (embedTicketBank 12) = _
  rw [BitMachineStackEmbedding.bank_at]
  change BitMachineStackEmbedding.bank embedOld (ticketForeign q₁)
    (Function.update (publicBase q₂ (.ticket q₁) child) 1 [])
    (embedOld 12) = _
  rw [BitMachineStackEmbedding.bank_at]
  simp [publicBase, innerBase]

theorem initial_child (n s q₁ q₂ : Nat) (child : Code) :
    initialBank n s q₁ q₂ child 2 = encodeCode child := by
  change BitMachineStackEmbedding.bank embedPrep (fun _ => [])
    (prepBefore n s q₁ q₂ child) (embedPrep 2) = _
  rw [BitMachineStackEmbedding.bank_at]
  change BitMachineStackEmbedding.bank embedTemplate (prepForeign n)
    (templateBefore s q₁ q₂ child) (embedTemplate 2) = _
  rw [BitMachineStackEmbedding.bank_at]
  change BitMachineStackEmbedding.bank embedTicketBank (templateForeign s)
    (ticketBefore q₁ q₂ child) (embedTicketBank 2) = _
  rw [BitMachineStackEmbedding.bank_at]
  change BitMachineStackEmbedding.bank embedOld (ticketForeign q₁)
    (Function.update (publicBase q₂ (.ticket q₁) child) 1 [])
    (embedOld 2) = _
  rw [BitMachineStackEmbedding.bank_at]
  simp [publicBase, innerBase]

theorem initial_blank_high (n s q₁ q₂ : Nat) (child : Code)
    (i : FinalBank) (hi : 22 ≤ i.val) :
    initialBank n s q₁ q₂ child i = [] := by
  have hnot : ¬ ∃ j : PrepBank, embedPrep j = i := by
    rintro ⟨j,hj⟩
    have hv : j.val = i.val := by
      simpa [embedPrep] using congrArg Fin.val hj
    omega
  rw [initialBank, BitMachineStackEmbedding.bank_outside
    embedPrep (fun _ => []) _ i hnot]

theorem initial_core_other_blank (n s q₁ q₂ : Nat) (child : Code)
    (i : Bank) (hchild : i ≠ 2) (hq₂ : i ≠ 12) :
    initialBank n s q₁ q₂ child
      (embedPrep (embedTemplate (embedTicketBank (embedOld i)))) = [] := by
  rw [initialBank, BitMachineStackEmbedding.bank_at]
  rw [prepBefore, BitMachineStackEmbedding.bank_at]
  rw [templateBefore, BitMachineStackEmbedding.bank_at]
  rw [ticketBefore, BitMachineStackEmbedding.bank_at]
  fin_cases i <;> simp_all [publicBase, innerBase]

theorem initial_template_output_blank (n s q₁ q₂ : Nat) (child : Code) :
    initialBank n s q₁ q₂ child 14 = [] := by
  have h := initial_core_other_blank n s q₁ q₂ child
    (14 : Bank) (by decide) (by decide)
  simpa [embedPrep, embedTemplate, embedTicketBank, embedOld] using h

def embeddedPreparationProgram : PrepLabel →
    TM2.Stmt (fun _ : FinalBank => Bool)
      PrepLabel PrepControl :=
  fun l => BitMachineStackEmbedding.stackStmt embedPrep
    (templateThenScalarsProgram l)

theorem embedded_preparation_run (n s q₁ q₂ : Nat) (child : Code)
    (hs : 3 ≤ s) :
    ∃ t ≤ templateRowClock s q₁ q₂ child +
      ((2*s+5)+(2*s+4)+1)+1,
      ((advance embeddedPreparationProgram)^[t])
        (⟨some (BitMachineRawSequence.leftLabel templateStart),
          (templateControl,scalarControl),
          initialBank n s q₁ q₂ child⟩ :
          TM2.Cfg (fun _ : FinalBank => Bool)
            PrepLabel PrepControl) =
        ⟨none, (templateControl,scalarControl),
          armBefore n s q₁ q₂ child⟩ := by
  obtain ⟨t,ht,hr⟩ := template_then_scalars_run n s q₁ q₂ child hs
  have h := BitMachineStackRun.run embedPrep (fun _ => [])
    templateThenScalarsProgram
    (⟨some (BitMachineRawSequence.leftLabel templateStart),
      (templateControl,scalarControl),
      prepBefore n s q₁ q₂ child⟩ :
      TM2.Cfg (fun _ : PrepBank => Bool)
        PrepLabel PrepControl) t
  rw [hr] at h
  exact ⟨t, ht, by simpa only [embeddedPreparationProgram,
    BitMachineStackEmbedding.stackCfg, initialBank,
    armBefore] using h⟩

theorem after_both_22 (n s q₁ q₂ : Nat) (child : Code) :
    afterBoth n s q₁ q₂ child 22 =
      encodeCode (firstArm q₁ q₂ s child) := by
  simp [afterBoth, armAfterA]

theorem after_both_23 (n s q₁ q₂ : Nat) (child : Code) :
    afterBoth n s q₁ q₂ child 23 =
      encodeCode (CodeRowArms.vertexArm n s child) := by
  simp [afterBoth]

theorem after_both_24 (n s q₁ q₂ : Nat) (child : Code) :
    afterBoth n s q₁ q₂ child 24 =
      encodeCode (CodeRowArms.auxiliaryArm s child) := by
  simp [afterBoth]

theorem after_both_29 (n s q₁ q₂ : Nat) (child : Code) :
    afterBoth n s q₁ q₂ child 29 = [] := by
  simp [afterBoth, armAfterA,
    arm_outside n s q₁ q₂ child 29 (by decide)]

theorem after_both_30 (n s q₁ q₂ : Nat) (child : Code) :
    afterBoth n s q₁ q₂ child 30 = [] := by
  simp [afterBoth, armAfterA,
    arm_outside n s q₁ q₂ child 30 (by decide)]

noncomputable def finalBank (n s q₁ q₂ : Nat) (child : Code) :
    FinalBank → List Bool :=
  Function.update (afterBoth n s q₁ q₂ child) 29
    (encodeCode (graphRowsCode (V := Fin n) q₁ q₂ s child))

theorem branch_final_run (n s q₁ q₂ : Nat) (child : Code) :
    ∃ t ≤ 2*(codeSize (firstArm q₁ q₂ s child) +
      codeSize (CodeRowArms.vertexArm n s child) +
      codeSize (CodeRowArms.auxiliaryArm s child))+11,
      ((advance branchAssembleProgram)^[t])
        (⟨some (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel
              (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan))),
          (((none,none),none),()), afterBoth n s q₁ q₂ child⟩ :
          TM2.Cfg (fun _ : FinalBank => Bool) _ _) =
        ⟨none, (((none,none),none),()),
          finalBank n s q₁ q₂ child⟩ := by
  obtain ⟨t,ht,hr⟩ := branch_assemble_run
    (afterBoth n s q₁ q₂ child) (after_both_30 n s q₁ q₂ child)
  have hout :
      branchPrefix ++
        afterBoth n s q₁ q₂ child 22 ++
        afterBoth n s q₁ q₂ child 23 ++
        afterBoth n s q₁ q₂ child 24 ++
        afterBoth n s q₁ q₂ child 29 =
      encodeCode (graphRowsCode (V := Fin n) q₁ q₂ s child) := by
    rw [after_both_22, after_both_23, after_both_24,
      after_both_29, List.append_nil]
    rw [branch_prefix_exact]
    rfl
  rw [hout] at hr
  refine ⟨t, ?_, hr⟩
  rw [after_both_22, after_both_23, after_both_24] at ht
  simp only [encodeCode_length] at ht
  omega

def preparationThenAProgram :=
  BitMachineRawSequence.program embeddedPreparationProgram armAProgram
    (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)
    (templateControl,scalarControl) (none,())

theorem preparation_then_a_run (n s q₁ q₂ : Nat) (child : Code)
    (hs : 3 ≤ s) :
    ∃ t ≤ (templateRowClock s q₁ q₂ child +
      ((2*s+5)+(2*s+4)+1)+1) +
      (2*codeSize (templateRowCode q₁ q₂ s child)+5)+1,
      ((advance preparationThenAProgram)^[t])
        (⟨some (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel templateStart)),
          ((templateControl,scalarControl),(none,())),
          initialBank n s q₁ q₂ child⟩ :
          TM2.Cfg (fun _ : FinalBank => Bool) _ _) =
        ⟨none, ((templateControl,scalarControl),(none,())),
          armAfterA n s q₁ q₂ child⟩ := by
  obtain ⟨ta,hta,ha⟩ := embedded_preparation_run n s q₁ q₂ child hs
  obtain ⟨tb,htb,hb⟩ := arm_a_run n s q₁ q₂ child
  obtain ⟨t,ht,hr⟩ := BitMachineRawSequence.runs
    embeddedPreparationProgram armAProgram
    (BitMachineRawSequence.leftLabel templateStart)
    (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)
    (templateControl,scalarControl) (templateControl,scalarControl)
    (none,()) (none,())
    (initialBank n s q₁ q₂ child)
    (armBefore n s q₁ q₂ child)
    (armAfterA n s q₁ q₂ child) ta tb ha hb
  exact ⟨t, by omega, hr⟩

def throughArmsProgram :=
  BitMachineRawSequence.program preparationThenAProgram
    embeddedArmsProgram CodeRowArms.Label.childCopy
    ((templateControl,scalarControl),(none,())) none

theorem through_arms_run (n s q₁ q₂ : Nat) (child : Code)
    (hs : 3 ≤ s) :
    ∃ t ≤ ((templateRowClock s q₁ q₂ child +
      ((2*s+5)+(2*s+4)+1)+1) +
      (2*codeSize (templateRowCode q₁ q₂ s child)+5)+1) +
      CodeRowArms.clock n s child+1,
      ((advance throughArmsProgram)^[t])
        (⟨some (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel
              (BitMachineRawSequence.leftLabel templateStart))),
          (((templateControl,scalarControl),(none,())),none),
          initialBank n s q₁ q₂ child⟩ :
          TM2.Cfg (fun _ : FinalBank => Bool) _ _) =
        ⟨none, (((templateControl,scalarControl),(none,())),none),
          afterBoth n s q₁ q₂ child⟩ := by
  obtain ⟨ta,hta,ha⟩ := preparation_then_a_run n s q₁ q₂ child hs
  obtain ⟨t,ht,hr⟩ := BitMachineRawSequence.runs
    preparationThenAProgram embeddedArmsProgram
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel templateStart))
    CodeRowArms.Label.childCopy
    ((templateControl,scalarControl),(none,()))
    ((templateControl,scalarControl),(none,())) none none
    (initialBank n s q₁ q₂ child)
    (armAfterA n s q₁ q₂ child)
    (afterBoth n s q₁ q₂ child) ta
    (CodeRowArms.clock n s child) ha
    (embedded_arms_run n s q₁ q₂ child)
  exact ⟨t, by omega, hr⟩

def program :=
  BitMachineRawSequence.program throughArmsProgram
    branchAssembleProgram
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)))
    (((templateControl,scalarControl),(none,())),none)
    (((none,none),none),())

def clockBound (n s q₁ q₂ : Nat) (child : Code) : Nat :=
  (((templateRowClock s q₁ q₂ child +
      ((2*s+5)+(2*s+4)+1)+1) +
      (2*codeSize (templateRowCode q₁ q₂ s child)+5)+1) +
      CodeRowArms.clock n s child+1) +
    (2*(codeSize (firstArm q₁ q₂ s child) +
      codeSize (CodeRowArms.vertexArm n s child) +
      codeSize (CodeRowArms.auxiliaryArm s child))+11)+1

/-- The clock is linear in the supplied operand lengths and the actual
serialized output length. The large absolute branch-header constants are
absorbed by the output syntax size, not by an input-dependent program. -/
theorem clock_linear (n s q₁ q₂ : Nat) (child : Code)
    (hs : 3 ≤ s) :
    clockBound n s q₁ q₂ child ≤
      80 * (n+s+q₁+q₂+codeSize child+
        codeSize (graphRowsCode (V := Fin n) q₁ q₂ s child)+1) := by
  have ht := template_row_clock_linear s q₁ q₂ child
  have hfirst : codeSize (firstArm q₁ q₂ s child) =
      9 + codeSize (templateRowCode q₁ q₂ s child) := by
    simp [firstArm, codeSize]
  have hgraph :
      codeSize (graphRowsCode (V := Fin n) q₁ q₂ s child) =
        1539 + codeSize (firstArm q₁ q₂ s child) +
          codeSize (CodeRowArms.vertexArm n s child) +
          codeSize (CodeRowArms.auxiliaryArm s child) := by
    change 3 + (512+1) + (510+1) + (511+1) +
      codeSize (firstArm q₁ q₂ s child) +
      codeSize (CodeRowArms.vertexArm n s child) +
      codeSize (CodeRowArms.auxiliaryArm s child) = _
    omega
  have harms : CodeRowArms.clock n s child =
      2*(codeSize child+n+((s-3)+1)+(4*s+1))+14 := by
    simp [CodeRowArms.clock, unary_length, encodeCode_length]
  unfold clockBound
  omega

/-- The physically constructed word is the source-defined graph-row code.
No generated child, branch, or desired output word appears in the initial
configuration. -/
theorem run_exact (n s q₁ q₂ : Nat) (child : Code) (hs : 3 ≤ s) :
    ∃ t ≤ clockBound n s q₁ q₂ child,
      ((advance program)^[t])
        (⟨some (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel
              (BitMachineRawSequence.leftLabel
                (BitMachineRawSequence.leftLabel templateStart)))),
          ((((templateControl,scalarControl),(none,())),none),
            (((none,none),none),())),
          initialBank n s q₁ q₂ child⟩ :
          TM2.Cfg (fun _ : FinalBank => Bool) _ _) =
        ⟨none,
          ((((templateControl,scalarControl),(none,())),none),
            (((none,none),none),())),
          finalBank n s q₁ q₂ child⟩ := by
  obtain ⟨ta,hta,ha⟩ := through_arms_run n s q₁ q₂ child hs
  obtain ⟨tb,htb,hb⟩ := branch_final_run n s q₁ q₂ child
  obtain ⟨t,ht,hr⟩ := BitMachineRawSequence.runs
    throughArmsProgram branchAssembleProgram
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel templateStart)))
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)))
    (((templateControl,scalarControl),(none,())),none)
    (((templateControl,scalarControl),(none,())),none)
    (((none,none),none),()) (((none,none),none),())
    (initialBank n s q₁ q₂ child)
    (afterBoth n s q₁ q₂ child)
    (finalBank n s q₁ q₂ child) ta tb ha hb
  exact ⟨t, by dsimp [clockBound]; omega, hr⟩

theorem output_exact (n s q₁ q₂ : Nat) (child : Code) :
    finalBank n s q₁ q₂ child 29 =
      encodeCode (graphRowsCode (V := Fin n) q₁ q₂ s child) := by
  simp [finalBank]

theorem input_child_retained (n s q₁ q₂ : Nat) (child : Code) :
    finalBank n s q₁ q₂ child 2 = encodeCode child := by
  simp only [finalBank, afterBoth,
    Function.update_of_ne (by decide : (2 : FinalBank) ≠ 29),
    Function.update_of_ne (by decide : (2 : FinalBank) ≠ 24),
    Function.update_of_ne (by decide : (2 : FinalBank) ≠ 23)]
  exact arm_inputs_2 n s q₁ q₂ child

theorem final_template_at (n s q₁ q₂ : Nat) (child : Code)
    (i : TemplateBank) :
    finalBank n s q₁ q₂ child
      (embedPrep (embedTemplate i)) =
    templateAfterAppend s q₁ q₂ child i := by
  have h29 : embedPrep (embedTemplate i) ≠ (29 : FinalBank) := by
    intro h
    have hv : i.val = 29 := by
      simpa [embedPrep, embedTemplate] using congrArg Fin.val h
    omega
  have h24 : embedPrep (embedTemplate i) ≠ (24 : FinalBank) := by
    intro h
    have hv : i.val = 24 := by
      simpa [embedPrep, embedTemplate] using congrArg Fin.val h
    omega
  have h23 : embedPrep (embedTemplate i) ≠ (23 : FinalBank) := by
    intro h
    have hv : i.val = 23 := by
      simpa [embedPrep, embedTemplate] using congrArg Fin.val h
    omega
  have h22 : embedPrep (embedTemplate i) ≠ (22 : FinalBank) := by
    intro h
    have hv : i.val = 22 := by
      simpa [embedPrep, embedTemplate] using congrArg Fin.val h
    omega
  simp only [finalBank, afterBoth, armAfterA,
    Function.update_of_ne h29, Function.update_of_ne h24,
    Function.update_of_ne h23, Function.update_of_ne h22]
  change BitMachineStackEmbedding.bank embedPrep (fun _ => [])
    (prepAfterArith n s q₁ q₂ child)
    (embedPrep (embedTemplate i)) = _
  rw [BitMachineStackEmbedding.bank_at]
  have h21 : embedTemplate i ≠ (21 : PrepBank) := by
    intro h
    have hv : i.val = 21 := by
      simpa [embedTemplate] using congrArg Fin.val h
    omega
  have h20 : embedTemplate i ≠ (20 : PrepBank) := by
    intro h
    have hv : i.val = 20 := by
      simpa [embedTemplate] using congrArg Fin.val h
    omega
  have h19 : embedTemplate i ≠ (19 : PrepBank) := by
    intro h
    have hv : i.val = 19 := by
      simpa [embedTemplate] using congrArg Fin.val h
    omega
  simp only [prepAfterArith, prepAfterTerm,
    Function.update_of_ne h21, Function.update_of_ne h20,
    Function.update_of_ne h19]
  change BitMachineStackEmbedding.bank embedTemplate (prepForeign n)
    (templateAfterAppend s q₁ q₂ child) (embedTemplate i) = _
  exact BitMachineStackEmbedding.bank_at _ _ _ i

theorem input_n_retained (n s q₁ q₂ : Nat) (child : Code) :
    finalBank n s q₁ q₂ child 18 = List.replicate n true := by
  simp only [finalBank, afterBoth,
    Function.update_of_ne (by decide : (18 : FinalBank) ≠ 29),
    Function.update_of_ne (by decide : (18 : FinalBank) ≠ 24),
    Function.update_of_ne (by decide : (18 : FinalBank) ≠ 23)]
  exact arm_inputs_18 n s q₁ q₂ child

theorem input_s_retained (n s q₁ q₂ : Nat) (child : Code) :
    finalBank n s q₁ q₂ child 17 = List.replicate s true := by
  rw [show (17 : FinalBank) = embedPrep (embedTemplate 17) by rfl,
    final_template_at]
  exact template_row_retains_s s q₁ q₂ child

theorem input_q₁_retained (n s q₁ q₂ : Nat) (child : Code) :
    finalBank n s q₁ q₂ child 16 = List.replicate q₁ true := by
  rw [show (16 : FinalBank) = embedPrep (embedTemplate 16) by rfl,
    final_template_at]
  exact template_row_retains_q₁ s q₁ q₂ child

theorem input_q₂_retained (n s q₁ q₂ : Nat) (child : Code) :
    finalBank n s q₁ q₂ child 12 = List.replicate q₂ true := by
  rw [show (12 : FinalBank) = embedPrep (embedTemplate 12) by rfl,
    final_template_at]
  exact template_row_retains_q₂ s q₁ q₂ child

theorem scratch_six_cleared (n s q₁ q₂ : Nat) (child : Code) :
    finalBank n s q₁ q₂ child 6 = [] := by
  rw [show (6 : FinalBank) = embedPrep (embedTemplate 6) by rfl,
    final_template_at]
  exact template_row_clears_scratch s q₁ q₂ child

theorem scratch_thirty_cleared (n s q₁ q₂ : Nat) (child : Code) :
    finalBank n s q₁ q₂ child 30 = [] := by
  simp only [finalBank, Function.update_of_ne
    (by decide : (30 : FinalBank) ≠ 29)]
  exact after_both_30 n s q₁ q₂ child

#print axioms run_exact
#print axioms output_exact
#print axioms clock_linear
#print axioms scratch_thirty_cleared

end Paper2.CodeRowsGraphCompiler
