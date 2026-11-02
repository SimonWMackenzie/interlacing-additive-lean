import Paper2.CodeRowsGraphCompiler
import Paper2.CodeCopiesMachine
import Paper2.CodeAtomCountInput
import Paper2.CodeConstructorMachine
import EthInapproximability.CurrentPaper.BitMachineCopy
import EthInapproximability.CurrentPaper.BitMachineRawSequence

/-! First physical successor compiler: the column code, starting from the
previous row syntax word rather than an assembled `graphRowsCode` oracle. -/

set_option maxHeartbeats 1000000

namespace Paper2.CodeRecursiveColumn

open Turing Turing.TM2.Stmt
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open Paper2.GeneratorCode Paper2.GeneratorSerialization
open Paper2.GeneratorSource Paper2.CodeRowsGraphCompiler
open Paper2.CodeRowsArmA

abbrev Stack := Fin 64

def embedRow : FinalBank ↪ Stack where
  toFun i := ⟨i.val, by omega⟩
  inj' := by
    intro a b h
    exact Fin.ext (Fin.mk.inj h)

def foreignWords (w Q : Nat) (previousCol : Code) :
    Stack → List Bool :=
  fun i => if i = 31 then List.replicate w true else
    if i = 32 then List.replicate Q true else
    if i = 33 then encodeCode previousCol else []

noncomputable def initial (n s q₁ q₂ w Q : Nat)
    (previousRow previousCol : Code) : Stack → List Bool :=
  BitMachineStackEmbedding.bank embedRow
    (foreignWords w Q previousCol)
    (initialBank n s q₁ q₂ previousRow)

noncomputable def afterGraph (n s q₁ q₂ w Q : Nat)
    (previousRow previousCol : Code) : Stack → List Bool :=
  BitMachineStackEmbedding.bank embedRow
    (foreignWords w Q previousCol)
    (finalBank n s q₁ q₂ previousRow)

def graphCode (n s q₁ q₂ : Nat) (previousRow : Code) : Code :=
  graphRowsCode (V := Fin n) q₁ q₂ s previousRow

theorem after_graph_output (n s q₁ q₂ w Q : Nat)
    (previousRow previousCol : Code) :
    afterGraph n s q₁ q₂ w Q previousRow previousCol 29 =
      encodeCode (graphCode n s q₁ q₂ previousRow) := by
  change BitMachineStackEmbedding.bank embedRow
    (foreignWords w Q previousCol)
    (finalBank n s q₁ q₂ previousRow) (embedRow 29) = _
  rw [BitMachineStackEmbedding.bank_at]
  exact output_exact n s q₁ q₂ previousRow

theorem foreign_at (w Q : Nat) (previousCol : Code)
    (S : FinalBank → List Bool) (i : Stack) (hi : 31 ≤ i.val) :
    BitMachineStackEmbedding.bank embedRow
      (foreignWords w Q previousCol) S i =
    foreignWords w Q previousCol i := by
  have hnot : ¬ ∃ j : FinalBank, embedRow j = i := by
    rintro ⟨j,hj⟩
    have hv : j.val = i.val := by
      simpa [embedRow] using congrArg Fin.val hj
    omega
  exact BitMachineStackEmbedding.bank_outside
    embedRow (foreignWords w Q previousCol) S i hnot

theorem after_graph_w (n s q₁ q₂ w Q : Nat)
    (previousRow previousCol : Code) :
    afterGraph n s q₁ q₂ w Q previousRow previousCol 31 =
      List.replicate w true := by
  rw [afterGraph, foreign_at w Q previousCol _ 31 (by decide)]
  rfl

theorem after_graph_Q (n s q₁ q₂ w Q : Nat)
    (previousRow previousCol : Code) :
    afterGraph n s q₁ q₂ w Q previousRow previousCol 32 =
      List.replicate Q true := by
  rw [afterGraph, foreign_at w Q previousCol _ 32 (by decide)]
  rfl

theorem after_graph_previous_col (n s q₁ q₂ w Q : Nat)
    (previousRow previousCol : Code) :
    afterGraph n s q₁ q₂ w Q previousRow previousCol 33 =
      encodeCode previousCol := by
  rw [afterGraph, foreign_at w Q previousCol _ 33 (by decide)]
  rfl

theorem after_graph_blank (n s q₁ q₂ w Q : Nat)
    (previousRow previousCol : Code) (i : Stack) (hi : 34 ≤ i.val) :
    afterGraph n s q₁ q₂ w Q previousRow previousCol i = [] := by
  rw [afterGraph, foreign_at w Q previousCol _ i (by omega)]
  have h31 : i ≠ (31 : Stack) := by
    intro h
    have hv := congrArg Fin.val h
    omega
  have h32 : i ≠ (32 : Stack) := by
    intro h
    have hv := congrArg Fin.val h
    omega
  have h33 : i ≠ (33 : Stack) := by
    intro h
    have hv := congrArg Fin.val h
    omega
  simp [foreignWords, h31, h32, h33]

abbrev RowLabel :=
  BitMachineRawSequence.Label
    (BitMachineRawSequence.Label
      (BitMachineRawSequence.Label
        CodeRowsGraphCompiler.PrepLabel
        (BitMachineRawSequence.Label
          BitMachineCopy.Label CodeRowsArmA.PrefixLabel))
      CodeRowArms.Label)
    (BitMachineRawSequence.Label
      (BitMachineRawSequence.Label
        (BitMachineRawSequence.Label
          BitMachineCopy.Label BitMachineCopy.Label)
        BitMachineCopy.Label)
      CodeRowsLiteralPrefix.Label)

abbrev RowControl :=
  BitMachineRawSequence.Control
    (BitMachineRawSequence.Control
      (BitMachineRawSequence.Control
        CodeRowsGraphCompiler.PrepControl
        (BitMachineRawSequence.Control (Option Bool) Unit))
      CodeRowArms.Control)
    (BitMachineRawSequence.Control
      (BitMachineRawSequence.Control
        (BitMachineRawSequence.Control (Option Bool) (Option Bool))
        (Option Bool)) Unit)

def rowStart : RowLabel :=
  BitMachineRawSequence.leftLabel
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel
          CodeRowsPreparation.templateStart)))

def rowControl : RowControl :=
  ((((CodeRowsPreparation.templateControl,
       CodeRowsPreparation.scalarControl),(none,())),none),
    (((none,none),none),()))

def liftedGraphProgram :=
  fun l => BitMachineStackEmbedding.stackStmt embedRow
    (CodeRowsGraphCompiler.program l)

theorem lifted_graph_run (n s q₁ q₂ w Q : Nat)
    (previousRow previousCol : Code) (hs : 3 ≤ s) :
    ∃ t ≤ clockBound n s q₁ q₂ previousRow,
      ((advance liftedGraphProgram)^[t])
        (⟨some rowStart, rowControl,
          initial n s q₁ q₂ w Q previousRow previousCol⟩ :
          TM2.Cfg (fun _ : Stack => Bool) _ _) =
        ⟨none, rowControl,
          afterGraph n s q₁ q₂ w Q previousRow previousCol⟩ := by
  obtain ⟨t,ht,hr⟩ :=
    CodeRowsGraphCompiler.run_exact n s q₁ q₂ previousRow hs
  have h := BitMachineStackRun.run embedRow
    (foreignWords w Q previousCol)
    CodeRowsGraphCompiler.program
    (⟨some rowStart, rowControl,
      initialBank n s q₁ q₂ previousRow⟩ :
      TM2.Cfg (fun _ : FinalBank => Bool) _ _) t
  simp only [rowStart, rowControl] at h
  rw [hr] at h
  exact ⟨t,ht,by simpa only [liftedGraphProgram,
    BitMachineStackEmbedding.stackCfg, initial, afterGraph] using h⟩

noncomputable def afterDelimiter (n s q₁ q₂ w Q : Nat)
    (previousRow previousCol : Code) : Stack → List Bool :=
  Function.update (afterGraph n s q₁ q₂ w Q previousRow previousCol)
    34 [false]

noncomputable def afterWTerm (n s q₁ q₂ w Q : Nat)
    (previousRow previousCol : Code) : Stack → List Bool :=
  Function.update (afterGraph n s q₁ q₂ w Q previousRow previousCol)
    34 (unary w)

inductive DelimiterLabel where
  | write | accept
  deriving DecidableEq, Fintype

def delimiterProgram : DelimiterLabel →
    TM2.Stmt (fun _ : Stack => Bool) DelimiterLabel Unit
  | .write => push 34 (fun _ => false) (goto (fun _ => .accept))
  | .accept => halt

theorem delimiter_run (n s q₁ q₂ w Q : Nat)
    (previousRow previousCol : Code) :
    ((advance delimiterProgram)^[2])
      (⟨some .write, (),
        afterGraph n s q₁ q₂ w Q previousRow previousCol⟩ :
        TM2.Cfg (fun _ : Stack => Bool) DelimiterLabel Unit) =
      ⟨none, (), afterDelimiter n s q₁ q₂ w Q previousRow previousCol⟩ := by
  simp [advance, TM2.step, TM2.stepAux, delimiterProgram,
    afterDelimiter]
  rw [after_graph_blank n s q₁ q₂ w Q previousRow previousCol
    34 (by decide)]

def wCopyIndex : Fin 3 ↪ Stack where
  toFun i := ![31,34,38] i
  inj' := by
    intro a b h
    fin_cases a <;> fin_cases b <;> simp_all

theorem w_copy_initial_bank (n s q₁ q₂ w Q : Nat)
    (previousRow previousCol : Code) :
    BitMachineStackEmbedding.bank wCopyIndex
      (afterDelimiter n s q₁ q₂ w Q previousRow previousCol)
      (BitMachineCopy.cfg (some .scan) none
        (List.replicate w true) [false] []).stk =
    afterDelimiter n s q₁ q₂ w Q previousRow previousCol := by
  apply BitMachineStackEmbedding.bank_eq_self
  intro i
  fin_cases i
  · change List.replicate w true =
      afterDelimiter n s q₁ q₂ w Q previousRow previousCol 31
    simp [afterDelimiter, after_graph_w]
  · change [false] =
      afterDelimiter n s q₁ q₂ w Q previousRow previousCol 34
    simp [afterDelimiter]
  · change ([] : List Bool) =
      afterDelimiter n s q₁ q₂ w Q previousRow previousCol 38
    simp [afterDelimiter,
      after_graph_blank n s q₁ q₂ w Q previousRow previousCol
        38 (by decide)]

theorem w_copy_result_bank (n s q₁ q₂ w Q : Nat)
    (previousRow previousCol : Code) :
    BitMachineStackEmbedding.bank wCopyIndex
      (afterDelimiter n s q₁ q₂ w Q previousRow previousCol)
      (BitMachineCopy.cfg none none
        (List.replicate w true) (unary w) []).stk =
    afterWTerm n s q₁ q₂ w Q previousRow previousCol := by
  have hstk :
      (BitMachineCopy.cfg none none
        (List.replicate w true) (unary w) []).stk =
      Function.update
        (BitMachineCopy.cfg (some .scan) none
          (List.replicate w true) [false] []).stk
        (1 : Fin 3) (unary w) := by
    funext i
    fin_cases i <;> rfl
  rw [hstk, BitMachineStackEmbedding.bank_update,
    w_copy_initial_bank]
  change Function.update
      (Function.update (afterGraph n s q₁ q₂ w Q
        previousRow previousCol) 34 [false]) 34 (unary w) =
    Function.update (afterGraph n s q₁ q₂ w Q
      previousRow previousCol) 34 (unary w)
  simp

def wCopyProgram : BitMachineCopy.Label →
    TM2.Stmt (fun _ : Stack => Bool)
      BitMachineCopy.Label (Option Bool) :=
  fun l => BitMachineStackEmbedding.stackStmt wCopyIndex
    (BitMachineCopy.program l)

theorem w_copy_run (n s q₁ q₂ w Q : Nat)
    (previousRow previousCol : Code) :
    ((advance wCopyProgram)^[2*w+2])
      (⟨some .scan, none,
        afterDelimiter n s q₁ q₂ w Q previousRow previousCol⟩ :
        TM2.Cfg (fun _ : Stack => Bool)
          BitMachineCopy.Label (Option Bool)) =
      ⟨none, none,
        afterWTerm n s q₁ q₂ w Q previousRow previousCol⟩ := by
  have h := BitMachineStackRun.run wCopyIndex
    (afterDelimiter n s q₁ q₂ w Q previousRow previousCol)
    BitMachineCopy.program
    (BitMachineCopy.cfg (some .scan) none
      (List.replicate w true) [false] []) (2*w+2)
  have hc := BitMachineCopy.run_correct none
    (List.replicate w true) [false]
  simp only [List.length_replicate] at hc
  rw [← BitMachineCopy.run, hc] at h
  have hword : List.replicate w true ++ [false] = unary w := rfl
  rw [hword] at h
  simpa only [wCopyProgram, BitMachineStackEmbedding.stackCfg,
    w_copy_initial_bank, w_copy_result_bank] using h

def wTermProgram :=
  BitMachineRawSequence.program delimiterProgram wCopyProgram
    BitMachineCopy.Label.scan () none

theorem w_term_run (n s q₁ q₂ w Q : Nat)
    (previousRow previousCol : Code) :
    ∃ t ≤ 2*w+5,
      ((advance wTermProgram)^[t])
        (⟨some (BitMachineRawSequence.leftLabel
            DelimiterLabel.write), ((),none),
          afterGraph n s q₁ q₂ w Q previousRow previousCol⟩ :
          TM2.Cfg (fun _ : Stack => Bool) _ _) =
        ⟨none, ((),none),
          afterWTerm n s q₁ q₂ w Q previousRow previousCol⟩ := by
  obtain ⟨t,ht,hr⟩ := BitMachineRawSequence.runs
    delimiterProgram wCopyProgram DelimiterLabel.write
    BitMachineCopy.Label.scan () () none none
    (afterGraph n s q₁ q₂ w Q previousRow previousCol)
    (afterDelimiter n s q₁ q₂ w Q previousRow previousCol)
    (afterWTerm n s q₁ q₂ w Q previousRow previousCol)
    2 (2*w+2)
    (delimiter_run n s q₁ q₂ w Q previousRow previousCol)
    (w_copy_run n s q₁ q₂ w Q previousRow previousCol)
  exact ⟨t, by omega, hr⟩

noncomputable def afterTicket (n s q₁ q₂ w Q : Nat)
    (previousRow previousCol : Code) : Stack → List Bool :=
  Function.update (afterWTerm n s q₁ q₂ w Q previousRow previousCol)
    35 (encodeCode (.ticket Q))

def ticketQIndex : Fin 3 ↪ Stack where
  toFun i := ![32,35,38] i
  inj' := by
    intro a b h
    fin_cases a <;> fin_cases b <;> simp_all

theorem ticket_initial_bank (n s q₁ q₂ w Q : Nat)
    (previousRow previousCol : Code) :
    BitMachineStackEmbedding.bank ticketQIndex
      (afterWTerm n s q₁ q₂ w Q previousRow previousCol)
      (CodeAtomCountInput.initial Q).stk =
    afterWTerm n s q₁ q₂ w Q previousRow previousCol := by
  apply BitMachineStackEmbedding.bank_eq_self
  intro i
  fin_cases i
  · change List.replicate Q true =
      afterWTerm n s q₁ q₂ w Q previousRow previousCol 32
    simp [afterWTerm, after_graph_Q]
  · change ([] : List Bool) =
      afterWTerm n s q₁ q₂ w Q previousRow previousCol 35
    simp [afterWTerm,
      after_graph_blank n s q₁ q₂ w Q previousRow previousCol
        35 (by decide)]
  · change ([] : List Bool) =
      afterWTerm n s q₁ q₂ w Q previousRow previousCol 38
    simp [afterWTerm,
      after_graph_blank n s q₁ q₂ w Q previousRow previousCol
        38 (by decide)]

theorem ticket_result_bank (n s q₁ q₂ w Q : Nat)
    (previousRow previousCol : Code) :
    BitMachineStackEmbedding.bank ticketQIndex
      (afterWTerm n s q₁ q₂ w Q previousRow previousCol)
      (CodeAtomCountInput.final Q).stk =
    afterTicket n s q₁ q₂ w Q previousRow previousCol := by
  have hstk : (CodeAtomCountInput.final Q).stk =
      Function.update (CodeAtomCountInput.initial Q).stk
        (1 : Fin 3) (encodeCode (.ticket Q)) := by
    funext i
    fin_cases i <;> rfl
  rw [hstk, BitMachineStackEmbedding.bank_update,
    ticket_initial_bank]
  rfl

def ticketQProgram : CodeAtomCountInput.Label →
    TM2.Stmt (fun _ : Stack => Bool)
      CodeAtomCountInput.Label CodeAtomCountInput.Control :=
  fun l => BitMachineStackEmbedding.stackStmt ticketQIndex
    (CodeAtomCountInput.program l)

theorem ticket_q_run (n s q₁ q₂ w Q : Nat)
    (previousRow previousCol : Code) :
    ∃ t ≤ 2*Q+8,
      ((advance ticketQProgram)^[t])
        (⟨some (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel
              CodeAtomCountInput.InitLabel.write)),
          (((),none),()),
          afterWTerm n s q₁ q₂ w Q previousRow previousCol⟩ :
          TM2.Cfg (fun _ : Stack => Bool) _ _) =
        ⟨none, (((),none),()),
          afterTicket n s q₁ q₂ w Q previousRow previousCol⟩ := by
  obtain ⟨t,ht,hr⟩ := CodeAtomCountInput.run_ticket_count Q
  have h := BitMachineStackRun.run ticketQIndex
    (afterWTerm n s q₁ q₂ w Q previousRow previousCol)
    CodeAtomCountInput.program (CodeAtomCountInput.initial Q) t
  rw [hr] at h
  exact ⟨t,ht,by simpa only [ticketQProgram,
    BitMachineStackEmbedding.stackCfg,
    ticket_initial_bank, ticket_result_bank] using h⟩

noncomputable def afterCopies (n s q₁ q₂ w Q : Nat)
    (previousRow previousCol : Code) : Stack → List Bool :=
  Function.update
    (Function.update
      (afterTicket n s q₁ q₂ w Q previousRow previousCol)
      34 [])
    36 (encodeCode (copies w (graphCode n s q₁ q₂ previousRow)))

def copiesIndex : Fin 5 ↪ Stack where
  toFun i := ![34,29,36,40,39] i
  inj' := by
    intro a b h
    fin_cases a <;> fin_cases b <;> simp_all

theorem copies_initial_bank (n s q₁ q₂ w Q : Nat)
    (previousRow previousCol : Code) :
    BitMachineStackEmbedding.bank copiesIndex
      (afterTicket n s q₁ q₂ w Q previousRow previousCol)
      (CodeCopiesMachine.initial
        (unary w) (encodeCode (graphCode n s q₁ q₂ previousRow))).stk =
    afterTicket n s q₁ q₂ w Q previousRow previousCol := by
  apply BitMachineStackEmbedding.bank_eq_self
  intro i
  fin_cases i
  · change unary w = afterTicket n s q₁ q₂ w Q
      previousRow previousCol 34
    simp [afterTicket, afterWTerm]
  · change encodeCode (graphCode n s q₁ q₂ previousRow) =
      afterTicket n s q₁ q₂ w Q previousRow previousCol 29
    simp [afterTicket, afterWTerm, after_graph_output]
  · change ([] : List Bool) =
      afterTicket n s q₁ q₂ w Q previousRow previousCol 36
    simp [afterTicket, afterWTerm,
      after_graph_blank n s q₁ q₂ w Q previousRow previousCol
        36 (by decide)]
  · change ([] : List Bool) =
      afterTicket n s q₁ q₂ w Q previousRow previousCol 40
    simp [afterTicket, afterWTerm,
      after_graph_blank n s q₁ q₂ w Q previousRow previousCol
        40 (by decide)]
  · change ([] : List Bool) =
      afterTicket n s q₁ q₂ w Q previousRow previousCol 39
    simp [afterTicket, afterWTerm,
      after_graph_blank n s q₁ q₂ w Q previousRow previousCol
        39 (by decide)]

theorem copies_result_bank (n s q₁ q₂ w Q : Nat)
    (previousRow previousCol : Code) :
    BitMachineStackEmbedding.bank copiesIndex
      (afterTicket n s q₁ q₂ w Q previousRow previousCol)
      (CodeCopiesMachine.cfg none none []
        (encodeCode (graphCode n s q₁ q₂ previousRow))
        (encodeCode (copies w (graphCode n s q₁ q₂ previousRow)))
        [] []).stk =
    afterCopies n s q₁ q₂ w Q previousRow previousCol := by
  have hstk :
      (CodeCopiesMachine.cfg none none []
        (encodeCode (graphCode n s q₁ q₂ previousRow))
        (encodeCode (copies w (graphCode n s q₁ q₂ previousRow)))
        [] []).stk =
      Function.update
        (Function.update
          (CodeCopiesMachine.initial
            (unary w) (encodeCode (graphCode n s q₁ q₂ previousRow))).stk
          (0 : Fin 5) [])
        (2 : Fin 5)
        (encodeCode (copies w (graphCode n s q₁ q₂ previousRow))) := by
    funext i
    fin_cases i <;> rfl
  rw [hstk, BitMachineStackEmbedding.bank_update,
    BitMachineStackEmbedding.bank_update, copies_initial_bank]
  rfl

def embeddedCopiesProgram : CodeCopiesMachine.Label →
    TM2.Stmt (fun _ : Stack => Bool)
      CodeCopiesMachine.Label CodeCopiesMachine.Control :=
  fun l => BitMachineStackEmbedding.stackStmt copiesIndex
    (CodeCopiesMachine.program l)

theorem embedded_copies_run (n s q₁ q₂ w Q : Nat)
    (previousRow previousCol : Code) :
    ((advance embeddedCopiesProgram)^[CodeCopiesMachine.clock w
      (graphCode n s q₁ q₂ previousRow)])
      (⟨some .initialize, none,
        afterTicket n s q₁ q₂ w Q previousRow previousCol⟩ :
        TM2.Cfg (fun _ : Stack => Bool)
          CodeCopiesMachine.Label CodeCopiesMachine.Control) =
      ⟨none, none,
        afterCopies n s q₁ q₂ w Q previousRow previousCol⟩ := by
  have h := BitMachineStackRun.run copiesIndex
    (afterTicket n s q₁ q₂ w Q previousRow previousCol)
    CodeCopiesMachine.program
    (CodeCopiesMachine.initial
      (unary w) (encodeCode (graphCode n s q₁ q₂ previousRow)))
    (CodeCopiesMachine.clock w (graphCode n s q₁ q₂ previousRow))
  rw [← CodeCopiesMachine.run,
    CodeCopiesMachine.run_copies w (graphCode n s q₁ q₂ previousRow)] at h
  simpa only [embeddedCopiesProgram,
    BitMachineStackEmbedding.stackCfg,
    copies_initial_bank,
    copies_result_bank] using h

def columnCode (n s q₁ q₂ w Q : Nat) (previousRow : Code) : Code :=
  .append (.ticket Q) (copies w (graphCode n s q₁ q₂ previousRow))

noncomputable def afterColumn (n s q₁ q₂ w Q : Nat)
    (previousRow previousCol : Code) : Stack → List Bool :=
  Function.update (afterCopies n s q₁ q₂ w Q previousRow previousCol)
    37 (encodeCode (columnCode n s q₁ q₂ w Q previousRow))

def appendIndex : Fin 8 ↪ Stack where
  toFun i := ![35,36,41,42,43,44,37,45] i
  inj' := by
    intro a b h
    fin_cases a <;> fin_cases b <;> simp_all

theorem append_initial_bank (n s q₁ q₂ w Q : Nat)
    (previousRow previousCol : Code) :
    BitMachineStackEmbedding.bank appendIndex
      (afterCopies n s q₁ q₂ w Q previousRow previousCol)
      (CodeConstructorMachine.cfg (some .appendRightCopy) none
        (CodeConstructorMachine.appendInputs (.ticket Q)
          (copies w (graphCode n s q₁ q₂ previousRow))) [] []).stk =
    afterCopies n s q₁ q₂ w Q previousRow previousCol := by
  apply BitMachineStackEmbedding.bank_eq_self
  intro i
  fin_cases i
  · change encodeCode (.ticket Q) =
      afterCopies n s q₁ q₂ w Q previousRow previousCol 35
    simp [afterCopies, afterTicket]
  · change encodeCode (copies w (graphCode n s q₁ q₂ previousRow)) =
      afterCopies n s q₁ q₂ w Q previousRow previousCol 36
    simp [afterCopies]
  · change ([] : List Bool) =
      afterCopies n s q₁ q₂ w Q previousRow previousCol 41
    simp [afterCopies, afterTicket, afterWTerm,
      after_graph_blank n s q₁ q₂ w Q previousRow previousCol
        41 (by decide)]
  · change ([] : List Bool) =
      afterCopies n s q₁ q₂ w Q previousRow previousCol 42
    simp [afterCopies, afterTicket, afterWTerm,
      after_graph_blank n s q₁ q₂ w Q previousRow previousCol
        42 (by decide)]
  · change ([] : List Bool) =
      afterCopies n s q₁ q₂ w Q previousRow previousCol 43
    simp [afterCopies, afterTicket, afterWTerm,
      after_graph_blank n s q₁ q₂ w Q previousRow previousCol
        43 (by decide)]
  · change ([] : List Bool) =
      afterCopies n s q₁ q₂ w Q previousRow previousCol 44
    simp [afterCopies, afterTicket, afterWTerm,
      after_graph_blank n s q₁ q₂ w Q previousRow previousCol
        44 (by decide)]
  · change ([] : List Bool) =
      afterCopies n s q₁ q₂ w Q previousRow previousCol 37
    simp [afterCopies, afterTicket, afterWTerm,
      after_graph_blank n s q₁ q₂ w Q previousRow previousCol
        37 (by decide)]
  · change ([] : List Bool) =
      afterCopies n s q₁ q₂ w Q previousRow previousCol 45
    simp [afterCopies, afterTicket, afterWTerm,
      after_graph_blank n s q₁ q₂ w Q previousRow previousCol
        45 (by decide)]

theorem append_result_bank (n s q₁ q₂ w Q : Nat)
    (previousRow previousCol : Code) :
    BitMachineStackEmbedding.bank appendIndex
      (afterCopies n s q₁ q₂ w Q previousRow previousCol)
      (CodeConstructorMachine.cfg none none
        (CodeConstructorMachine.appendInputs (.ticket Q)
          (copies w (graphCode n s q₁ q₂ previousRow)))
        (encodeCode (columnCode n s q₁ q₂ w Q previousRow)) []).stk =
    afterColumn n s q₁ q₂ w Q previousRow previousCol := by
  have hstk :
      (CodeConstructorMachine.cfg none none
        (CodeConstructorMachine.appendInputs (.ticket Q)
          (copies w (graphCode n s q₁ q₂ previousRow)))
        (encodeCode (columnCode n s q₁ q₂ w Q previousRow)) []).stk =
      Function.update
        (CodeConstructorMachine.cfg (some .appendRightCopy) none
          (CodeConstructorMachine.appendInputs (.ticket Q)
            (copies w (graphCode n s q₁ q₂ previousRow))) [] []).stk
        (6 : Fin 8)
        (encodeCode (columnCode n s q₁ q₂ w Q previousRow)) := by
    funext i
    fin_cases i <;> rfl
  rw [hstk, BitMachineStackEmbedding.bank_update,
    append_initial_bank]
  rfl

def embeddedAppendProgram : CodeConstructorMachine.Label →
    TM2.Stmt (fun _ : Stack => Bool)
      CodeConstructorMachine.Label CodeConstructorMachine.Control :=
  fun l => BitMachineStackEmbedding.stackStmt appendIndex
    (CodeConstructorMachine.program l)

theorem embedded_append_run (n s q₁ q₂ w Q : Nat)
    (previousRow previousCol : Code) :
    ((advance embeddedAppendProgram)^[
      CodeConstructorMachine.appendClock
        (encodeCode (.ticket Q))
        (encodeCode (copies w (graphCode n s q₁ q₂ previousRow)))])
      (⟨some .appendRightCopy, none,
        afterCopies n s q₁ q₂ w Q previousRow previousCol⟩ :
        TM2.Cfg (fun _ : Stack => Bool)
          CodeConstructorMachine.Label CodeConstructorMachine.Control) =
      ⟨none, none,
        afterColumn n s q₁ q₂ w Q previousRow previousCol⟩ := by
  have h := BitMachineStackRun.run appendIndex
    (afterCopies n s q₁ q₂ w Q previousRow previousCol)
    CodeConstructorMachine.program
    (CodeConstructorMachine.cfg (some .appendRightCopy) none
      (CodeConstructorMachine.appendInputs (.ticket Q)
        (copies w (graphCode n s q₁ q₂ previousRow))) [] [])
    (CodeConstructorMachine.appendClock
      (encodeCode (.ticket Q))
      (encodeCode (copies w (graphCode n s q₁ q₂ previousRow))))
  rw [← CodeConstructorMachine.run,
    CodeConstructorMachine.run_append (.ticket Q)
      (copies w (graphCode n s q₁ q₂ previousRow))] at h
  have hr := append_result_bank n s q₁ q₂ w Q previousRow previousCol
  simp only [columnCode] at hr
  simpa only [embeddedAppendProgram,
    BitMachineStackEmbedding.stackCfg,
    append_initial_bank, hr] using h

def throughWProgram :=
  BitMachineRawSequence.program liftedGraphProgram wTermProgram
    (BitMachineRawSequence.leftLabel DelimiterLabel.write)
    rowControl ((),none)

theorem through_w_run (n s q₁ q₂ w Q : Nat)
    (previousRow previousCol : Code) (hs : 3 ≤ s) :
    ∃ t ≤ clockBound n s q₁ q₂ previousRow + (2*w+5)+1,
      ((advance throughWProgram)^[t])
        (⟨some (BitMachineRawSequence.leftLabel rowStart),
          (rowControl,((),none)),
          initial n s q₁ q₂ w Q previousRow previousCol⟩ :
          TM2.Cfg (fun _ : Stack => Bool) _ _) =
        ⟨none, (rowControl,((),none)),
          afterWTerm n s q₁ q₂ w Q previousRow previousCol⟩ := by
  obtain ⟨ta,hta,ha⟩ :=
    lifted_graph_run n s q₁ q₂ w Q previousRow previousCol hs
  obtain ⟨tb,htb,hb⟩ :=
    w_term_run n s q₁ q₂ w Q previousRow previousCol
  obtain ⟨t,ht,hr⟩ := BitMachineRawSequence.runs
    liftedGraphProgram wTermProgram rowStart
    (BitMachineRawSequence.leftLabel DelimiterLabel.write)
    rowControl rowControl ((),none) ((),none)
    (initial n s q₁ q₂ w Q previousRow previousCol)
    (afterGraph n s q₁ q₂ w Q previousRow previousCol)
    (afterWTerm n s q₁ q₂ w Q previousRow previousCol)
    ta tb ha hb
  exact ⟨t, by omega, hr⟩

def throughTicketProgram :=
  BitMachineRawSequence.program throughWProgram ticketQProgram
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel
        CodeAtomCountInput.InitLabel.write))
    (rowControl,((),none)) (((),none),())

theorem through_ticket_run (n s q₁ q₂ w Q : Nat)
    (previousRow previousCol : Code) (hs : 3 ≤ s) :
    ∃ t ≤ (clockBound n s q₁ q₂ previousRow + (2*w+5)+1) +
      (2*Q+8)+1,
      ((advance throughTicketProgram)^[t])
        (⟨some (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel rowStart)),
          ((rowControl,((),none)),(((),none),())),
          initial n s q₁ q₂ w Q previousRow previousCol⟩ :
          TM2.Cfg (fun _ : Stack => Bool) _ _) =
        ⟨none, ((rowControl,((),none)),(((),none),())),
          afterTicket n s q₁ q₂ w Q previousRow previousCol⟩ := by
  obtain ⟨ta,hta,ha⟩ :=
    through_w_run n s q₁ q₂ w Q previousRow previousCol hs
  obtain ⟨tb,htb,hb⟩ :=
    ticket_q_run n s q₁ q₂ w Q previousRow previousCol
  obtain ⟨t,ht,hr⟩ := BitMachineRawSequence.runs
    throughWProgram ticketQProgram
    (BitMachineRawSequence.leftLabel rowStart)
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel
        CodeAtomCountInput.InitLabel.write))
    (rowControl,((),none)) (rowControl,((),none))
    (((),none),()) (((),none),())
    (initial n s q₁ q₂ w Q previousRow previousCol)
    (afterWTerm n s q₁ q₂ w Q previousRow previousCol)
    (afterTicket n s q₁ q₂ w Q previousRow previousCol)
    ta tb ha hb
  exact ⟨t, by omega, hr⟩

def throughCopiesProgram :=
  BitMachineRawSequence.program throughTicketProgram
    embeddedCopiesProgram CodeCopiesMachine.Label.initialize
    ((rowControl,((),none)),(((),none),())) none

theorem through_copies_run (n s q₁ q₂ w Q : Nat)
    (previousRow previousCol : Code) (hs : 3 ≤ s) :
    ∃ t ≤ ((clockBound n s q₁ q₂ previousRow + (2*w+5)+1) +
      (2*Q+8)+1) +
      CodeCopiesMachine.clock w (graphCode n s q₁ q₂ previousRow)+1,
      ((advance throughCopiesProgram)^[t])
        (⟨some (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel
              (BitMachineRawSequence.leftLabel rowStart))),
          (((rowControl,((),none)),(((),none),())),none),
          initial n s q₁ q₂ w Q previousRow previousCol⟩ :
          TM2.Cfg (fun _ : Stack => Bool) _ _) =
        ⟨none, (((rowControl,((),none)),(((),none),())),none),
          afterCopies n s q₁ q₂ w Q previousRow previousCol⟩ := by
  obtain ⟨ta,hta,ha⟩ :=
    through_ticket_run n s q₁ q₂ w Q previousRow previousCol hs
  obtain ⟨t,ht,hr⟩ := BitMachineRawSequence.runs
    throughTicketProgram embeddedCopiesProgram
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel rowStart))
    CodeCopiesMachine.Label.initialize
    ((rowControl,((),none)),(((),none),()))
    ((rowControl,((),none)),(((),none),())) none none
    (initial n s q₁ q₂ w Q previousRow previousCol)
    (afterTicket n s q₁ q₂ w Q previousRow previousCol)
    (afterCopies n s q₁ q₂ w Q previousRow previousCol)
    ta (CodeCopiesMachine.clock w (graphCode n s q₁ q₂ previousRow))
    ha (embedded_copies_run n s q₁ q₂ w Q previousRow previousCol)
  exact ⟨t, by omega, hr⟩

def program :=
  BitMachineRawSequence.program throughCopiesProgram
    embeddedAppendProgram CodeConstructorMachine.Label.appendRightCopy
    (((rowControl,((),none)),(((),none),())),none) none

def clockBound (n s q₁ q₂ w Q : Nat) (previousRow : Code) : Nat :=
  (((CodeRowsGraphCompiler.clockBound n s q₁ q₂ previousRow + (2*w+5)+1) +
      (2*Q+8)+1) +
      CodeCopiesMachine.clock w (graphCode n s q₁ q₂ previousRow)+1) +
    CodeConstructorMachine.appendClock
      (encodeCode (.ticket Q))
      (encodeCode (copies w (graphCode n s q₁ q₂ previousRow)))+1

theorem run_exact (n s q₁ q₂ w Q : Nat)
    (previousRow previousCol : Code) (hs : 3 ≤ s) :
    ∃ t ≤ clockBound n s q₁ q₂ w Q previousRow,
      ((advance program)^[t])
        (⟨some (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel
              (BitMachineRawSequence.leftLabel
                (BitMachineRawSequence.leftLabel rowStart)))),
          ((((rowControl,((),none)),(((),none),())),none),none),
          initial n s q₁ q₂ w Q previousRow previousCol⟩ :
          TM2.Cfg (fun _ : Stack => Bool) _ _) =
        ⟨none,
          ((((rowControl,((),none)),(((),none),())),none),none),
          afterColumn n s q₁ q₂ w Q previousRow previousCol⟩ := by
  obtain ⟨ta,hta,ha⟩ :=
    through_copies_run n s q₁ q₂ w Q previousRow previousCol hs
  obtain ⟨t,ht,hr⟩ := BitMachineRawSequence.runs
    throughCopiesProgram embeddedAppendProgram
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel rowStart)))
    CodeConstructorMachine.Label.appendRightCopy
    (((rowControl,((),none)),(((),none),())),none)
    (((rowControl,((),none)),(((),none),())),none)
    none none
    (initial n s q₁ q₂ w Q previousRow previousCol)
    (afterCopies n s q₁ q₂ w Q previousRow previousCol)
    (afterColumn n s q₁ q₂ w Q previousRow previousCol)
    ta (CodeConstructorMachine.appendClock
      (encodeCode (.ticket Q))
      (encodeCode (copies w (graphCode n s q₁ q₂ previousRow))))
    ha (embedded_append_run n s q₁ q₂ w Q previousRow previousCol)
  exact ⟨t, by dsimp [clockBound]; omega, hr⟩

theorem output_exact (n s q₁ q₂ w Q : Nat)
    (previousRow previousCol : Code) :
    afterColumn n s q₁ q₂ w Q previousRow previousCol 37 =
      encodeCode (columnCode n s q₁ q₂ w Q previousRow) := by
  simp [afterColumn]

theorem source_successor_column (n s q₁ q₂ w Q : Nat)
    (row₀ col₀ : Code) (k : Nat) :
    columnCode n s q₁ q₂ w Q
      (recursiveCodes n s q₁ q₂ w Q row₀ col₀ k).1 =
    (recursiveCodes n s q₁ q₂ w Q row₀ col₀ (k+1)).2 := by
  rfl

#print axioms run_exact
#print axioms output_exact

end Paper2.CodeRecursiveColumn
