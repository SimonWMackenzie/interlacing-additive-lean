import Paper2.CodeRowsCompiler
import Paper2.CodeConstructorMachine
import Paper2.CodeCopiesMachine
import EthInapproximability.CurrentPaper.BitMachineRawSequence
import EthInapproximability.CurrentPaper.BitMachineStackRun
import EthInapproximability.CurrentPaper.BitMachineCopy
import Paper2.CodeAtomCountInput

/-! Physical wiring checkpoint for the actual template-row syntax. -/

namespace Paper2.CodeRowsJoin

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open Paper2.GeneratorCode Paper2.GeneratorSerialization
open Paper2.GeneratorSource

abbrev Bank := Fin 16

/-- Inner append reads serialized ticket and child on banks 1,2; it writes
the serialized append on bank 3. Bank 6 is scratch. -/
def innerIndex : Fin 8 ↪ Bank where
  toFun i := ![1,2,8,9,10,11,3,6] i
  inj' := by
    intro a b h
    fin_cases a <;> fin_cases b <;> simp_all

/-- Copies consumes a working count on bank 0, reads and retains the inner
code on bank 3, and produces the right-nested copies code on bank 4. -/
def copiesIndex : Fin 5 ↪ Bank where
  toFun i := ![0,3,4,6,7] i
  inj' := by
    intro a b h
    fin_cases a <;> fin_cases b <;> simp_all

def innerBase (q₂ : Nat) (ticket child : Code) : Bank → List Bool :=
  fun i => if i = 0 then unary q₂ else if i = 1 then encodeCode ticket else
    if i = 2 then encodeCode child else if i = 12 then
      List.replicate q₂ true else []

def publicBase (q₂ : Nat) (ticket child : Code) : Bank → List Bool :=
  Function.update (innerBase q₂ ticket child) (0 : Bank) []

def countTerminated (q₂ : Nat) (ticket child : Code) : Bank → List Bool :=
  Function.update (publicBase q₂ ticket child) (0 : Bank) [false]

def countCopyIndex : Fin 3 ↪ Bank where
  toFun i := ![12,0,6] i
  inj' := by
    intro a b h
    fin_cases a <;> fin_cases b <;> simp_all

inductive TerminatorLabel where
  | write | accept
  deriving DecidableEq, Fintype

def terminatorProgram : TerminatorLabel →
    TM2.Stmt (fun _ : Bank => Bool) TerminatorLabel Unit
  | .write => TM2.Stmt.push 0 (fun _ => false)
      (TM2.Stmt.goto (fun _ => .accept))
  | .accept => TM2.Stmt.halt

theorem terminator_run (q₂ : Nat) (ticket child : Code) :
    ((advance terminatorProgram)^[2])
      (⟨some .write, (), publicBase q₂ ticket child⟩ :
        TM2.Cfg (fun _ : Bank => Bool) TerminatorLabel Unit) =
      ⟨none, (), countTerminated q₂ ticket child⟩ := by
  simp [advance, TM2.step, TM2.stepAux, terminatorProgram,
    countTerminated, publicBase, Function.update]

theorem count_copy_initial_bank (q₂ : Nat) (ticket child : Code) :
    BitMachineStackEmbedding.bank countCopyIndex
      (countTerminated q₂ ticket child)
      (BitMachineCopy.cfg (some .scan) none
        (List.replicate q₂ true) [false] []).stk =
      countTerminated q₂ ticket child := by
  apply BitMachineStackEmbedding.bank_eq_self
  intro i
  fin_cases i <;> simp [countCopyIndex, countTerminated,
    publicBase, innerBase, BitMachineCopy.cfg,
    BitMachineCopy.stackContents]

theorem count_copy_result_bank (q₂ : Nat) (ticket child : Code) :
    BitMachineStackEmbedding.bank countCopyIndex
      (countTerminated q₂ ticket child)
      (BitMachineCopy.cfg none none
        (List.replicate q₂ true) (unary q₂) []).stk =
      innerBase q₂ ticket child := by
  have hstk :
      (BitMachineCopy.cfg none none
        (List.replicate q₂ true) (unary q₂) []).stk =
      Function.update
        (BitMachineCopy.cfg (some .scan) none
          (List.replicate q₂ true) [false] []).stk
        (1 : Fin 3) (unary q₂) := by
    funext i
    fin_cases i <;> rfl
  rw [hstk, BitMachineStackEmbedding.bank_update,
    count_copy_initial_bank]
  funext i
  fin_cases i <;> simp [countCopyIndex, countTerminated,
    publicBase, innerBase]

def countCopyProgram : BitMachineCopy.Label →
    TM2.Stmt (fun _ : Bank => Bool) BitMachineCopy.Label (Option Bool) :=
  fun l => BitMachineStackEmbedding.stackStmt countCopyIndex
    (BitMachineCopy.program l)

theorem count_copy_run (q₂ : Nat) (ticket child : Code) :
    ((advance countCopyProgram)^[2*(List.replicate q₂ true).length+2])
      (⟨some .scan, none, countTerminated q₂ ticket child⟩ :
        TM2.Cfg (fun _ : Bank => Bool) BitMachineCopy.Label (Option Bool)) =
      ⟨none, none, innerBase q₂ ticket child⟩ := by
  have h := BitMachineStackRun.run countCopyIndex
    (countTerminated q₂ ticket child) BitMachineCopy.program
    (BitMachineCopy.cfg (some .scan) none
      (List.replicate q₂ true) [false] [])
    (2*(List.replicate q₂ true).length+2)
  rw [← BitMachineCopy.run,
    BitMachineCopy.run_correct none (List.replicate q₂ true) [false]] at h
  simp only [BitMachineStackEmbedding.stackCfg] at h
  rw [count_copy_initial_bank] at h
  have hword : List.replicate q₂ true ++ [false] = unary q₂ := rfl
  rw [hword, count_copy_result_bank] at h
  simpa [countCopyProgram, BitMachineCopy.cfg] using h

def countPrepProgram :=
  BitMachineRawSequence.program terminatorProgram countCopyProgram
    BitMachineCopy.Label.scan () none

theorem count_prep_run (q₂ : Nat) (ticket child : Code) :
    ∃ t ≤ 2*q₂+5,
      ((advance countPrepProgram)^[t])
        (⟨some (BitMachineRawSequence.leftLabel TerminatorLabel.write),
          ((),none), publicBase q₂ ticket child⟩ :
          TM2.Cfg (fun _ : Bank => Bool)
            (BitMachineRawSequence.Label TerminatorLabel
              BitMachineCopy.Label)
            (BitMachineRawSequence.Control Unit (Option Bool))) =
        ⟨none, ((),none), innerBase q₂ ticket child⟩ := by
  obtain ⟨t,ht,hr⟩ := BitMachineRawSequence.runs
    terminatorProgram countCopyProgram TerminatorLabel.write
    BitMachineCopy.Label.scan () () none none
    (publicBase q₂ ticket child) (countTerminated q₂ ticket child)
    (innerBase q₂ ticket child) 2
    (2*(List.replicate q₂ true).length+2)
    (terminator_run q₂ ticket child) (count_copy_run q₂ ticket child)
  refine ⟨t, ?_, hr⟩
  simp only [List.length_replicate] at ht
  omega

def innerFirst (q₂ : Nat) (ticket child : Code) : Bank → List Bool :=
  Function.update (innerBase q₂ ticket child) (3 : Bank)
    (encodeCode (.append ticket child))

def innerFinal (q₂ : Nat) (ticket child : Code) : Bank → List Bool :=
  Function.update (Function.update (innerFirst q₂ ticket child)
    (0 : Bank) []) (4 : Bank) (encodeCode (copies q₂ (.append ticket child)))

theorem inner_initial_bank (q₂ : Nat) (ticket child : Code) :
    BitMachineStackEmbedding.bank innerIndex (innerBase q₂ ticket child)
      (CodeConstructorMachine.cfg (some .appendRightCopy) none
        (CodeConstructorMachine.appendInputs ticket child) [] []).stk =
      innerBase q₂ ticket child := by
  apply BitMachineStackEmbedding.bank_eq_self
  intro i
  fin_cases i <;> simp [innerIndex, innerBase,
    CodeConstructorMachine.cfg, CodeConstructorMachine.contents,
    CodeConstructorMachine.appendInputs]

theorem inner_result_bank (q₂ : Nat) (ticket child : Code) :
    BitMachineStackEmbedding.bank innerIndex (innerBase q₂ ticket child)
      (CodeConstructorMachine.cfg none none
        (CodeConstructorMachine.appendInputs ticket child)
        (encodeCode (.append ticket child)) []).stk =
      innerFirst q₂ ticket child := by
  have hstk :
      (CodeConstructorMachine.cfg none none
        (CodeConstructorMachine.appendInputs ticket child)
        (encodeCode (.append ticket child)) []).stk =
      Function.update
        (CodeConstructorMachine.cfg (some .appendRightCopy) none
          (CodeConstructorMachine.appendInputs ticket child) [] []).stk
        (6 : Fin 8) (encodeCode (.append ticket child)) := by
    funext i
    fin_cases i <;> rfl
  rw [hstk, BitMachineStackEmbedding.bank_update,
    inner_initial_bank]
  rfl

theorem copies_initial_bank (q₂ : Nat) (ticket child : Code) :
    BitMachineStackEmbedding.bank copiesIndex (innerFirst q₂ ticket child)
      (CodeCopiesMachine.initial (unary q₂)
        (encodeCode (.append ticket child))).stk =
      innerFirst q₂ ticket child := by
  apply BitMachineStackEmbedding.bank_eq_self
  intro i
  fin_cases i <;> simp [copiesIndex, innerFirst, innerBase,
    CodeCopiesMachine.initial, CodeCopiesMachine.cfg,
    CodeCopiesMachine.contents]

theorem copies_result_bank (q₂ : Nat) (ticket child : Code) :
    BitMachineStackEmbedding.bank copiesIndex (innerFirst q₂ ticket child)
      (CodeCopiesMachine.cfg none none []
        (encodeCode (.append ticket child))
        (encodeCode (copies q₂ (.append ticket child))) [] []).stk =
      innerFinal q₂ ticket child := by
  have hstk :
      (CodeCopiesMachine.cfg none none []
        (encodeCode (.append ticket child))
        (encodeCode (copies q₂ (.append ticket child))) [] []).stk =
      Function.update
        (Function.update
          (CodeCopiesMachine.initial (unary q₂)
            (encodeCode (.append ticket child))).stk
          (0 : Fin 5) [])
        (2 : Fin 5) (encodeCode (copies q₂ (.append ticket child))) := by
    funext i
    fin_cases i <;> rfl
  rw [hstk, BitMachineStackEmbedding.bank_update,
    BitMachineStackEmbedding.bank_update, copies_initial_bank]
  rfl

def innerProgram : CodeConstructorMachine.Label →
    TM2.Stmt (fun _ : Bank => Bool) CodeConstructorMachine.Label
      CodeConstructorMachine.Control :=
  fun l => BitMachineStackEmbedding.stackStmt innerIndex
    (CodeConstructorMachine.program l)

def copiesProgram : CodeCopiesMachine.Label →
    TM2.Stmt (fun _ : Bank => Bool) CodeCopiesMachine.Label
      CodeCopiesMachine.Control :=
  fun l => BitMachineStackEmbedding.stackStmt copiesIndex
    (CodeCopiesMachine.program l)

theorem inner_run (q₂ : Nat) (ticket child : Code) :
    ((advance innerProgram)^[CodeConstructorMachine.appendClock
      (encodeCode ticket) (encodeCode child)])
      (⟨some .appendRightCopy, none, innerBase q₂ ticket child⟩ :
        TM2.Cfg (fun _ : Bank => Bool) CodeConstructorMachine.Label
          CodeConstructorMachine.Control) =
      ⟨none, none, innerFirst q₂ ticket child⟩ := by
  have h := BitMachineStackRun.run innerIndex
    (innerBase q₂ ticket child) CodeConstructorMachine.program
    (CodeConstructorMachine.cfg (some .appendRightCopy) none
      (CodeConstructorMachine.appendInputs ticket child) [] [])
    (CodeConstructorMachine.appendClock (encodeCode ticket) (encodeCode child))
  rw [← CodeConstructorMachine.run, CodeConstructorMachine.run_append] at h
  simpa only [innerProgram, BitMachineStackEmbedding.stackCfg,
    inner_initial_bank, inner_result_bank]
    using h

theorem copies_run (q₂ : Nat) (ticket child : Code) :
    ((advance copiesProgram)^[CodeCopiesMachine.clock q₂
      (.append ticket child)])
      (⟨some .initialize, none, innerFirst q₂ ticket child⟩ :
        TM2.Cfg (fun _ : Bank => Bool) CodeCopiesMachine.Label
          CodeCopiesMachine.Control) =
      ⟨none, none, innerFinal q₂ ticket child⟩ := by
  have h := BitMachineStackRun.run copiesIndex
    (innerFirst q₂ ticket child) CodeCopiesMachine.program
    (CodeCopiesMachine.initial (unary q₂)
      (encodeCode (.append ticket child)))
    (CodeCopiesMachine.clock q₂ (.append ticket child))
  rw [← CodeCopiesMachine.run, CodeCopiesMachine.run_copies] at h
  simpa only [copiesProgram, BitMachineStackEmbedding.stackCfg,
    copies_initial_bank, copies_result_bank] using h

def appendCopiesProgram :=
  BitMachineRawSequence.program innerProgram copiesProgram
    CodeCopiesMachine.Label.initialize
    (none : CodeConstructorMachine.Control)
    (none : CodeCopiesMachine.Control)

/-- One fixed ambient controller physically constructs the inner append,
then its right-nested `q₂` copies. The count bank is a *working* count and
is consumed, so a retained public q₂ needs a preceding physical copy. -/
theorem append_copies_run (q₂ : Nat) (ticket child : Code) :
    ∃ t ≤ CodeConstructorMachine.appendClock
        (encodeCode ticket) (encodeCode child) +
        CodeCopiesMachine.clock q₂ (.append ticket child) + 1,
      ((advance appendCopiesProgram)^[t])
        (⟨some (BitMachineRawSequence.leftLabel
            CodeConstructorMachine.Label.appendRightCopy),
          (none,none), innerBase q₂ ticket child⟩ :
          TM2.Cfg (fun _ : Bank => Bool)
            (BitMachineRawSequence.Label CodeConstructorMachine.Label
              CodeCopiesMachine.Label)
            (BitMachineRawSequence.Control CodeConstructorMachine.Control
              CodeCopiesMachine.Control)) =
        ⟨none, (none,none), innerFinal q₂ ticket child⟩ := by
  exact BitMachineRawSequence.runs innerProgram copiesProgram
    CodeConstructorMachine.Label.appendRightCopy
    CodeCopiesMachine.Label.initialize none none none none
    (innerBase q₂ ticket child) (innerFirst q₂ ticket child)
    (innerFinal q₂ ticket child)
    (CodeConstructorMachine.appendClock (encodeCode ticket) (encodeCode child))
    (CodeCopiesMachine.clock q₂ (.append ticket child))
    (inner_run q₂ ticket child) (copies_run q₂ ticket child)

def preparedAppendCopiesProgram :=
  BitMachineRawSequence.program countPrepProgram appendCopiesProgram
    (BitMachineRawSequence.leftLabel
      CodeConstructorMachine.Label.appendRightCopy)
    ((), (none : Option Bool))
    ((none : Option Bool), (none : Option Bool))

/-- One physical fixed controller: retain a delimiter-free public q₂ count
on bank 12, physically generate a terminated working count on bank 0,
construct the exact inner `.append`, and run actual `copies q₂` syntax
generation. The ticket word on bank 1 is still an explicit prerequisite. -/
theorem prepared_append_copies_run (q₂ : Nat) (ticket child : Code) :
    ∃ t ≤ 2*q₂+5 +
      CodeConstructorMachine.appendClock
        (encodeCode ticket) (encodeCode child) +
      CodeCopiesMachine.clock q₂ (.append ticket child) + 2,
      ((advance preparedAppendCopiesProgram)^[t])
        (⟨some (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel TerminatorLabel.write)),
          (((),none),(none,none)), publicBase q₂ ticket child⟩ :
          TM2.Cfg (fun _ : Bank => Bool)
            (BitMachineRawSequence.Label
              (BitMachineRawSequence.Label TerminatorLabel BitMachineCopy.Label)
              (BitMachineRawSequence.Label CodeConstructorMachine.Label
                CodeCopiesMachine.Label))
            (BitMachineRawSequence.Control
              (BitMachineRawSequence.Control Unit (Option Bool))
              (BitMachineRawSequence.Control CodeConstructorMachine.Control
                CodeCopiesMachine.Control))) =
        ⟨none, (((),none),(none,none)), innerFinal q₂ ticket child⟩ := by
  obtain ⟨ta,hta,ha⟩ := count_prep_run q₂ ticket child
  obtain ⟨tb,htb,hb⟩ := append_copies_run q₂ ticket child
  obtain ⟨t,ht,hr⟩ := BitMachineRawSequence.runs
    countPrepProgram appendCopiesProgram
    (BitMachineRawSequence.leftLabel TerminatorLabel.write)
    (BitMachineRawSequence.leftLabel
      CodeConstructorMachine.Label.appendRightCopy)
    ((),none) ((),none) (none,none) (none,none)
    (publicBase q₂ ticket child) (innerBase q₂ ticket child)
    (innerFinal q₂ ticket child) ta tb ha hb
  exact ⟨t, by omega, hr⟩

abbrev TicketBank := Fin 17

def embedOld : Bank ↪ TicketBank where
  toFun i := ⟨i.val, by omega⟩
  inj' := by
    intro a b h
    exact Fin.ext (Fin.mk.inj h)

def ticketIndex : Fin 3 ↪ TicketBank where
  toFun i := ![16,1,6] i
  inj' := by
    intro a b h
    fin_cases a <;> fin_cases b <;> simp_all

def ticketForeign (q₁ : Nat) : TicketBank → List Bool :=
  fun i => if i = 16 then List.replicate q₁ true else []

noncomputable def ticketBefore (q₁ q₂ : Nat) (child : Code) :
    TicketBank → List Bool :=
  BitMachineStackEmbedding.bank embedOld (ticketForeign q₁)
    (Function.update (publicBase q₂ (.ticket q₁) child) (1 : Bank) [])

noncomputable def ticketReady (q₁ q₂ : Nat) (child : Code) :
    TicketBank → List Bool :=
  BitMachineStackEmbedding.bank embedOld (ticketForeign q₁)
    (publicBase q₂ (.ticket q₁) child)

noncomputable def ticketAfterCopies (q₁ q₂ : Nat) (child : Code) :
    TicketBank → List Bool :=
  BitMachineStackEmbedding.bank embedOld (ticketForeign q₁)
    (innerFinal q₂ (.ticket q₁) child)

theorem ticket_initial_bank (q₁ q₂ : Nat) (child : Code) :
    BitMachineStackEmbedding.bank ticketIndex (ticketBefore q₁ q₂ child)
      (CodeAtomCountInput.initial q₁).stk = ticketBefore q₁ q₂ child := by
  apply BitMachineStackEmbedding.bank_eq_self
  intro i
  fin_cases i
  · have hnot : ¬ ∃ j : Bank, embedOld j = (16 : TicketBank) := by
      rintro ⟨j,hj⟩
      have hv : j.val = 16 := by
        simpa [embedOld] using congrArg Fin.val hj
      omega
    change List.replicate q₁ true = ticketBefore q₁ q₂ child 16
    rw [ticketBefore, BitMachineStackEmbedding.bank_outside
      embedOld (ticketForeign q₁) _ 16 hnot]
    rfl
  · change ([] : List Bool) = ticketBefore q₁ q₂ child 1
    rw [ticketBefore,
      show (1 : TicketBank) = embedOld (1 : Bank) by rfl,
      BitMachineStackEmbedding.bank_at]
    rfl
  · change ([] : List Bool) = ticketBefore q₁ q₂ child 6
    rw [ticketBefore,
      show (6 : TicketBank) = embedOld (6 : Bank) by rfl,
      BitMachineStackEmbedding.bank_at]
    rfl

theorem ticket_result_bank (q₁ q₂ : Nat) (child : Code) :
    BitMachineStackEmbedding.bank ticketIndex (ticketBefore q₁ q₂ child)
      (CodeAtomCountInput.final q₁).stk = ticketReady q₁ q₂ child := by
  have hstk : (CodeAtomCountInput.final q₁).stk =
      Function.update (CodeAtomCountInput.initial q₁).stk (1 : Fin 3)
        (encodeCode (.ticket q₁)) := by
    funext i
    fin_cases i <;> rfl
  rw [hstk, BitMachineStackEmbedding.bank_update, ticket_initial_bank]
  change Function.update
      (BitMachineStackEmbedding.bank embedOld (ticketForeign q₁)
        (Function.update (publicBase q₂ (.ticket q₁) child) 1 []))
      (embedOld (1 : Bank)) (encodeCode (.ticket q₁)) =
      BitMachineStackEmbedding.bank embedOld (ticketForeign q₁)
        (publicBase q₂ (.ticket q₁) child)
  rw [← BitMachineStackEmbedding.bank_update]
  congr 1
  funext i
  fin_cases i <;> simp [publicBase, innerBase]

def ticketProgram : CodeAtomCountInput.Label →
    TM2.Stmt (fun _ : TicketBank => Bool)
      CodeAtomCountInput.Label CodeAtomCountInput.Control :=
  fun l => BitMachineStackEmbedding.stackStmt ticketIndex
    (CodeAtomCountInput.program l)

theorem ticket_run (q₁ q₂ : Nat) (child : Code) :
    ∃ t ≤ 2*q₁+8,
      ((advance ticketProgram)^[t])
        (⟨(CodeAtomCountInput.initial q₁).l,
          (CodeAtomCountInput.initial q₁).var,
          ticketBefore q₁ q₂ child⟩ :
          TM2.Cfg (fun _ : TicketBank => Bool)
            CodeAtomCountInput.Label CodeAtomCountInput.Control) =
        ⟨none, (CodeAtomCountInput.final q₁).var,
          ticketReady q₁ q₂ child⟩ := by
  obtain ⟨t,ht,hr⟩ := CodeAtomCountInput.run_ticket_count q₁
  have h := BitMachineStackRun.run ticketIndex
    (ticketBefore q₁ q₂ child) CodeAtomCountInput.program
    (CodeAtomCountInput.initial q₁) t
  rw [hr] at h
  refine ⟨t, ht, ?_⟩
  simpa only [ticketProgram, BitMachineStackEmbedding.stackCfg,
    ticket_initial_bank, ticket_result_bank] using h

def oldIndex : Bank ↪ TicketBank := embedOld

def liftedPreparedProgram :
    (BitMachineRawSequence.Label
      (BitMachineRawSequence.Label TerminatorLabel BitMachineCopy.Label)
      (BitMachineRawSequence.Label CodeConstructorMachine.Label
        CodeCopiesMachine.Label)) →
    TM2.Stmt (fun _ : TicketBank => Bool)
      (BitMachineRawSequence.Label
        (BitMachineRawSequence.Label TerminatorLabel BitMachineCopy.Label)
        (BitMachineRawSequence.Label CodeConstructorMachine.Label
          CodeCopiesMachine.Label))
      (BitMachineRawSequence.Control
        (BitMachineRawSequence.Control Unit (Option Bool))
        (BitMachineRawSequence.Control CodeConstructorMachine.Control
          CodeCopiesMachine.Control)) :=
  fun l => BitMachineStackEmbedding.stackStmt oldIndex
    (preparedAppendCopiesProgram l)

theorem lifted_prepared_run (q₁ q₂ : Nat) (child : Code) :
    ∃ t ≤ 2*q₂+5 +
      CodeConstructorMachine.appendClock
        (encodeCode (.ticket q₁)) (encodeCode child) +
      CodeCopiesMachine.clock q₂ (.append (.ticket q₁) child) + 2,
      ((advance liftedPreparedProgram)^[t])
        (⟨some (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel TerminatorLabel.write)),
          (((),none),(none,none)), ticketReady q₁ q₂ child⟩ :
          TM2.Cfg (fun _ : TicketBank => Bool) _ _) =
        ⟨none, (((),none),(none,none)),
          ticketAfterCopies q₁ q₂ child⟩ := by
  obtain ⟨t,ht,hr⟩ := prepared_append_copies_run q₂ (.ticket q₁) child
  have h := BitMachineStackRun.run oldIndex (ticketForeign q₁)
    preparedAppendCopiesProgram
    (⟨some (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel TerminatorLabel.write)),
      (((),none),(none,none)), publicBase q₂ (.ticket q₁) child⟩ :
      TM2.Cfg (fun _ : Bank => Bool) _ _) t
  rw [hr] at h
  exact ⟨t, ht, by simpa [liftedPreparedProgram, oldIndex,
    BitMachineStackEmbedding.stackCfg, ticketReady,
    ticketAfterCopies] using h⟩

def ticketStart : CodeAtomCountInput.Label :=
  BitMachineRawSequence.leftLabel
    (BitMachineRawSequence.leftLabel CodeAtomCountInput.InitLabel.write)

def preparedStart :
    BitMachineRawSequence.Label
      (BitMachineRawSequence.Label TerminatorLabel BitMachineCopy.Label)
      (BitMachineRawSequence.Label CodeConstructorMachine.Label
        CodeCopiesMachine.Label) :=
  BitMachineRawSequence.leftLabel
    (BitMachineRawSequence.leftLabel TerminatorLabel.write)

def ticketThenPreparedProgram :=
  BitMachineRawSequence.program ticketProgram liftedPreparedProgram
    preparedStart
    ((((),none),()) : CodeAtomCountInput.Control)
    ((((),none),(none,none)) :
      BitMachineRawSequence.Control
        (BitMachineRawSequence.Control Unit (Option Bool))
        (BitMachineRawSequence.Control CodeConstructorMachine.Control
          CodeCopiesMachine.Control))

/-- One fixed physical controller from public delimiter-free `true^q₁`,
`true^q₂` and serialized child: materialize ticket q₁, materialize a
terminated *working* q₂ word while retaining the public count, append the
child, and create all q₂ copies. The outer s ticket and append are next. -/
theorem ticket_then_prepared_run (q₁ q₂ : Nat) (child : Code) :
    ∃ t ≤ (2*q₁+8) + (2*q₂+5 +
      CodeConstructorMachine.appendClock
        (encodeCode (.ticket q₁)) (encodeCode child) +
      CodeCopiesMachine.clock q₂ (.append (.ticket q₁) child) + 2) + 1,
      ((advance ticketThenPreparedProgram)^[t])
        (⟨some (BitMachineRawSequence.leftLabel ticketStart),
          ((((),none),()),(((),none),(none,none))),
          ticketBefore q₁ q₂ child⟩ :
          TM2.Cfg (fun _ : TicketBank => Bool) _ _) =
        ⟨none, ((((),none),()),(((),none),(none,none))),
          ticketAfterCopies q₁ q₂ child⟩ := by
  obtain ⟨ta,hta,ha⟩ := ticket_run q₁ q₂ child
  obtain ⟨tb,htb,hb⟩ := lifted_prepared_run q₁ q₂ child
  have ha' :
      ((advance ticketProgram)^[ta])
        (⟨some ticketStart, (((),none),()), ticketBefore q₁ q₂ child⟩ :
          TM2.Cfg (fun _ : TicketBank => Bool)
            CodeAtomCountInput.Label CodeAtomCountInput.Control) =
        ⟨none, (((),none),()), ticketReady q₁ q₂ child⟩ := by
    simpa [ticketStart, CodeAtomCountInput.initial,
      CodeAtomCountInput.final] using ha
  obtain ⟨t,ht,hr⟩ := BitMachineRawSequence.runs
    ticketProgram liftedPreparedProgram ticketStart preparedStart
    (((),none),()) (((),none),())
    (((),none),(none,none)) (((),none),(none,none))
    (ticketBefore q₁ q₂ child) (ticketReady q₁ q₂ child)
    (ticketAfterCopies q₁ q₂ child) ta tb ha' hb
  exact ⟨t, by omega, hr⟩

abbrev TemplateBank := Fin 18

def embedTicketBank : TicketBank ↪ TemplateBank where
  toFun i := ⟨i.val, by omega⟩
  inj' := by
    intro a b h
    exact Fin.ext (Fin.mk.inj h)

def templateForeign (s : Nat) : TemplateBank → List Bool :=
  fun i => if i = 17 then List.replicate s true else []

noncomputable def templateBefore (s q₁ q₂ : Nat) (child : Code) :
    TemplateBank → List Bool :=
  BitMachineStackEmbedding.bank embedTicketBank (templateForeign s)
    (ticketBefore q₁ q₂ child)

noncomputable def templateAfterCopies (s q₁ q₂ : Nat) (child : Code) :
    TemplateBank → List Bool :=
  BitMachineStackEmbedding.bank embedTicketBank (templateForeign s)
    (ticketAfterCopies q₁ q₂ child)

noncomputable def templateAfterTicket (s q₁ q₂ : Nat) (child : Code) :
    TemplateBank → List Bool :=
  Function.update (templateAfterCopies s q₁ q₂ child)
    (5 : TemplateBank) (encodeCode (.ticket s))

noncomputable def templateAfterAppend (s q₁ q₂ : Nat) (child : Code) :
    TemplateBank → List Bool :=
  Function.update (templateAfterTicket s q₁ q₂ child)
    (14 : TemplateBank)
    (encodeCode (templateRowCode q₁ q₂ s child))

def ticketSIndex : Fin 3 ↪ TemplateBank where
  toFun i := ![17,5,6] i
  inj' := by
    intro a b h
    fin_cases a <;> fin_cases b <;> simp_all

def outerAppendIndex : Fin 8 ↪ TemplateBank where
  toFun i := ![5,4,8,9,10,11,14,6] i
  inj' := by
    intro a b h
    fin_cases a <;> fin_cases b <;> simp_all

theorem template_count_at (s q₁ q₂ : Nat) (child : Code) :
    templateAfterCopies s q₁ q₂ child 17 = List.replicate s true := by
  have hnot : ¬ ∃ i : TicketBank, embedTicketBank i = (17 : TemplateBank) := by
    rintro ⟨i,hi⟩
    have hv : i.val = 17 := by
      simpa [embedTicketBank] using congrArg Fin.val hi
    omega
  rw [templateAfterCopies,
    BitMachineStackEmbedding.bank_outside embedTicketBank
      (templateForeign s) _ 17 hnot]
  rfl

theorem template_old_at (s q₁ q₂ : Nat) (child : Code)
    (i : Bank) :
    templateAfterCopies s q₁ q₂ child
      (⟨i.val, by omega⟩ : TemplateBank) =
      innerFinal q₂ (.ticket q₁) child i := by
  change templateAfterCopies s q₁ q₂ child
    (embedTicketBank (embedOld i)) = _
  rw [templateAfterCopies, BitMachineStackEmbedding.bank_at,
    ticketAfterCopies, BitMachineStackEmbedding.bank_at]

theorem template_before_old_at (s q₁ q₂ : Nat) (child : Code)
    (i : Bank) :
    templateBefore s q₁ q₂ child
      (⟨i.val, by omega⟩ : TemplateBank) =
      (Function.update (publicBase q₂ (.ticket q₁) child)
        (1 : Bank) []) i := by
  change templateBefore s q₁ q₂ child
    (embedTicketBank (embedOld i)) = _
  rw [templateBefore, BitMachineStackEmbedding.bank_at,
    ticketBefore, BitMachineStackEmbedding.bank_at]

theorem ticket_s_initial_bank (s q₁ q₂ : Nat) (child : Code) :
    BitMachineStackEmbedding.bank ticketSIndex
      (templateAfterCopies s q₁ q₂ child)
      (CodeAtomCountInput.initial s).stk =
      templateAfterCopies s q₁ q₂ child := by
  apply BitMachineStackEmbedding.bank_eq_self
  intro i
  fin_cases i
  · change List.replicate s true = templateAfterCopies s q₁ q₂ child 17
    exact (template_count_at s q₁ q₂ child).symm
  · change ([] : List Bool) = templateAfterCopies s q₁ q₂ child 5
    have h5 : templateAfterCopies s q₁ q₂ child 5 =
        innerFinal q₂ (.ticket q₁) child 5 := by
      simpa using template_old_at s q₁ q₂ child (5 : Bank)
    rw [h5]
    simp [innerFinal, innerFirst, innerBase]
  · change ([] : List Bool) = templateAfterCopies s q₁ q₂ child 6
    have h6 : templateAfterCopies s q₁ q₂ child 6 =
        innerFinal q₂ (.ticket q₁) child 6 := by
      simpa using template_old_at s q₁ q₂ child (6 : Bank)
    rw [h6]
    simp [innerFinal, innerFirst, innerBase]

theorem ticket_s_result_bank (s q₁ q₂ : Nat) (child : Code) :
    BitMachineStackEmbedding.bank ticketSIndex
      (templateAfterCopies s q₁ q₂ child)
      (CodeAtomCountInput.final s).stk =
      templateAfterTicket s q₁ q₂ child := by
  have hstk : (CodeAtomCountInput.final s).stk =
      Function.update (CodeAtomCountInput.initial s).stk
        (1 : Fin 3) (encodeCode (.ticket s)) := by
    funext i
    fin_cases i <;> rfl
  rw [hstk, BitMachineStackEmbedding.bank_update,
    ticket_s_initial_bank]
  rfl

def ticketSProgram : CodeAtomCountInput.Label →
    TM2.Stmt (fun _ : TemplateBank => Bool)
      CodeAtomCountInput.Label CodeAtomCountInput.Control :=
  fun l => BitMachineStackEmbedding.stackStmt ticketSIndex
    (CodeAtomCountInput.program l)

theorem ticket_s_run (s q₁ q₂ : Nat) (child : Code) :
    ∃ t ≤ 2*s+8,
      ((advance ticketSProgram)^[t])
        (⟨some ticketStart, (((),none),()),
          templateAfterCopies s q₁ q₂ child⟩ :
          TM2.Cfg (fun _ : TemplateBank => Bool)
            CodeAtomCountInput.Label CodeAtomCountInput.Control) =
        ⟨none, (((),none),()),
          templateAfterTicket s q₁ q₂ child⟩ := by
  obtain ⟨t,ht,hr⟩ := CodeAtomCountInput.run_ticket_count s
  have h := BitMachineStackRun.run ticketSIndex
    (templateAfterCopies s q₁ q₂ child) CodeAtomCountInput.program
    (CodeAtomCountInput.initial s) t
  rw [hr] at h
  refine ⟨t, ht, ?_⟩
  simpa only [ticketSProgram, BitMachineStackEmbedding.stackCfg,
    ticket_s_initial_bank, ticket_s_result_bank,
    ticketStart] using h

theorem template_after_old_at (s q₁ q₂ : Nat) (child : Code)
    (i : Bank) (hi : i ≠ (5 : Bank)) :
    templateAfterTicket s q₁ q₂ child
      (⟨i.val, by omega⟩ : TemplateBank) =
      innerFinal q₂ (.ticket q₁) child i := by
  have hne : (⟨i.val, by omega⟩ : TemplateBank) ≠ 5 := by
    intro h
    apply hi
    apply Fin.ext
    simpa using congrArg Fin.val h
  rw [templateAfterTicket, Function.update_of_ne hne]
  exact template_old_at s q₁ q₂ child i

private theorem template_after_ticket_at (s q₁ q₂ : Nat) (child : Code) :
    templateAfterTicket s q₁ q₂ child 5 = encodeCode (.ticket s) := by
  simp [templateAfterTicket]

theorem outer_append_initial_bank (s q₁ q₂ : Nat) (child : Code) :
    BitMachineStackEmbedding.bank outerAppendIndex
      (templateAfterTicket s q₁ q₂ child)
      (CodeConstructorMachine.cfg (some .appendRightCopy) none
        (CodeConstructorMachine.appendInputs (.ticket s)
          (copies q₂ (.append (.ticket q₁) child))) [] []).stk =
      templateAfterTicket s q₁ q₂ child := by
  apply BitMachineStackEmbedding.bank_eq_self
  intro i
  fin_cases i
  · change encodeCode (.ticket s) = templateAfterTicket s q₁ q₂ child 5
    exact (template_after_ticket_at s q₁ q₂ child).symm
  · change encodeCode (copies q₂ (.append (.ticket q₁) child)) =
      templateAfterTicket s q₁ q₂ child 4
    have h := template_after_old_at s q₁ q₂ child (4 : Bank) (by decide)
    have h4 : templateAfterTicket s q₁ q₂ child 4 =
        innerFinal q₂ (.ticket q₁) child 4 := by simpa using h
    rw [h4]
    simp [innerFinal]
  · change ([] : List Bool) = templateAfterTicket s q₁ q₂ child 8
    have h := template_after_old_at s q₁ q₂ child (8 : Bank) (by decide)
    have h8 : templateAfterTicket s q₁ q₂ child 8 =
        innerFinal q₂ (.ticket q₁) child 8 := by simpa using h
    rw [h8]
    simp [innerFinal, innerFirst, innerBase]
  · change ([] : List Bool) = templateAfterTicket s q₁ q₂ child 9
    have h := template_after_old_at s q₁ q₂ child (9 : Bank) (by decide)
    have h9 : templateAfterTicket s q₁ q₂ child 9 =
        innerFinal q₂ (.ticket q₁) child 9 := by simpa using h
    rw [h9]
    simp [innerFinal, innerFirst, innerBase]
  · change ([] : List Bool) = templateAfterTicket s q₁ q₂ child 10
    have h := template_after_old_at s q₁ q₂ child (10 : Bank) (by decide)
    have h10 : templateAfterTicket s q₁ q₂ child 10 =
        innerFinal q₂ (.ticket q₁) child 10 := by simpa using h
    rw [h10]
    simp [innerFinal, innerFirst, innerBase]
  · change ([] : List Bool) = templateAfterTicket s q₁ q₂ child 11
    have h := template_after_old_at s q₁ q₂ child (11 : Bank) (by decide)
    have h11 : templateAfterTicket s q₁ q₂ child 11 =
        innerFinal q₂ (.ticket q₁) child 11 := by simpa using h
    rw [h11]
    simp [innerFinal, innerFirst, innerBase]
  · change ([] : List Bool) = templateAfterTicket s q₁ q₂ child 14
    have h := template_after_old_at s q₁ q₂ child (14 : Bank) (by decide)
    have h14 : templateAfterTicket s q₁ q₂ child 14 =
        innerFinal q₂ (.ticket q₁) child 14 := by simpa using h
    rw [h14]
    simp [innerFinal, innerFirst, innerBase]
  · change ([] : List Bool) = templateAfterTicket s q₁ q₂ child 6
    have h := template_after_old_at s q₁ q₂ child (6 : Bank) (by decide)
    have h6 : templateAfterTicket s q₁ q₂ child 6 =
        innerFinal q₂ (.ticket q₁) child 6 := by simpa using h
    rw [h6]
    simp [innerFinal, innerFirst, innerBase]

theorem outer_append_result_bank (s q₁ q₂ : Nat) (child : Code) :
    BitMachineStackEmbedding.bank outerAppendIndex
      (templateAfterTicket s q₁ q₂ child)
      (CodeConstructorMachine.cfg none none
        (CodeConstructorMachine.appendInputs (.ticket s)
          (copies q₂ (.append (.ticket q₁) child)))
        (encodeCode (templateRowCode q₁ q₂ s child)) []).stk =
      templateAfterAppend s q₁ q₂ child := by
  have hstk :
      (CodeConstructorMachine.cfg none none
        (CodeConstructorMachine.appendInputs (.ticket s)
          (copies q₂ (.append (.ticket q₁) child)))
        (encodeCode (templateRowCode q₁ q₂ s child)) []).stk =
      Function.update
        (CodeConstructorMachine.cfg (some .appendRightCopy) none
          (CodeConstructorMachine.appendInputs (.ticket s)
            (copies q₂ (.append (.ticket q₁) child))) [] []).stk
        (6 : Fin 8) (encodeCode (templateRowCode q₁ q₂ s child)) := by
    funext i
    fin_cases i <;> rfl
  rw [hstk, BitMachineStackEmbedding.bank_update,
    outer_append_initial_bank]
  rfl

def outerAppendProgram : CodeConstructorMachine.Label →
    TM2.Stmt (fun _ : TemplateBank => Bool)
      CodeConstructorMachine.Label CodeConstructorMachine.Control :=
  fun l => BitMachineStackEmbedding.stackStmt outerAppendIndex
    (CodeConstructorMachine.program l)

theorem outer_append_run (s q₁ q₂ : Nat) (child : Code) :
    ((advance outerAppendProgram)^[CodeConstructorMachine.appendClock
      (encodeCode (.ticket s))
      (encodeCode (copies q₂ (.append (.ticket q₁) child)))])
      (⟨some .appendRightCopy, none,
        templateAfterTicket s q₁ q₂ child⟩ :
        TM2.Cfg (fun _ : TemplateBank => Bool)
          CodeConstructorMachine.Label CodeConstructorMachine.Control) =
      ⟨none, none, templateAfterAppend s q₁ q₂ child⟩ := by
  have h := BitMachineStackRun.run outerAppendIndex
    (templateAfterTicket s q₁ q₂ child) CodeConstructorMachine.program
    (CodeConstructorMachine.cfg (some .appendRightCopy) none
      (CodeConstructorMachine.appendInputs (.ticket s)
        (copies q₂ (.append (.ticket q₁) child))) [] [])
    (CodeConstructorMachine.appendClock
      (encodeCode (.ticket s))
      (encodeCode (copies q₂ (.append (.ticket q₁) child))))
  rw [← CodeConstructorMachine.run,
    CodeConstructorMachine.run_append] at h
  have hword : encodeCode (.append (.ticket s)
      (copies q₂ (.append (.ticket q₁) child))) =
      encodeCode (templateRowCode q₁ q₂ s child) := rfl
  rw [hword] at h
  simpa only [outerAppendProgram, BitMachineStackEmbedding.stackCfg,
    outer_append_initial_bank, outer_append_result_bank] using h

def liftedCoreProgram :=
  fun l => BitMachineStackEmbedding.stackStmt embedTicketBank
    (ticketThenPreparedProgram l)

theorem lifted_core_run (s q₁ q₂ : Nat) (child : Code) :
    ∃ t ≤ (2*q₁+8) + (2*q₂+5 +
      CodeConstructorMachine.appendClock
        (encodeCode (.ticket q₁)) (encodeCode child) +
      CodeCopiesMachine.clock q₂ (.append (.ticket q₁) child) + 2) + 1,
      ((advance liftedCoreProgram)^[t])
        (⟨some (BitMachineRawSequence.leftLabel ticketStart),
          ((((),none),()),(((),none),(none,none))),
          templateBefore s q₁ q₂ child⟩ :
          TM2.Cfg (fun _ : TemplateBank => Bool) _ _) =
        ⟨none, ((((),none),()),(((),none),(none,none))),
          templateAfterCopies s q₁ q₂ child⟩ := by
  obtain ⟨t,ht,hr⟩ := ticket_then_prepared_run q₁ q₂ child
  have h := BitMachineStackRun.run embedTicketBank (templateForeign s)
    ticketThenPreparedProgram
    (⟨some (BitMachineRawSequence.leftLabel ticketStart),
      ((((),none),()),(((),none),(none,none))),
      ticketBefore q₁ q₂ child⟩ :
      TM2.Cfg (fun _ : TicketBank => Bool) _ _) t
  rw [hr] at h
  exact ⟨t, ht, by simpa [liftedCoreProgram,
    BitMachineStackEmbedding.stackCfg,
    templateBefore, templateAfterCopies] using h⟩

abbrev PreparedLabel :=
  BitMachineRawSequence.Label
    (BitMachineRawSequence.Label TerminatorLabel BitMachineCopy.Label)
    (BitMachineRawSequence.Label CodeConstructorMachine.Label
      CodeCopiesMachine.Label)

abbrev PreparedControl :=
  BitMachineRawSequence.Control
    (BitMachineRawSequence.Control Unit (Option Bool))
    (BitMachineRawSequence.Control CodeConstructorMachine.Control
      CodeCopiesMachine.Control)

abbrev CoreLabel :=
  BitMachineRawSequence.Label CodeAtomCountInput.Label PreparedLabel

abbrev CoreControl :=
  BitMachineRawSequence.Control CodeAtomCountInput.Control PreparedControl

def coreStart : CoreLabel := BitMachineRawSequence.leftLabel ticketStart

def coreControl : CoreControl :=
  ((((),none),()),(((),none),(none,none)))

def ticketControl : CodeAtomCountInput.Control := (((),none),())

def coreTicketControl : BitMachineRawSequence.Control
    CoreControl CodeAtomCountInput.Control :=
  (coreControl,ticketControl)

def coreTicketProgram :=
  BitMachineRawSequence.program liftedCoreProgram ticketSProgram
    ticketStart coreControl ticketControl

theorem core_ticket_run (s q₁ q₂ : Nat) (child : Code) :
    ∃ t ≤ ((2*q₁+8) + (2*q₂+5 +
      CodeConstructorMachine.appendClock
        (encodeCode (.ticket q₁)) (encodeCode child) +
      CodeCopiesMachine.clock q₂ (.append (.ticket q₁) child) + 2) + 1) +
      (2*s+8) + 1,
      ((advance coreTicketProgram)^[t])
        (⟨some (BitMachineRawSequence.leftLabel coreStart),
          coreTicketControl,
          templateBefore s q₁ q₂ child⟩ :
          TM2.Cfg (fun _ : TemplateBank => Bool) _ _) =
        ⟨none, coreTicketControl,
          templateAfterTicket s q₁ q₂ child⟩ := by
  obtain ⟨ta,hta,ha⟩ := lifted_core_run s q₁ q₂ child
  obtain ⟨tb,htb,hb⟩ := ticket_s_run s q₁ q₂ child
  obtain ⟨t,ht,hr⟩ := BitMachineRawSequence.runs
    liftedCoreProgram ticketSProgram coreStart ticketStart
    coreControl coreControl ticketControl ticketControl
    (templateBefore s q₁ q₂ child)
    (templateAfterCopies s q₁ q₂ child)
    (templateAfterTicket s q₁ q₂ child) ta tb ha hb
  exact ⟨t, by omega, hr⟩

def templateRowProgram :=
  BitMachineRawSequence.program coreTicketProgram outerAppendProgram
    CodeConstructorMachine.Label.appendRightCopy
    coreTicketControl (none : CodeConstructorMachine.Control)

def templateRowClock (s q₁ q₂ : Nat) (child : Code) : Nat :=
  ((2*q₁+8) + (2*q₂+5 +
    CodeConstructorMachine.appendClock
      (encodeCode (.ticket q₁)) (encodeCode child) +
    CodeCopiesMachine.clock q₂ (.append (.ticket q₁) child) + 2) + 1) +
    (2*s+8) + 1 +
    CodeConstructorMachine.appendClock
      (encodeCode (.ticket s))
      (encodeCode (copies q₂ (.append (.ticket q₁) child))) + 1

/-- First complete physical compiler milestone. A single fixed, finite
controller starts with delimiter-free count cells `true^s`, `true^q₁`,
`true^q₂`, plus the child serialization; it creates the exact production
`templateRowCode` serialization on bank 14. Intermediate ticket, append,
terminated working count, and copies words are all constructed by its
physical phases. -/
theorem template_row_run (s q₁ q₂ : Nat) (child : Code) :
    ∃ t ≤ templateRowClock s q₁ q₂ child,
      ((advance templateRowProgram)^[t])
        (⟨some (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel coreStart)),
          (coreTicketControl,none), templateBefore s q₁ q₂ child⟩ :
          TM2.Cfg (fun _ : TemplateBank => Bool) _ _) =
        ⟨none, (coreTicketControl,none),
          templateAfterAppend s q₁ q₂ child⟩ := by
  obtain ⟨ta,hta,ha⟩ := core_ticket_run s q₁ q₂ child
  have hb := outer_append_run s q₁ q₂ child
  obtain ⟨t,ht,hr⟩ := BitMachineRawSequence.runs
    coreTicketProgram outerAppendProgram
    (BitMachineRawSequence.leftLabel coreStart)
    CodeConstructorMachine.Label.appendRightCopy
    coreTicketControl coreTicketControl none none
    (templateBefore s q₁ q₂ child)
    (templateAfterTicket s q₁ q₂ child)
    (templateAfterAppend s q₁ q₂ child) ta
    (CodeConstructorMachine.appendClock
      (encodeCode (.ticket s))
      (encodeCode (copies q₂ (.append (.ticket q₁) child))))
    ha hb
  exact ⟨t, by dsimp [templateRowClock]; omega, hr⟩

theorem template_row_output (s q₁ q₂ : Nat) (child : Code) :
    templateAfterAppend s q₁ q₂ child 14 =
      encodeCode (templateRowCode q₁ q₂ s child) := by
  simp [templateAfterAppend]

theorem template_final_old_at (s q₁ q₂ : Nat) (child : Code)
    (i : Bank) (h5 : i ≠ 5) (h14 : i ≠ 14) :
    templateAfterAppend s q₁ q₂ child
      (⟨i.val, by omega⟩ : TemplateBank) =
      innerFinal q₂ (.ticket q₁) child i := by
  have hne : (⟨i.val, by omega⟩ : TemplateBank) ≠ 14 := by
    intro h
    apply h14
    apply Fin.ext
    simpa using congrArg Fin.val h
  rw [templateAfterAppend, Function.update_of_ne hne]
  exact template_after_old_at s q₁ q₂ child i h5

theorem template_row_retains_s (s q₁ q₂ : Nat) (child : Code) :
    templateAfterAppend s q₁ q₂ child 17 = List.replicate s true := by
  simp only [templateAfterAppend, templateAfterTicket,
    Function.update_of_ne (by decide : (17 : TemplateBank) ≠ 14),
    Function.update_of_ne (by decide : (17 : TemplateBank) ≠ 5)]
  exact template_count_at s q₁ q₂ child

theorem template_row_retains_q₁ (s q₁ q₂ : Nat) (child : Code) :
    templateAfterAppend s q₁ q₂ child 16 = List.replicate q₁ true := by
  simp only [templateAfterAppend, templateAfterTicket,
    Function.update_of_ne (by decide : (16 : TemplateBank) ≠ 14),
    Function.update_of_ne (by decide : (16 : TemplateBank) ≠ 5)]
  have hnot : ¬ ∃ i : Bank, embedOld i = (16 : TicketBank) := by
    rintro ⟨i,hi⟩
    have hv : i.val = 16 := by
      simpa [embedOld] using congrArg Fin.val hi
    omega
  change BitMachineStackEmbedding.bank embedTicketBank (templateForeign s)
      (ticketAfterCopies q₁ q₂ child) (embedTicketBank 16) = _
  rw [BitMachineStackEmbedding.bank_at]
  change BitMachineStackEmbedding.bank embedOld (ticketForeign q₁)
      (innerFinal q₂ (.ticket q₁) child) 16 = _
  rw [BitMachineStackEmbedding.bank_outside
    embedOld (ticketForeign q₁) _ 16 hnot]
  rfl

theorem template_row_retains_q₂ (s q₁ q₂ : Nat) (child : Code) :
    templateAfterAppend s q₁ q₂ child 12 = List.replicate q₂ true := by
  have h := template_final_old_at s q₁ q₂ child (12 : Bank)
    (by decide) (by decide)
  have h12 : templateAfterAppend s q₁ q₂ child 12 =
      innerFinal q₂ (.ticket q₁) child 12 := by simpa using h
  rw [h12]
  simp [innerFinal, innerFirst, innerBase]

theorem template_row_retains_child (s q₁ q₂ : Nat) (child : Code) :
    templateAfterAppend s q₁ q₂ child 2 = encodeCode child := by
  have h := template_final_old_at s q₁ q₂ child (2 : Bank)
    (by decide) (by decide)
  have h2 : templateAfterAppend s q₁ q₂ child 2 =
      innerFinal q₂ (.ticket q₁) child 2 := by simpa using h
  rw [h2]
  simp [innerFinal, innerFirst, innerBase]

theorem template_row_clears_scratch (s q₁ q₂ : Nat) (child : Code) :
    templateAfterAppend s q₁ q₂ child 6 = [] := by
  have h := template_final_old_at s q₁ q₂ child (6 : Bank)
    (by decide) (by decide)
  have h6 : templateAfterAppend s q₁ q₂ child 6 =
      innerFinal q₂ (.ticket q₁) child 6 := by simpa using h
  rw [h6]
  simp [innerFinal, innerFirst, innerBase]

/-- The one-controller clock is linear in explicit input counts, child
serialization, and the actual emitted syntax word. -/
theorem template_row_clock_linear (s q₁ q₂ : Nat) (child : Code) :
    templateRowClock s q₁ q₂ child ≤
      8 * (s + q₁ + q₂ + codeSize child +
        codeSize (templateRowCode q₁ q₂ s child) + 1) := by
  let c := codeSize child
  let a := codeSize (copies q₂ (.append (.ticket q₁) child))
  have ha : a = 4 + q₂ * (q₁ + c + 10) := by
    dsimp [a]
    rw [CodeCopiesMachine.codeSize_copies]
    change 4 + q₂ * (3 + (3 + (3 + (q₁ + 1)) + codeSize child)) =
      4 + q₂ * (q₁ + c + 10)
    dsimp [c]
    ring
  have ht : codeSize (templateRowCode q₁ q₂ s child) = s + 7 + a := by
    change 3 + (3 + (s + 1)) + a = s + 7 + a
    omega
  have hm : q₂ * (2 * (q₁ + c + 7) + 4) ≤
      2 * q₂ * (q₁ + c + 10) := by
    nlinarith
  have hinner : CodeConstructorMachine.appendClock
      (encodeCode (.ticket q₁)) (encodeCode child) =
      2 * (q₁ + 4 + c) + 6 := by
    rw [CodeConstructorMachine.appendClock,
      encodeCode_length, encodeCode_length]
    change 2 * ((3 + (q₁ + 1)) + codeSize child) + 6 =
      2 * (q₁ + 4 + c) + 6
    dsimp [c]
    omega
  have hcopies : CodeCopiesMachine.clock q₂
      (.append (.ticket q₁) child) =
      3 + q₂ * (2 * (q₁ + c + 7) + 4) := by
    change 3 + q₂ *
      (2 * (3 + (3 + (q₁ + 1)) + codeSize child) + 4) =
      3 + q₂ * (2 * (q₁ + c + 7) + 4)
    dsimp [c]
    ring
  have houter : CodeConstructorMachine.appendClock
      (encodeCode (.ticket s))
      (encodeCode (copies q₂ (.append (.ticket q₁) child))) =
      2 * (s + 4 + a) + 6 := by
    rw [CodeConstructorMachine.appendClock,
      encodeCode_length, encodeCode_length]
    change 2 * ((3 + (s + 1)) + a) + 6 =
      2 * (s + 4 + a) + 6
    omega
  dsimp [templateRowClock]
  rw [hinner, hcopies, houter, ht]
  nlinarith [ha, hm]

#print axioms template_row_run
#print axioms template_row_clock_linear
#print axioms template_row_output

end Paper2.CodeRowsJoin
