import Paper2.CodeRecursiveRow

/-! One fixed controller for both actual successor codes. The left-associated
phase sequence is a physical inlining, not a list of independent machines. -/

set_option maxHeartbeats 1000000
set_option maxRecDepth 8192

namespace Paper2.CodeRecursiveStep

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open Paper2.GeneratorCode Paper2.GeneratorSerialization
open Paper2.GeneratorSource Paper2.CodeRecursiveColumn
open Paper2.CodeRecursiveRow

abbrev ColLabel :=
  BitMachineRawSequence.Label
    (BitMachineRawSequence.Label
      (BitMachineRawSequence.Label
        (BitMachineRawSequence.Label RowLabel
          (BitMachineRawSequence.Label
            CodeRecursiveColumn.DelimiterLabel BitMachineCopy.Label))
        CodeAtomCountInput.Label)
      CodeCopiesMachine.Label)
    CodeConstructorMachine.Label

abbrev ColControl :=
  BitMachineRawSequence.Control
    (BitMachineRawSequence.Control
      (BitMachineRawSequence.Control
        (BitMachineRawSequence.Control RowControl
          CodeRawCountTerm.Control)
        CodeAtomCountInput.Control)
      CodeCopiesMachine.Control)
    CodeConstructorMachine.Control

def colStart : ColLabel :=
  BitMachineRawSequence.leftLabel
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel rowStart)))

def colControl : ColControl :=
  ((((rowControl,((),none)),(((),none),())),none),none)

abbrev TermControl := CodeRawCountTerm.Control
def termControl : TermControl := ((),none)
def termStart : CodeRawCountTerm.Label :=
  BitMachineRawSequence.leftLabel
    CodeRawCountTerm.DelimiterLabel.write

def p₁ :=
  BitMachineRawSequence.program CodeRecursiveColumn.program
    q₁TermProgram termStart colControl termControl

def b₁ (n s q₁ q₂ w Q : Nat) (previousRow : Code) : Nat :=
  CodeRecursiveColumn.clockBound n s q₁ q₂ w Q previousRow +
    (2*q₁+5)+1

theorem p₁_run (n s q₁ q₂ w Q : Nat)
    (previousRow previousCol : Code) (hs : 3 ≤ s) :
    ∃ t ≤ b₁ n s q₁ q₂ w Q previousRow,
      ((advance p₁)^[t])
        (⟨some (BitMachineRawSequence.leftLabel colStart),
          (colControl,termControl),
          initial n s q₁ q₂ w Q previousRow previousCol⟩ :
          TM2.Cfg (fun _ : Stack => Bool) _ _) =
        ⟨none, (colControl,termControl),
          afterQ₁Term n s q₁ q₂ w Q previousRow previousCol⟩ := by
  obtain ⟨ta,hta,ha⟩ := CodeRecursiveColumn.run_exact
    n s q₁ q₂ w Q previousRow previousCol hs
  obtain ⟨tb,htb,hb⟩ := q₁_term_run
    n s q₁ q₂ w Q previousRow previousCol
  obtain ⟨t,ht,hr⟩ := BitMachineRawSequence.runs
    CodeRecursiveColumn.program q₁TermProgram
    colStart termStart colControl colControl
    termControl termControl
    (initial n s q₁ q₂ w Q previousRow previousCol)
    (afterColumn n s q₁ q₂ w Q previousRow previousCol)
    (afterQ₁Term n s q₁ q₂ w Q previousRow previousCol)
    ta tb ha hb
  exact ⟨t, by dsimp [b₁]; omega, hr⟩

def p₂ :=
  BitMachineRawSequence.program p₁ q₂TermProgram
    termStart (colControl,termControl) termControl

def b₂ (n s q₁ q₂ w Q : Nat) (previousRow : Code) : Nat :=
  b₁ n s q₁ q₂ w Q previousRow + (2*q₂+5)+1

theorem p₂_run (n s q₁ q₂ w Q : Nat)
    (previousRow previousCol : Code) (hs : 3 ≤ s) :
    ∃ t ≤ b₂ n s q₁ q₂ w Q previousRow,
      ((advance p₂)^[t])
        (⟨some (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel colStart)),
          ((colControl,termControl),termControl),
          initial n s q₁ q₂ w Q previousRow previousCol⟩ :
          TM2.Cfg (fun _ : Stack => Bool) _ _) =
        ⟨none, ((colControl,termControl),termControl),
          afterQ₂Term n s q₁ q₂ w Q previousRow previousCol⟩ := by
  obtain ⟨ta,hta,ha⟩ := p₁_run
    n s q₁ q₂ w Q previousRow previousCol hs
  obtain ⟨tb,htb,hb⟩ := q₂_term_run
    n s q₁ q₂ w Q previousRow previousCol
  obtain ⟨t,ht,hr⟩ := BitMachineRawSequence.runs
    p₁ q₂TermProgram
    (BitMachineRawSequence.leftLabel colStart) termStart
    (colControl,termControl) (colControl,termControl)
    termControl termControl
    (initial n s q₁ q₂ w Q previousRow previousCol)
    (afterQ₁Term n s q₁ q₂ w Q previousRow previousCol)
    (afterQ₂Term n s q₁ q₂ w Q previousRow previousCol)
    ta tb ha hb
  exact ⟨t, by dsimp [b₂]; omega, hr⟩

def p₃ :=
  BitMachineRawSequence.program p₂ QTermProgram
    termStart ((colControl,termControl),termControl) termControl

def b₃ (n s q₁ q₂ w Q : Nat) (previousRow : Code) : Nat :=
  b₂ n s q₁ q₂ w Q previousRow + (2*Q+5)+1

theorem p₃_run (n s q₁ q₂ w Q : Nat)
    (previousRow previousCol : Code) (hs : 3 ≤ s) :
    ∃ t ≤ b₃ n s q₁ q₂ w Q previousRow,
      ((advance p₃)^[t])
        (⟨some (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel
              (BitMachineRawSequence.leftLabel colStart))),
          (((colControl,termControl),termControl),termControl),
          initial n s q₁ q₂ w Q previousRow previousCol⟩ :
          TM2.Cfg (fun _ : Stack => Bool) _ _) =
        ⟨none,
          (((colControl,termControl),termControl),termControl),
          afterQTerm n s q₁ q₂ w Q previousRow previousCol⟩ := by
  obtain ⟨ta,hta,ha⟩ := p₂_run
    n s q₁ q₂ w Q previousRow previousCol hs
  obtain ⟨tb,htb,hb⟩ := Q_term_run
    n s q₁ q₂ w Q previousRow previousCol
  obtain ⟨t,ht,hr⟩ := BitMachineRawSequence.runs
    p₂ QTermProgram
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel colStart)) termStart
    ((colControl,termControl),termControl)
    ((colControl,termControl),termControl)
    termControl termControl
    (initial n s q₁ q₂ w Q previousRow previousCol)
    (afterQ₂Term n s q₁ q₂ w Q previousRow previousCol)
    (afterQTerm n s q₁ q₂ w Q previousRow previousCol)
    ta tb ha hb
  exact ⟨t, by dsimp [b₃]; omega, hr⟩

def p₄ :=
  BitMachineRawSequence.program p₃ embeddedTaggedProgram
    (TaggedCompiler.Label.outerInit .third)
    (((colControl,termControl),termControl),termControl) none

def b₄ (n s q₁ q₂ w Q : Nat)
    (previousRow previousCol : Code) : Nat :=
  b₃ n s q₁ q₂ w Q previousRow +
    TaggedCompiler.taggedClock q₁ q₂ s previousCol+1

theorem p₄_run (n s q₁ q₂ w Q : Nat)
    (previousRow previousCol : Code) (hs : 3 ≤ s) :
    ∃ t ≤ b₄ n s q₁ q₂ w Q previousRow previousCol,
      ((advance p₄)^[t])
        (⟨some (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel
              (BitMachineRawSequence.leftLabel
                (BitMachineRawSequence.leftLabel colStart)))),
          ((((colControl,termControl),termControl),termControl),none),
          initial n s q₁ q₂ w Q previousRow previousCol⟩ :
          TM2.Cfg (fun _ : Stack => Bool) _ _) =
        ⟨none,
          ((((colControl,termControl),termControl),termControl),none),
          afterTagged n s q₁ q₂ w Q previousRow previousCol⟩ := by
  obtain ⟨ta,hta,ha⟩ := p₃_run
    n s q₁ q₂ w Q previousRow previousCol hs
  obtain ⟨t,ht,hr⟩ := BitMachineRawSequence.runs
    p₃ embeddedTaggedProgram
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel colStart)))
    (TaggedCompiler.Label.outerInit .third)
    (((colControl,termControl),termControl),termControl)
    (((colControl,termControl),termControl),termControl)
    none none
    (initial n s q₁ q₂ w Q previousRow previousCol)
    (afterQTerm n s q₁ q₂ w Q previousRow previousCol)
    (afterTagged n s q₁ q₂ w Q previousRow previousCol)
    ta (TaggedCompiler.taggedClock q₁ q₂ s previousCol)
    ha (embedded_tagged_run n s q₁ q₂ w Q
      previousRow previousCol)
  exact ⟨t, by dsimp [b₄]; omega, hr⟩

def ticketStart : CodeAtomCountInput.Label :=
  BitMachineRawSequence.leftLabel
    (BitMachineRawSequence.leftLabel
      CodeAtomCountInput.InitLabel.write)
def ticketControl : CodeAtomCountInput.Control := (((),none),())

def p₅ :=
  BitMachineRawSequence.program p₄ embeddedTicketWProgram
    ticketStart
    ((((colControl,termControl),termControl),termControl),none)
    ticketControl

def b₅ (n s q₁ q₂ w Q : Nat)
    (previousRow previousCol : Code) : Nat :=
  b₄ n s q₁ q₂ w Q previousRow previousCol + (2*w+8)+1

theorem p₅_run (n s q₁ q₂ w Q : Nat)
    (previousRow previousCol : Code) (hs : 3 ≤ s) :
    ∃ t ≤ b₅ n s q₁ q₂ w Q previousRow previousCol,
      ((advance p₅)^[t])
        (⟨some (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel
              (BitMachineRawSequence.leftLabel
                (BitMachineRawSequence.leftLabel
                  (BitMachineRawSequence.leftLabel colStart))))),
          (((((colControl,termControl),termControl),termControl),none),
            ticketControl),
          initial n s q₁ q₂ w Q previousRow previousCol⟩ :
          TM2.Cfg (fun _ : Stack => Bool) _ _) =
        ⟨none,
          (((((colControl,termControl),termControl),termControl),none),
            ticketControl),
          afterTicketW n s q₁ q₂ w Q previousRow previousCol⟩ := by
  obtain ⟨ta,hta,ha⟩ := p₄_run
    n s q₁ q₂ w Q previousRow previousCol hs
  obtain ⟨tb,htb,hb⟩ := embedded_ticket_w_run
    n s q₁ q₂ w Q previousRow previousCol
  obtain ⟨t,ht,hr⟩ := BitMachineRawSequence.runs
    p₄ embeddedTicketWProgram
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel colStart))))
    ticketStart
    ((((colControl,termControl),termControl),termControl),none)
    ((((colControl,termControl),termControl),termControl),none)
    ticketControl ticketControl
    (initial n s q₁ q₂ w Q previousRow previousCol)
    (afterTagged n s q₁ q₂ w Q previousRow previousCol)
    (afterTicketW n s q₁ q₂ w Q previousRow previousCol)
    ta tb ha hb
  exact ⟨t, by dsimp [b₅]; omega, hr⟩

def p₆ :=
  BitMachineRawSequence.program p₅ CodeRecursiveRow.embeddedAppendProgram
    CodeConstructorMachine.Label.appendRightCopy
    (((((colControl,termControl),termControl),termControl),none),
      ticketControl) none

def b₆ (n s q₁ q₂ w Q : Nat)
    (previousRow previousCol : Code) : Nat :=
  b₅ n s q₁ q₂ w Q previousRow previousCol +
    CodeConstructorMachine.appendClock
      (encodeCode (.ticket w))
      (encodeCode (taggedCode q₁ q₂ s previousCol))+1

theorem p₆_run (n s q₁ q₂ w Q : Nat)
    (previousRow previousCol : Code) (hs : 3 ≤ s) :
    ∃ t ≤ b₆ n s q₁ q₂ w Q previousRow previousCol,
      ((advance p₆)^[t])
        (⟨some (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel
              (BitMachineRawSequence.leftLabel
                (BitMachineRawSequence.leftLabel
                  (BitMachineRawSequence.leftLabel
                    (BitMachineRawSequence.leftLabel colStart)))))),
          ((((((colControl,termControl),termControl),termControl),none),
            ticketControl),none),
          initial n s q₁ q₂ w Q previousRow previousCol⟩ :
          TM2.Cfg (fun _ : Stack => Bool) _ _) =
        ⟨none,
          ((((((colControl,termControl),termControl),termControl),none),
            ticketControl),none),
          afterRowUnit n s q₁ q₂ w Q previousRow previousCol⟩ := by
  obtain ⟨ta,hta,ha⟩ := p₅_run
    n s q₁ q₂ w Q previousRow previousCol hs
  obtain ⟨t,ht,hr⟩ := BitMachineRawSequence.runs
    p₅ CodeRecursiveRow.embeddedAppendProgram
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel colStart)))))
    CodeConstructorMachine.Label.appendRightCopy
    (((((colControl,termControl),termControl),termControl),none),
      ticketControl)
    (((((colControl,termControl),termControl),termControl),none),
      ticketControl)
    none none
    (initial n s q₁ q₂ w Q previousRow previousCol)
    (afterTicketW n s q₁ q₂ w Q previousRow previousCol)
    (afterRowUnit n s q₁ q₂ w Q previousRow previousCol)
    ta (CodeConstructorMachine.appendClock
      (encodeCode (.ticket w))
      (encodeCode (taggedCode q₁ q₂ s previousCol)))
    ha (embedded_append_run n s q₁ q₂ w Q
      previousRow previousCol)
  exact ⟨t, by dsimp [b₆]; omega, hr⟩

def program :=
  BitMachineRawSequence.program p₆ CodeRecursiveRow.embeddedCopiesProgram
    CodeCopiesMachine.Label.initialize
    ((((((colControl,termControl),termControl),termControl),none),
      ticketControl),none) none

def clockBound (n s q₁ q₂ w Q : Nat)
    (previousRow previousCol : Code) : Nat :=
  b₆ n s q₁ q₂ w Q previousRow previousCol +
    CodeCopiesMachine.clock Q (rowUnitCode q₁ q₂ s w previousCol)+1

/-- A physically charged, fixed 64-stack, finite-label TM2 run producing
both exact successor syntax words from the two actual preceding syntax words
and the six public delimiter-free count cells. -/
theorem run_exact (n s q₁ q₂ w Q : Nat)
    (previousRow previousCol : Code) (hs : 3 ≤ s) :
    ∃ t ≤ clockBound n s q₁ q₂ w Q previousRow previousCol,
      ((advance program)^[t])
        (⟨some (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel
              (BitMachineRawSequence.leftLabel
                (BitMachineRawSequence.leftLabel
                  (BitMachineRawSequence.leftLabel
                    (BitMachineRawSequence.leftLabel
                      (BitMachineRawSequence.leftLabel colStart))))))),
          (((((((colControl,termControl),termControl),termControl),none),
            ticketControl),none),none),
          initial n s q₁ q₂ w Q previousRow previousCol⟩ :
          TM2.Cfg (fun _ : Stack => Bool) _ _) =
        ⟨none,
          (((((((colControl,termControl),termControl),termControl),none),
            ticketControl),none),none),
          afterRow n s q₁ q₂ w Q previousRow previousCol⟩ := by
  obtain ⟨ta,hta,ha⟩ := p₆_run
    n s q₁ q₂ w Q previousRow previousCol hs
  obtain ⟨t,ht,hr⟩ := BitMachineRawSequence.runs
    p₆ CodeRecursiveRow.embeddedCopiesProgram
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel
              (BitMachineRawSequence.leftLabel colStart))))))
    CodeCopiesMachine.Label.initialize
    ((((((colControl,termControl),termControl),termControl),none),
      ticketControl),none)
    ((((((colControl,termControl),termControl),termControl),none),
      ticketControl),none)
    none none
    (initial n s q₁ q₂ w Q previousRow previousCol)
    (afterRowUnit n s q₁ q₂ w Q previousRow previousCol)
    (afterRow n s q₁ q₂ w Q previousRow previousCol)
    ta (CodeCopiesMachine.clock Q
      (rowUnitCode q₁ q₂ s w previousCol))
    ha (embedded_copies_run n s q₁ q₂ w Q
      previousRow previousCol)
  exact ⟨t, by dsimp [clockBound]; omega, hr⟩

theorem row_output (n s q₁ q₂ w Q : Nat)
    (previousRow previousCol : Code) :
    afterRow n s q₁ q₂ w Q previousRow previousCol 52 =
      encodeCode (rowCode q₁ q₂ s w Q previousCol) :=
  row_output_exact n s q₁ q₂ w Q previousRow previousCol

theorem column_output (n s q₁ q₂ w Q : Nat)
    (previousRow previousCol : Code) :
    afterRow n s q₁ q₂ w Q previousRow previousCol 37 =
      encodeCode (columnCode n s q₁ q₂ w Q previousRow) := by
  simp only [afterRow, afterRowUnit, afterTicketW,
    afterTagged, afterQTerm, afterQ₂Term, afterQ₁Term,
    Function.update_of_ne (by decide : (37 : Stack) ≠ 52),
    Function.update_of_ne (by decide : (37 : Stack) ≠ 48),
    Function.update_of_ne (by decide : (37 : Stack) ≠ 51),
    Function.update_of_ne (by decide : (37 : Stack) ≠ 50),
    Function.update_of_ne (by decide : (37 : Stack) ≠ 49),
    Function.update_of_ne (by decide : (37 : Stack) ≠ 47),
    Function.update_of_ne (by decide : (37 : Stack) ≠ 46)]
  exact CodeRecursiveColumn.output_exact n s q₁ q₂ w Q
    previousRow previousCol

theorem final_lower_at (n s q₁ q₂ w Q : Nat)
    (previousRow previousCol : Code) (i : Stack)
    (hi : i.val < 34) :
    afterRow n s q₁ q₂ w Q previousRow previousCol i =
      afterGraph n s q₁ q₂ w Q previousRow previousCol i := by
  have h46 : i ≠ (46 : Stack) := by
    intro h; have hv := congrArg Fin.val h; omega
  have h47 : i ≠ (47 : Stack) := by
    intro h; have hv := congrArg Fin.val h; omega
  have h48 : i ≠ (48 : Stack) := by
    intro h; have hv := congrArg Fin.val h; omega
  have h49 : i ≠ (49 : Stack) := by
    intro h; have hv := congrArg Fin.val h; omega
  have h50 : i ≠ (50 : Stack) := by
    intro h; have hv := congrArg Fin.val h; omega
  have h51 : i ≠ (51 : Stack) := by
    intro h; have hv := congrArg Fin.val h; omega
  have h52 : i ≠ (52 : Stack) := by
    intro h; have hv := congrArg Fin.val h; omega
  simp only [afterRow, afterRowUnit, afterTicketW,
    afterTagged, afterQTerm, afterQ₂Term, afterQ₁Term,
    Function.update_of_ne h52, Function.update_of_ne h48,
    Function.update_of_ne h51, Function.update_of_ne h50,
    Function.update_of_ne h49, Function.update_of_ne h47,
    Function.update_of_ne h46]
  apply after_column_unchanged n s q₁ q₂ w Q previousRow previousCol
  all_goals intro h; have hv := congrArg Fin.val h; omega

theorem previous_row_retained (n s q₁ q₂ w Q : Nat)
    (previousRow previousCol : Code) :
    afterRow n s q₁ q₂ w Q previousRow previousCol 2 =
      encodeCode previousRow := by
  rw [final_lower_at n s q₁ q₂ w Q previousRow previousCol
    2 (by decide)]
  change BitMachineStackEmbedding.bank embedRow
    (foreignWords w Q previousCol)
    (CodeRowsGraphCompiler.finalBank n s q₁ q₂ previousRow)
    (embedRow 2) = _
  rw [BitMachineStackEmbedding.bank_at]
  exact CodeRowsGraphCompiler.input_child_retained
    n s q₁ q₂ previousRow

theorem previous_col_retained (n s q₁ q₂ w Q : Nat)
    (previousRow previousCol : Code) :
    afterRow n s q₁ q₂ w Q previousRow previousCol 33 =
      encodeCode previousCol := by
  rw [final_lower_at n s q₁ q₂ w Q previousRow previousCol
    33 (by decide)]
  exact after_graph_previous_col n s q₁ q₂ w Q
    previousRow previousCol

theorem raw_w_retained (n s q₁ q₂ w Q : Nat)
    (previousRow previousCol : Code) :
    afterRow n s q₁ q₂ w Q previousRow previousCol 31 =
      List.replicate w true := by
  rw [final_lower_at n s q₁ q₂ w Q previousRow previousCol
    31 (by decide)]
  exact after_graph_w n s q₁ q₂ w Q previousRow previousCol

theorem raw_Q_retained (n s q₁ q₂ w Q : Nat)
    (previousRow previousCol : Code) :
    afterRow n s q₁ q₂ w Q previousRow previousCol 32 =
      List.replicate Q true := by
  rw [final_lower_at n s q₁ q₂ w Q previousRow previousCol
    32 (by decide)]
  exact after_graph_Q n s q₁ q₂ w Q previousRow previousCol

theorem raw_n_retained (n s q₁ q₂ w Q : Nat)
    (previousRow previousCol : Code) :
    afterRow n s q₁ q₂ w Q previousRow previousCol 18 =
      List.replicate n true := by
  rw [final_lower_at n s q₁ q₂ w Q previousRow previousCol
    18 (by decide)]
  change BitMachineStackEmbedding.bank embedRow
    (foreignWords w Q previousCol)
    (CodeRowsGraphCompiler.finalBank n s q₁ q₂ previousRow)
    (embedRow 18) = _
  rw [BitMachineStackEmbedding.bank_at]
  exact CodeRowsGraphCompiler.input_n_retained
    n s q₁ q₂ previousRow

theorem raw_s_retained (n s q₁ q₂ w Q : Nat)
    (previousRow previousCol : Code) :
    afterRow n s q₁ q₂ w Q previousRow previousCol 17 =
      List.replicate s true := by
  rw [final_lower_at n s q₁ q₂ w Q previousRow previousCol
    17 (by decide)]
  change BitMachineStackEmbedding.bank embedRow
    (foreignWords w Q previousCol)
    (CodeRowsGraphCompiler.finalBank n s q₁ q₂ previousRow)
    (embedRow 17) = _
  rw [BitMachineStackEmbedding.bank_at]
  exact CodeRowsGraphCompiler.input_s_retained
    n s q₁ q₂ previousRow

theorem raw_q₁_retained (n s q₁ q₂ w Q : Nat)
    (previousRow previousCol : Code) :
    afterRow n s q₁ q₂ w Q previousRow previousCol 16 =
      List.replicate q₁ true := by
  rw [final_lower_at n s q₁ q₂ w Q previousRow previousCol
    16 (by decide)]
  change BitMachineStackEmbedding.bank embedRow
    (foreignWords w Q previousCol)
    (CodeRowsGraphCompiler.finalBank n s q₁ q₂ previousRow)
    (embedRow 16) = _
  rw [BitMachineStackEmbedding.bank_at]
  exact CodeRowsGraphCompiler.input_q₁_retained
    n s q₁ q₂ previousRow

theorem raw_q₂_retained (n s q₁ q₂ w Q : Nat)
    (previousRow previousCol : Code) :
    afterRow n s q₁ q₂ w Q previousRow previousCol 12 =
      List.replicate q₂ true := by
  rw [final_lower_at n s q₁ q₂ w Q previousRow previousCol
    12 (by decide)]
  change BitMachineStackEmbedding.bank embedRow
    (foreignWords w Q previousCol)
    (CodeRowsGraphCompiler.finalBank n s q₁ q₂ previousRow)
    (embedRow 12) = _
  rw [BitMachineStackEmbedding.bank_at]
  exact CodeRowsGraphCompiler.input_q₂_retained
    n s q₁ q₂ previousRow

theorem lower_scratch_cleared (n s q₁ q₂ w Q : Nat)
    (previousRow previousCol : Code) :
    afterRow n s q₁ q₂ w Q previousRow previousCol 6 = [] ∧
    afterRow n s q₁ q₂ w Q previousRow previousCol 30 = [] := by
  constructor
  · rw [final_lower_at n s q₁ q₂ w Q previousRow previousCol
      6 (by decide)]
    change BitMachineStackEmbedding.bank embedRow
      (foreignWords w Q previousCol)
      (CodeRowsGraphCompiler.finalBank n s q₁ q₂ previousRow)
      (embedRow 6) = _
    rw [BitMachineStackEmbedding.bank_at]
    exact CodeRowsGraphCompiler.scratch_six_cleared
      n s q₁ q₂ previousRow
  · rw [final_lower_at n s q₁ q₂ w Q previousRow previousCol
      30 (by decide)]
    change BitMachineStackEmbedding.bank embedRow
      (foreignWords w Q previousCol)
      (CodeRowsGraphCompiler.finalBank n s q₁ q₂ previousRow)
      (embedRow 30) = _
    rw [BitMachineStackEmbedding.bank_at]
    exact CodeRowsGraphCompiler.scratch_thirty_cleared
      n s q₁ q₂ previousRow

/-- Every high work bank outside the explicitly retained intermediate
syntax/count range 46–52 is blank at completion. This includes all tagged,
copy, and append scratch cells. -/
theorem high_scratch_cleared (n s q₁ q₂ w Q : Nat)
    (previousRow previousCol : Code) (i : Stack)
    (hi : 38 ≤ i.val)
    (h46 : i ≠ 46) (h47 : i ≠ 47) (h48 : i ≠ 48)
    (h49 : i ≠ 49) (h50 : i ≠ 50) (h51 : i ≠ 51)
    (h52 : i ≠ 52) :
    afterRow n s q₁ q₂ w Q previousRow previousCol i = [] := by
  simp only [afterRow, afterRowUnit, afterTicketW,
    afterTagged, afterQTerm, afterQ₂Term, afterQ₁Term,
    Function.update_of_ne h52, Function.update_of_ne h48,
    Function.update_of_ne h51, Function.update_of_ne h50,
    Function.update_of_ne h49, Function.update_of_ne h47,
    Function.update_of_ne h46]
  have h34 : i ≠ (34 : Stack) := by
    intro h; have hv := congrArg Fin.val h; omega
  have h35 : i ≠ (35 : Stack) := by
    intro h; have hv := congrArg Fin.val h; omega
  have h36 : i ≠ (36 : Stack) := by
    intro h; have hv := congrArg Fin.val h; omega
  have h37 : i ≠ (37 : Stack) := by
    intro h; have hv := congrArg Fin.val h; omega
  rw [after_column_unchanged n s q₁ q₂ w Q
    previousRow previousCol i h34 h35 h36 h37]
  exact after_graph_blank n s q₁ q₂ w Q
    previousRow previousCol i (by omega)

#print axioms run_exact
#print axioms row_output
#print axioms column_output

end Paper2.CodeRecursiveStep
