import Paper2.CodeRecursiveColumn
import Paper2.CodeRawCountTerm
import Paper2.CodeTaggedCompiler

/-! The row successor uses the actual previous column syntax word. Scalar
fields needed by the frozen tagged compiler are built physically from raw
count cells before that compiler is invoked. -/

set_option maxHeartbeats 1000000

namespace Paper2.CodeRecursiveRow

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open Paper2.GeneratorCode Paper2.GeneratorSerialization
open Paper2.GeneratorSource Paper2.CodeRecursiveColumn
open Paper2.CodeRowsArmA

def termIndex (source target scratch : Stack)
    (hst : source ≠ target) (hss : source ≠ scratch)
    (hts : target ≠ scratch) : Fin 3 ↪ Stack where
  toFun i := ![source,target,scratch] i
  inj' := by
    intro a b h
    fin_cases a <;> fin_cases b <;> simp_all

def termProgram (source target scratch : Stack)
    (hst : source ≠ target) (hss : source ≠ scratch)
    (hts : target ≠ scratch) : CodeRawCountTerm.Label →
    TM2.Stmt (fun _ : Stack => Bool)
      CodeRawCountTerm.Label CodeRawCountTerm.Control :=
  fun l => BitMachineStackEmbedding.stackStmt
    (termIndex source target scratch hst hss hts)
    (CodeRawCountTerm.program l)

theorem term_initial_bank (source target scratch : Stack)
    (hst : source ≠ target) (hss : source ≠ scratch)
    (hts : target ≠ scratch)
    (B : Stack → List Bool) (n : Nat)
    (hsource : B source = List.replicate n true)
    (htarget : B target = []) (hscratch : B scratch = []) :
    BitMachineStackEmbedding.bank
      (termIndex source target scratch hst hss hts) B
      (CodeRawCountTerm.initial n).stk = B := by
  apply BitMachineStackEmbedding.bank_eq_self
  intro i
  fin_cases i
  · exact hsource.symm
  · exact htarget.symm
  · exact hscratch.symm

theorem term_result_bank (source target scratch : Stack)
    (hst : source ≠ target) (hss : source ≠ scratch)
    (hts : target ≠ scratch)
    (B : Stack → List Bool) (n : Nat)
    (hsource : B source = List.replicate n true)
    (htarget : B target = []) (hscratch : B scratch = []) :
    BitMachineStackEmbedding.bank
      (termIndex source target scratch hst hss hts) B
      (CodeRawCountTerm.final n).stk =
    Function.update B target (unary n) := by
  have hstk : (CodeRawCountTerm.final n).stk =
      Function.update (CodeRawCountTerm.initial n).stk
        (1 : Fin 3) (unary n) := by
    funext i
    fin_cases i <;> rfl
  rw [hstk, BitMachineStackEmbedding.bank_update,
    term_initial_bank source target scratch hst hss hts
      B n hsource htarget hscratch]
  rfl

theorem term_run (source target scratch : Stack)
    (hst : source ≠ target) (hss : source ≠ scratch)
    (hts : target ≠ scratch)
    (B : Stack → List Bool) (n : Nat)
    (hsource : B source = List.replicate n true)
    (htarget : B target = []) (hscratch : B scratch = []) :
    ∃ t ≤ 2*n+5,
      ((advance (termProgram source target scratch hst hss hts))^[t])
        (⟨some (BitMachineRawSequence.leftLabel
            CodeRawCountTerm.DelimiterLabel.write),
          ((),none), B⟩ :
          TM2.Cfg (fun _ : Stack => Bool) _ _) =
        ⟨none, ((),none), Function.update B target (unary n)⟩ := by
  obtain ⟨t,ht,hr⟩ := CodeRawCountTerm.run_exact n
  have h := BitMachineStackRun.run
    (termIndex source target scratch hst hss hts) B
    CodeRawCountTerm.program (CodeRawCountTerm.initial n) t
  rw [hr] at h
  have hi := term_initial_bank source target scratch hst hss hts
    B n hsource htarget hscratch
  have hf := term_result_bank source target scratch hst hss hts
    B n hsource htarget hscratch
  exact ⟨t,ht,by simpa only [termProgram,
    BitMachineStackEmbedding.stackCfg, hi, hf] using h⟩

theorem after_column_unchanged (n s q₁ q₂ w Q : Nat)
    (previousRow previousCol : Code) (i : Stack)
    (h34 : i ≠ 34) (h35 : i ≠ 35)
    (h36 : i ≠ 36) (h37 : i ≠ 37) :
    afterColumn n s q₁ q₂ w Q previousRow previousCol i =
      afterGraph n s q₁ q₂ w Q previousRow previousCol i := by
  simp only [afterColumn, afterCopies, afterTicket, afterWTerm,
    Function.update_of_ne h37, Function.update_of_ne h36,
    Function.update_of_ne h34, Function.update_of_ne h35]

theorem base_q₁ (n s q₁ q₂ w Q : Nat)
    (previousRow previousCol : Code) :
    afterColumn n s q₁ q₂ w Q previousRow previousCol 16 =
      List.replicate q₁ true := by
  rw [after_column_unchanged n s q₁ q₂ w Q
    previousRow previousCol 16 (by decide) (by decide)
      (by decide) (by decide)]
  change BitMachineStackEmbedding.bank embedRow
    (foreignWords w Q previousCol)
    (CodeRowsGraphCompiler.finalBank n s q₁ q₂ previousRow) (embedRow 16) = _
  rw [BitMachineStackEmbedding.bank_at]
  exact CodeRowsGraphCompiler.input_q₁_retained n s q₁ q₂ previousRow

theorem base_q₂ (n s q₁ q₂ w Q : Nat)
    (previousRow previousCol : Code) :
    afterColumn n s q₁ q₂ w Q previousRow previousCol 12 =
      List.replicate q₂ true := by
  rw [after_column_unchanged n s q₁ q₂ w Q
    previousRow previousCol 12 (by decide) (by decide)
      (by decide) (by decide)]
  change BitMachineStackEmbedding.bank embedRow
    (foreignWords w Q previousCol)
    (CodeRowsGraphCompiler.finalBank n s q₁ q₂ previousRow) (embedRow 12) = _
  rw [BitMachineStackEmbedding.bank_at]
  exact CodeRowsGraphCompiler.input_q₂_retained n s q₁ q₂ previousRow

theorem base_Q (n s q₁ q₂ w Q : Nat)
    (previousRow previousCol : Code) :
    afterColumn n s q₁ q₂ w Q previousRow previousCol 32 =
      List.replicate Q true := by
  rw [after_column_unchanged n s q₁ q₂ w Q
    previousRow previousCol 32 (by decide) (by decide)
      (by decide) (by decide)]
  exact after_graph_Q n s q₁ q₂ w Q previousRow previousCol

theorem base_w (n s q₁ q₂ w Q : Nat)
    (previousRow previousCol : Code) :
    afterColumn n s q₁ q₂ w Q previousRow previousCol 31 =
      List.replicate w true := by
  rw [after_column_unchanged n s q₁ q₂ w Q
    previousRow previousCol 31 (by decide) (by decide)
      (by decide) (by decide)]
  exact after_graph_w n s q₁ q₂ w Q previousRow previousCol

theorem base_previous_col (n s q₁ q₂ w Q : Nat)
    (previousRow previousCol : Code) :
    afterColumn n s q₁ q₂ w Q previousRow previousCol 33 =
      encodeCode previousCol := by
  rw [after_column_unchanged n s q₁ q₂ w Q
    previousRow previousCol 33 (by decide) (by decide)
      (by decide) (by decide)]
  exact after_graph_previous_col n s q₁ q₂ w Q
    previousRow previousCol

theorem base_s_terminated (n s q₁ q₂ w Q : Nat)
    (previousRow previousCol : Code) :
    afterColumn n s q₁ q₂ w Q previousRow previousCol 19 =
      unary s := by
  rw [after_column_unchanged n s q₁ q₂ w Q
    previousRow previousCol 19 (by decide) (by decide)
      (by decide) (by decide)]
  change BitMachineStackEmbedding.bank embedRow
    (foreignWords w Q previousCol)
    (CodeRowsGraphCompiler.finalBank n s q₁ q₂ previousRow) (embedRow 19) = _
  rw [BitMachineStackEmbedding.bank_at]
  simp only [CodeRowsGraphCompiler.finalBank,
    CodeRowsArmsEmbed.afterBoth, CodeRowsArmA.armAfterA,
    Function.update_of_ne (by decide : (19 : FinalBank) ≠ 29),
    Function.update_of_ne (by decide : (19 : FinalBank) ≠ 24),
    Function.update_of_ne (by decide : (19 : FinalBank) ≠ 23),
    Function.update_of_ne (by decide : (19 : FinalBank) ≠ 22)]
  change BitMachineStackEmbedding.bank CodeRowsArmA.embedPrep (fun _ => [])
    (CodeRowsPreparation.prepAfterArith n s q₁ q₂ previousRow)
    (CodeRowsArmA.embedPrep 19) = _
  rw [BitMachineStackEmbedding.bank_at]
  simp [CodeRowsPreparation.prepAfterArith,
    CodeRowsPreparation.prepAfterTerm]

theorem base_blank (n s q₁ q₂ w Q : Nat)
    (previousRow previousCol : Code) (i : Stack)
    (hi : 38 ≤ i.val) :
    afterColumn n s q₁ q₂ w Q previousRow previousCol i = [] := by
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

noncomputable def afterQ₁Term (n s q₁ q₂ w Q : Nat)
    (previousRow previousCol : Code) : Stack → List Bool :=
  Function.update (afterColumn n s q₁ q₂ w Q previousRow previousCol)
    46 (unary q₁)

noncomputable def afterQ₂Term (n s q₁ q₂ w Q : Nat)
    (previousRow previousCol : Code) : Stack → List Bool :=
  Function.update (afterQ₁Term n s q₁ q₂ w Q previousRow previousCol)
    47 (unary q₂)

noncomputable def afterQTerm (n s q₁ q₂ w Q : Nat)
    (previousRow previousCol : Code) : Stack → List Bool :=
  Function.update (afterQ₂Term n s q₁ q₂ w Q previousRow previousCol)
    48 (unary Q)

def q₁TermProgram := termProgram 16 46 38 (by decide) (by decide) (by decide)
def q₂TermProgram := termProgram 12 47 38 (by decide) (by decide) (by decide)
def QTermProgram := termProgram 32 48 38 (by decide) (by decide) (by decide)

theorem q₁_term_run (n s q₁ q₂ w Q : Nat)
    (previousRow previousCol : Code) :
    ∃ t ≤ 2*q₁+5,
      ((advance q₁TermProgram)^[t])
        (⟨some (BitMachineRawSequence.leftLabel
            CodeRawCountTerm.DelimiterLabel.write),
          ((),none), afterColumn n s q₁ q₂ w Q
            previousRow previousCol⟩ :
          TM2.Cfg (fun _ : Stack => Bool) _ _) =
        ⟨none, ((),none), afterQ₁Term n s q₁ q₂ w Q
          previousRow previousCol⟩ := by
  simpa only [q₁TermProgram, afterQ₁Term] using
    term_run 16 46 38 (by decide) (by decide) (by decide)
      (afterColumn n s q₁ q₂ w Q previousRow previousCol) q₁
      (base_q₁ n s q₁ q₂ w Q previousRow previousCol)
      (base_blank n s q₁ q₂ w Q previousRow previousCol
        46 (by decide))
      (base_blank n s q₁ q₂ w Q previousRow previousCol
        38 (by decide))

theorem q₂_term_run (n s q₁ q₂ w Q : Nat)
    (previousRow previousCol : Code) :
    ∃ t ≤ 2*q₂+5,
      ((advance q₂TermProgram)^[t])
        (⟨some (BitMachineRawSequence.leftLabel
            CodeRawCountTerm.DelimiterLabel.write),
          ((),none), afterQ₁Term n s q₁ q₂ w Q
            previousRow previousCol⟩ :
          TM2.Cfg (fun _ : Stack => Bool) _ _) =
        ⟨none, ((),none), afterQ₂Term n s q₁ q₂ w Q
          previousRow previousCol⟩ := by
  have hsource : afterQ₁Term n s q₁ q₂ w Q
      previousRow previousCol 12 = List.replicate q₂ true := by
    simp [afterQ₁Term, base_q₂]
  have htarget : afterQ₁Term n s q₁ q₂ w Q
      previousRow previousCol 47 = [] := by
    simp [afterQ₁Term,
      base_blank n s q₁ q₂ w Q previousRow previousCol
        47 (by decide)]
  have hscratch : afterQ₁Term n s q₁ q₂ w Q
      previousRow previousCol 38 = [] := by
    simp [afterQ₁Term,
      base_blank n s q₁ q₂ w Q previousRow previousCol
        38 (by decide)]
  simpa only [q₂TermProgram, afterQ₂Term] using
    term_run 12 47 38 (by decide) (by decide) (by decide)
      (afterQ₁Term n s q₁ q₂ w Q previousRow previousCol) q₂
      hsource htarget hscratch

theorem Q_term_run (n s q₁ q₂ w Q : Nat)
    (previousRow previousCol : Code) :
    ∃ t ≤ 2*Q+5,
      ((advance QTermProgram)^[t])
        (⟨some (BitMachineRawSequence.leftLabel
            CodeRawCountTerm.DelimiterLabel.write),
          ((),none), afterQ₂Term n s q₁ q₂ w Q
            previousRow previousCol⟩ :
          TM2.Cfg (fun _ : Stack => Bool) _ _) =
        ⟨none, ((),none), afterQTerm n s q₁ q₂ w Q
          previousRow previousCol⟩ := by
  have hsource : afterQ₂Term n s q₁ q₂ w Q
      previousRow previousCol 32 = List.replicate Q true := by
    simp [afterQ₂Term, afterQ₁Term, base_Q]
  have htarget : afterQ₂Term n s q₁ q₂ w Q
      previousRow previousCol 48 = [] := by
    simp [afterQ₂Term, afterQ₁Term,
      base_blank n s q₁ q₂ w Q previousRow previousCol
        48 (by decide)]
  have hscratch : afterQ₂Term n s q₁ q₂ w Q
      previousRow previousCol 38 = [] := by
    simp [afterQ₂Term, afterQ₁Term,
      base_blank n s q₁ q₂ w Q previousRow previousCol
        38 (by decide)]
  simpa only [QTermProgram, afterQTerm] using
    term_run 32 48 38 (by decide) (by decide) (by decide)
      (afterQ₂Term n s q₁ q₂ w Q previousRow previousCol) Q
      hsource htarget hscratch

noncomputable def afterTagged (n s q₁ q₂ w Q : Nat)
    (previousRow previousCol : Code) : Stack → List Bool :=
  Function.update (afterQTerm n s q₁ q₂ w Q previousRow previousCol)
    49 (encodeCode (taggedCode q₁ q₂ s previousCol))

def taggedIndex : Fin 8 ↪ Stack where
  toFun i := ![46,47,19,33,54,55,56,49] i
  inj' := by
    intro a b h
    fin_cases a <;> fin_cases b <;> simp_all

theorem tagged_initial_bank (n s q₁ q₂ w Q : Nat)
    (previousRow previousCol : Code) :
    BitMachineStackEmbedding.bank taggedIndex
      (afterQTerm n s q₁ q₂ w Q previousRow previousCol)
      (TaggedCompiler.inputs q₁ q₂ s previousCol) =
    afterQTerm n s q₁ q₂ w Q previousRow previousCol := by
  apply BitMachineStackEmbedding.bank_eq_self
  intro i
  fin_cases i
  · change unary q₁ = afterQTerm n s q₁ q₂ w Q
      previousRow previousCol 46
    simp [afterQTerm, afterQ₂Term, afterQ₁Term]
  · change unary q₂ = afterQTerm n s q₁ q₂ w Q
      previousRow previousCol 47
    simp [afterQTerm, afterQ₂Term]
  · change unary s = afterQTerm n s q₁ q₂ w Q
      previousRow previousCol 19
    simp [afterQTerm, afterQ₂Term, afterQ₁Term,
      base_s_terminated]
  · change encodeCode previousCol = afterQTerm n s q₁ q₂ w Q
      previousRow previousCol 33
    simp [afterQTerm, afterQ₂Term, afterQ₁Term,
      base_previous_col]
  · change ([] : List Bool) = afterQTerm n s q₁ q₂ w Q
      previousRow previousCol 54
    simp [afterQTerm, afterQ₂Term, afterQ₁Term,
      base_blank n s q₁ q₂ w Q previousRow previousCol 54 (by decide)]
  · change ([] : List Bool) = afterQTerm n s q₁ q₂ w Q
      previousRow previousCol 55
    simp [afterQTerm, afterQ₂Term, afterQ₁Term,
      base_blank n s q₁ q₂ w Q previousRow previousCol 55 (by decide)]
  · change ([] : List Bool) = afterQTerm n s q₁ q₂ w Q
      previousRow previousCol 56
    simp [afterQTerm, afterQ₂Term, afterQ₁Term,
      base_blank n s q₁ q₂ w Q previousRow previousCol 56 (by decide)]
  · change ([] : List Bool) = afterQTerm n s q₁ q₂ w Q
      previousRow previousCol 49
    simp [afterQTerm, afterQ₂Term, afterQ₁Term,
      base_blank n s q₁ q₂ w Q previousRow previousCol 49 (by decide)]

theorem tagged_result_bank (n s q₁ q₂ w Q : Nat)
    (previousRow previousCol : Code) :
    BitMachineStackEmbedding.bank taggedIndex
      (afterQTerm n s q₁ q₂ w Q previousRow previousCol)
      (Function.update (TaggedCompiler.inputs q₁ q₂ s previousCol)
        7 (encodeCode (taggedCode q₁ q₂ s previousCol))) =
    afterTagged n s q₁ q₂ w Q previousRow previousCol := by
  rw [BitMachineStackEmbedding.bank_update,
    tagged_initial_bank]
  rfl

def embeddedTaggedProgram : TaggedCompiler.Label →
    TM2.Stmt (fun _ : Stack => Bool)
      TaggedCompiler.Label TaggedCompiler.Control :=
  fun l => BitMachineStackEmbedding.stackStmt taggedIndex
    (TaggedCompiler.program l)

theorem embedded_tagged_run (n s q₁ q₂ w Q : Nat)
    (previousRow previousCol : Code) :
    ((advance embeddedTaggedProgram)^[
      TaggedCompiler.taggedClock q₁ q₂ s previousCol])
      (⟨some (.outerInit .third), none,
        afterQTerm n s q₁ q₂ w Q previousRow previousCol⟩ :
        TM2.Cfg (fun _ : Stack => Bool)
          TaggedCompiler.Label TaggedCompiler.Control) =
      ⟨none, none,
        afterTagged n s q₁ q₂ w Q previousRow previousCol⟩ := by
  have h := BitMachineStackRun.run taggedIndex
    (afterQTerm n s q₁ q₂ w Q previousRow previousCol)
    TaggedCompiler.program
    (TaggedCompiler.cfg (some (.outerInit .third)) none
      (TaggedCompiler.inputs q₁ q₂ s previousCol))
    (TaggedCompiler.taggedClock q₁ q₂ s previousCol)
  rw [← TaggedCompiler.run,
    TaggedCompiler.run_tagged q₁ q₂ s previousCol] at h
  simp only [BitMachineStackEmbedding.stackCfg,
    TaggedCompiler.cfg] at h
  rw [tagged_initial_bank, tagged_result_bank] at h
  exact h

noncomputable def afterTicketW (n s q₁ q₂ w Q : Nat)
    (previousRow previousCol : Code) : Stack → List Bool :=
  Function.update (afterTagged n s q₁ q₂ w Q previousRow previousCol)
    50 (encodeCode (.ticket w))

def ticketWIndex : Fin 3 ↪ Stack where
  toFun i := ![31,50,38] i
  inj' := by
    intro a b h
    fin_cases a <;> fin_cases b <;> simp_all

theorem ticket_w_initial_bank (n s q₁ q₂ w Q : Nat)
    (previousRow previousCol : Code) :
    BitMachineStackEmbedding.bank ticketWIndex
      (afterTagged n s q₁ q₂ w Q previousRow previousCol)
      (CodeAtomCountInput.initial w).stk =
    afterTagged n s q₁ q₂ w Q previousRow previousCol := by
  apply BitMachineStackEmbedding.bank_eq_self
  intro i
  fin_cases i
  · change List.replicate w true =
      afterTagged n s q₁ q₂ w Q previousRow previousCol 31
    simp [afterTagged, afterQTerm, afterQ₂Term,
      afterQ₁Term, base_w]
  · change ([] : List Bool) =
      afterTagged n s q₁ q₂ w Q previousRow previousCol 50
    simp [afterTagged, afterQTerm, afterQ₂Term,
      afterQ₁Term,
      base_blank n s q₁ q₂ w Q previousRow previousCol
        50 (by decide)]
  · change ([] : List Bool) =
      afterTagged n s q₁ q₂ w Q previousRow previousCol 38
    simp [afterTagged, afterQTerm, afterQ₂Term,
      afterQ₁Term,
      base_blank n s q₁ q₂ w Q previousRow previousCol
        38 (by decide)]

theorem ticket_w_result_bank (n s q₁ q₂ w Q : Nat)
    (previousRow previousCol : Code) :
    BitMachineStackEmbedding.bank ticketWIndex
      (afterTagged n s q₁ q₂ w Q previousRow previousCol)
      (CodeAtomCountInput.final w).stk =
    afterTicketW n s q₁ q₂ w Q previousRow previousCol := by
  have hstk : (CodeAtomCountInput.final w).stk =
      Function.update (CodeAtomCountInput.initial w).stk
        (1 : Fin 3) (encodeCode (.ticket w)) := by
    funext i
    fin_cases i <;> rfl
  rw [hstk, BitMachineStackEmbedding.bank_update,
    ticket_w_initial_bank]
  rfl

def embeddedTicketWProgram : CodeAtomCountInput.Label →
    TM2.Stmt (fun _ : Stack => Bool)
      CodeAtomCountInput.Label CodeAtomCountInput.Control :=
  fun l => BitMachineStackEmbedding.stackStmt ticketWIndex
    (CodeAtomCountInput.program l)

theorem embedded_ticket_w_run (n s q₁ q₂ w Q : Nat)
    (previousRow previousCol : Code) :
    ∃ t ≤ 2*w+8,
      ((advance embeddedTicketWProgram)^[t])
        (⟨some (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel
              CodeAtomCountInput.InitLabel.write)),
          (((),none),()),
          afterTagged n s q₁ q₂ w Q previousRow previousCol⟩ :
          TM2.Cfg (fun _ : Stack => Bool) _ _) =
        ⟨none, (((),none),()),
          afterTicketW n s q₁ q₂ w Q previousRow previousCol⟩ := by
  obtain ⟨t,ht,hr⟩ := CodeAtomCountInput.run_ticket_count w
  have h := BitMachineStackRun.run ticketWIndex
    (afterTagged n s q₁ q₂ w Q previousRow previousCol)
    CodeAtomCountInput.program (CodeAtomCountInput.initial w) t
  rw [hr] at h
  exact ⟨t,ht,by simpa only [embeddedTicketWProgram,
    BitMachineStackEmbedding.stackCfg,
    ticket_w_initial_bank, ticket_w_result_bank] using h⟩

def rowUnitCode (q₁ q₂ s w : Nat) (previousCol : Code) : Code :=
  .append (.ticket w) (taggedCode q₁ q₂ s previousCol)

noncomputable def afterRowUnit (n s q₁ q₂ w Q : Nat)
    (previousRow previousCol : Code) : Stack → List Bool :=
  Function.update (afterTicketW n s q₁ q₂ w Q previousRow previousCol)
    51 (encodeCode (rowUnitCode q₁ q₂ s w previousCol))

theorem ticket_w_at_49 (n s q₁ q₂ w Q : Nat)
    (previousRow previousCol : Code) :
    afterTicketW n s q₁ q₂ w Q previousRow previousCol 49 =
      encodeCode (taggedCode q₁ q₂ s previousCol) := by
  simp [afterTicketW, afterTagged]

theorem ticket_w_at_50 (n s q₁ q₂ w Q : Nat)
    (previousRow previousCol : Code) :
    afterTicketW n s q₁ q₂ w Q previousRow previousCol 50 =
      encodeCode (.ticket w) := by
  simp [afterTicketW]

theorem ticket_w_blank_high (n s q₁ q₂ w Q : Nat)
    (previousRow previousCol : Code) (i : Stack)
    (hi : 51 ≤ i.val) :
    afterTicketW n s q₁ q₂ w Q previousRow previousCol i = [] := by
  have h50 : i ≠ (50 : Stack) := by
    intro h; have hv := congrArg Fin.val h; omega
  have h49 : i ≠ (49 : Stack) := by
    intro h; have hv := congrArg Fin.val h; omega
  have h48 : i ≠ (48 : Stack) := by
    intro h; have hv := congrArg Fin.val h; omega
  have h47 : i ≠ (47 : Stack) := by
    intro h; have hv := congrArg Fin.val h; omega
  have h46 : i ≠ (46 : Stack) := by
    intro h; have hv := congrArg Fin.val h; omega
  simp only [afterTicketW, afterTagged, afterQTerm, afterQ₂Term,
    afterQ₁Term, Function.update_of_ne h50,
    Function.update_of_ne h49, Function.update_of_ne h48,
    Function.update_of_ne h47, Function.update_of_ne h46]
  exact base_blank n s q₁ q₂ w Q previousRow previousCol i (by omega)

def appendIndex : Fin 8 ↪ Stack where
  toFun i := ![50,49,58,59,60,61,51,57] i
  inj' := by
    intro a b h
    fin_cases a <;> fin_cases b <;> simp_all

theorem append_initial_bank (n s q₁ q₂ w Q : Nat)
    (previousRow previousCol : Code) :
    BitMachineStackEmbedding.bank appendIndex
      (afterTicketW n s q₁ q₂ w Q previousRow previousCol)
      (CodeConstructorMachine.cfg (some .appendRightCopy) none
        (CodeConstructorMachine.appendInputs (.ticket w)
          (taggedCode q₁ q₂ s previousCol)) [] []).stk =
    afterTicketW n s q₁ q₂ w Q previousRow previousCol := by
  apply BitMachineStackEmbedding.bank_eq_self
  intro i
  fin_cases i
  · exact (ticket_w_at_50 n s q₁ q₂ w Q previousRow previousCol).symm
  · exact (ticket_w_at_49 n s q₁ q₂ w Q previousRow previousCol).symm
  · exact (ticket_w_blank_high n s q₁ q₂ w Q
      previousRow previousCol 58 (by decide)).symm
  · exact (ticket_w_blank_high n s q₁ q₂ w Q
      previousRow previousCol 59 (by decide)).symm
  · exact (ticket_w_blank_high n s q₁ q₂ w Q
      previousRow previousCol 60 (by decide)).symm
  · exact (ticket_w_blank_high n s q₁ q₂ w Q
      previousRow previousCol 61 (by decide)).symm
  · exact (ticket_w_blank_high n s q₁ q₂ w Q
      previousRow previousCol 51 (by decide)).symm
  · exact (ticket_w_blank_high n s q₁ q₂ w Q
      previousRow previousCol 57 (by decide)).symm

theorem append_result_bank (n s q₁ q₂ w Q : Nat)
    (previousRow previousCol : Code) :
    BitMachineStackEmbedding.bank appendIndex
      (afterTicketW n s q₁ q₂ w Q previousRow previousCol)
      (CodeConstructorMachine.cfg none none
        (CodeConstructorMachine.appendInputs (.ticket w)
          (taggedCode q₁ q₂ s previousCol))
        (encodeCode (rowUnitCode q₁ q₂ s w previousCol)) []).stk =
    afterRowUnit n s q₁ q₂ w Q previousRow previousCol := by
  have hstk :
      (CodeConstructorMachine.cfg none none
        (CodeConstructorMachine.appendInputs (.ticket w)
          (taggedCode q₁ q₂ s previousCol))
        (encodeCode (rowUnitCode q₁ q₂ s w previousCol)) []).stk =
      Function.update
        (CodeConstructorMachine.cfg (some .appendRightCopy) none
          (CodeConstructorMachine.appendInputs (.ticket w)
            (taggedCode q₁ q₂ s previousCol)) [] []).stk
        (6 : Fin 8) (encodeCode (rowUnitCode q₁ q₂ s w previousCol)) := by
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
        (encodeCode (.ticket w))
        (encodeCode (taggedCode q₁ q₂ s previousCol))])
      (⟨some .appendRightCopy, none,
        afterTicketW n s q₁ q₂ w Q previousRow previousCol⟩ :
        TM2.Cfg (fun _ : Stack => Bool)
          CodeConstructorMachine.Label CodeConstructorMachine.Control) =
      ⟨none, none,
        afterRowUnit n s q₁ q₂ w Q previousRow previousCol⟩ := by
  have h := BitMachineStackRun.run appendIndex
    (afterTicketW n s q₁ q₂ w Q previousRow previousCol)
    CodeConstructorMachine.program
    (CodeConstructorMachine.cfg (some .appendRightCopy) none
      (CodeConstructorMachine.appendInputs (.ticket w)
        (taggedCode q₁ q₂ s previousCol)) [] [])
    (CodeConstructorMachine.appendClock
      (encodeCode (.ticket w))
      (encodeCode (taggedCode q₁ q₂ s previousCol)))
  rw [← CodeConstructorMachine.run,
    CodeConstructorMachine.run_append (.ticket w)
      (taggedCode q₁ q₂ s previousCol)] at h
  have hr := append_result_bank n s q₁ q₂ w Q previousRow previousCol
  simp only [rowUnitCode] at hr
  simpa only [embeddedAppendProgram,
    BitMachineStackEmbedding.stackCfg,
    append_initial_bank, hr] using h

def rowCode (q₁ q₂ s w Q : Nat) (previousCol : Code) : Code :=
  copies Q (rowUnitCode q₁ q₂ s w previousCol)

noncomputable def afterRow (n s q₁ q₂ w Q : Nat)
    (previousRow previousCol : Code) : Stack → List Bool :=
  Function.update
    (Function.update
      (afterRowUnit n s q₁ q₂ w Q previousRow previousCol)
      48 [])
    52 (encodeCode (rowCode q₁ q₂ s w Q previousCol))

def copiesIndex : Fin 5 ↪ Stack where
  toFun i := ![48,51,52,62,63] i
  inj' := by
    intro a b h
    fin_cases a <;> fin_cases b <;> simp_all

theorem copies_initial_bank (n s q₁ q₂ w Q : Nat)
    (previousRow previousCol : Code) :
    BitMachineStackEmbedding.bank copiesIndex
      (afterRowUnit n s q₁ q₂ w Q previousRow previousCol)
      (CodeCopiesMachine.initial (unary Q)
        (encodeCode (rowUnitCode q₁ q₂ s w previousCol))).stk =
    afterRowUnit n s q₁ q₂ w Q previousRow previousCol := by
  apply BitMachineStackEmbedding.bank_eq_self
  intro i
  fin_cases i
  · change unary Q = afterRowUnit n s q₁ q₂ w Q
      previousRow previousCol 48
    simp [afterRowUnit, afterTicketW, afterTagged,
      afterQTerm]
  · change encodeCode (rowUnitCode q₁ q₂ s w previousCol) =
      afterRowUnit n s q₁ q₂ w Q previousRow previousCol 51
    simp [afterRowUnit]
  · change ([] : List Bool) = afterRowUnit n s q₁ q₂ w Q
      previousRow previousCol 52
    simp [afterRowUnit, afterTicketW, afterTagged,
      afterQTerm, afterQ₂Term, afterQ₁Term,
      base_blank n s q₁ q₂ w Q previousRow previousCol 52 (by decide)]
  · change ([] : List Bool) = afterRowUnit n s q₁ q₂ w Q
      previousRow previousCol 62
    simp [afterRowUnit, afterTicketW, afterTagged,
      afterQTerm, afterQ₂Term, afterQ₁Term,
      base_blank n s q₁ q₂ w Q previousRow previousCol 62 (by decide)]
  · change ([] : List Bool) = afterRowUnit n s q₁ q₂ w Q
      previousRow previousCol 63
    simp [afterRowUnit, afterTicketW, afterTagged,
      afterQTerm, afterQ₂Term, afterQ₁Term,
      base_blank n s q₁ q₂ w Q previousRow previousCol 63 (by decide)]

theorem copies_result_bank (n s q₁ q₂ w Q : Nat)
    (previousRow previousCol : Code) :
    BitMachineStackEmbedding.bank copiesIndex
      (afterRowUnit n s q₁ q₂ w Q previousRow previousCol)
      (CodeCopiesMachine.cfg none none []
        (encodeCode (rowUnitCode q₁ q₂ s w previousCol))
        (encodeCode (rowCode q₁ q₂ s w Q previousCol)) [] []).stk =
    afterRow n s q₁ q₂ w Q previousRow previousCol := by
  have hstk :
      (CodeCopiesMachine.cfg none none []
        (encodeCode (rowUnitCode q₁ q₂ s w previousCol))
        (encodeCode (rowCode q₁ q₂ s w Q previousCol)) [] []).stk =
      Function.update
        (Function.update
          (CodeCopiesMachine.initial (unary Q)
            (encodeCode (rowUnitCode q₁ q₂ s w previousCol))).stk
          (0 : Fin 5) [])
        (2 : Fin 5) (encodeCode (rowCode q₁ q₂ s w Q previousCol)) := by
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
    ((advance embeddedCopiesProgram)^[CodeCopiesMachine.clock Q
      (rowUnitCode q₁ q₂ s w previousCol)])
      (⟨some .initialize, none,
        afterRowUnit n s q₁ q₂ w Q previousRow previousCol⟩ :
        TM2.Cfg (fun _ : Stack => Bool)
          CodeCopiesMachine.Label CodeCopiesMachine.Control) =
      ⟨none, none,
        afterRow n s q₁ q₂ w Q previousRow previousCol⟩ := by
  have h := BitMachineStackRun.run copiesIndex
    (afterRowUnit n s q₁ q₂ w Q previousRow previousCol)
    CodeCopiesMachine.program
    (CodeCopiesMachine.initial (unary Q)
      (encodeCode (rowUnitCode q₁ q₂ s w previousCol)))
    (CodeCopiesMachine.clock Q (rowUnitCode q₁ q₂ s w previousCol))
  rw [← CodeCopiesMachine.run,
    CodeCopiesMachine.run_copies Q
      (rowUnitCode q₁ q₂ s w previousCol)] at h
  have hr := copies_result_bank n s q₁ q₂ w Q previousRow previousCol
  simp only [rowCode] at hr
  simpa only [embeddedCopiesProgram,
    BitMachineStackEmbedding.stackCfg,
    copies_initial_bank, hr] using h

theorem row_output_exact (n s q₁ q₂ w Q : Nat)
    (previousRow previousCol : Code) :
    afterRow n s q₁ q₂ w Q previousRow previousCol 52 =
      encodeCode (rowCode q₁ q₂ s w Q previousCol) := by
  simp [afterRow]

theorem source_successor_row (n s q₁ q₂ w Q : Nat)
    (row₀ col₀ : Code) (k : Nat) :
    rowCode q₁ q₂ s w Q
      (recursiveCodes n s q₁ q₂ w Q row₀ col₀ k).2 =
    (recursiveCodes n s q₁ q₂ w Q row₀ col₀ (k+1)).1 := by
  rfl

end Paper2.CodeRecursiveRow
