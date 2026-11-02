import EthInapproximability.CurrentPaper.SourceCSPTotalSelectiveFrame
import EthInapproximability.CurrentPaper.SourceCSPRowQueryUnary
import EthInapproximability.CurrentPaper.SourceClauseRowWriterBlank

/-! One physical typed-row read after selective CSP staging. -/

namespace EthInapproximability.CurrentPaper.SourceCSPStagedFirstRow

open Turing BitMachineEncoding BitMachineStackEmbedding

/-- Exact first-row factorization of an already validated nonempty row vector. -/
theorem first_row_decomposition {n m a q : Nat}
    (suffix : List Bool) (rows : Fin m → SourceCSPCodec.Row n a q)
    (hm : 0 < m)
    (hread : SourceCSPCodec.readFn (SourceCSPCodec.readRow n a q) m suffix =
      some (rows, [])) :
    ∃ rest,
      suffix = SourceCSPCodec.rowFields (rows ⟨0, hm⟩) ++ rest := by
  cases m with
  | zero => omega
  | succ m =>
      let rest := SourceCSPCodec.fnFields SourceCSPCodec.rowFields
        (fun i : Fin m => rows i.succ)
      have hsound :=
        SourceCSPCodec.readFn_sound SourceCSPCodec.rowFields
          (SourceCSPCodec.readRow n a q)
          (fun h => SourceCSPCodec.readRow_sound h) hread
      have hfields := SourceCSPCodec.fnFields_succ
        SourceCSPCodec.rowFields rows
      refine ⟨rest, ?_⟩
      simp only [List.append_nil] at hsound
      rw [hfields] at hsound
      exact hsound.symm

private theorem vertex_word (n : Nat) (hn : 0 < n) :
    true :: List.replicate (n - 1) true =
      List.replicate n true := by
  cases n with
  | zero => omega
  | succ n => rfl

def writerSourceCell (q : Nat) : SourceClauseRowWriterOperands.Stack q :=
  SourceClauseRowWriterCleanup.rowCell (.inr 0)

def writerVertexCell (q : Nat) : SourceClauseRowWriterOperands.Stack q :=
  SourceClauseRowWriterOperands.vertex

private theorem blank_bank_other (q n : Nat) (suffix : List Bool)
    (k : SourceClauseRowWriterOperands.Stack q)
    (hs : k ≠ writerSourceCell q)
    (hv : k ≠ writerVertexCell q) :
    SourceClauseRowWriterBlank.bank
      (SourceCSPRowQueryFrame.initial suffix []) n 0 [] [] [] k = [] := by
  cases k with
  | inl k =>
      cases k with
      | inl k =>
          cases k with
          | inl x =>
              cases x with
              | inl p =>
                  obtain ⟨j, r⟩ := p
                  simp [SourceClauseRowWriterBlank.bank,
                    SourceClauseRowWriterBlank.master,
                    SourceClauseRowWriterBlank.core,
                    SourceCSPRowQueryFrame.initial]
              | inr r =>
                  fin_cases r <;>
                    simp_all [SourceClauseRowWriterBlank.bank,
                      SourceClauseRowWriterBlank.master,
                      SourceClauseRowWriterBlank.core,
                      SourceCSPRowQueryFrame.initial,
                      writerSourceCell,
                      SourceClauseRowWriterCleanup.rowCell]
          | inr r =>
              fin_cases r <;>
                simp [SourceClauseRowWriterBlank.bank,
                  SourceClauseRowWriterBlank.master,
                  SourceClauseRowWriterBlank.core]
      | inr r =>
          cases r with
          | inl r =>
              simp [SourceClauseRowWriterBlank.bank,
                SourceClauseRowWriterBlank.master]
          | inr r =>
              simp [SourceClauseRowWriterBlank.bank,
                SourceClauseRowWriterBlank.master]
  | inr r =>
      fin_cases r <;>
        simp_all [SourceClauseRowWriterBlank.bank,
          writerVertexCell,
          SourceClauseRowWriterOperands.vertex]

/-- The staged physical right bank is exactly the standard clean
row-writer bank, with its row parser at the literal raw suffix and empty cap.
The unary vertex word is retained outside the row frame. -/
theorem staged_writer_eq_blank_bank (q n : Nat) (suffix : List Bool)
    (U : SourceCSPSelectiveStage.Stack q → List Bool)
    (hn : 0 < n)
    (hsource : U SourceCSPSecondPassInput.writerSource = suffix)
    (hvertex : U SourceCSPSecondPassInput.writerVertex =
      true :: List.replicate (n - 1) true)
    (hblank : ∀ k : SourceClauseRowWriterOperands.Stack q,
      (.inr k : SourceCSPSelectiveStage.Stack q) ≠
        SourceCSPSecondPassInput.writerSource →
      (.inr k : SourceCSPSelectiveStage.Stack q) ≠
        SourceCSPSecondPassInput.writerVertex →
      U (.inr k) = []) :
    (fun k : SourceClauseRowWriterOperands.Stack q => U (.inr k)) =
      SourceClauseRowWriterBlank.bank
        (SourceCSPRowQueryFrame.initial suffix []) n 0 [] [] [] := by
  funext k
  by_cases hs : k = writerSourceCell q
  · subst k
    simpa [writerSourceCell, SourceCSPSecondPassInput.writerSource,
      SourceClauseRowWriterCleanup.rowCell,
      SourceClauseRowWriterBlank.bank,
      SourceClauseRowWriterBlank.master,
      SourceClauseRowWriterBlank.core,
      SourceCSPRowQueryFrame.initial] using hsource
  by_cases hv : k = writerVertexCell q
  · subst k
    change U SourceCSPSecondPassInput.writerVertex = _
    rw [hvertex, vertex_word n hn]
    rfl
  have hU : U (.inr k) = [] := hblank k
    (by
      intro he
      exact hs (Sum.inr.inj he))
    (by
      intro he
      exact hv (Sum.inr.inj he))
  rw [hU]
  exact (blank_bank_other q n suffix k hs hv).symm

abbrev Stack (q : Nat) := SourceCSPSelectiveStage.Stack q

def rowSlot {q : Nat} (x : SourceCSPRowQueryFrame.Stack q) : Stack q :=
  .inr (SourceClauseRowWriterCleanup.rowCell x)

def rowCap {q : Nat} : Stack q := rowSlot (.inr 3)
def vertexSlot {q : Nat} : Stack q :=
  .inr SourceClauseRowWriterOperands.vertex
def workSlot {q : Nat} : Stack q :=
  .inr SourceClauseRowWriterOperands.scratch

def capCopyEmbedding {q : Nat} : Fin 3 ↪ Stack q where
  toFun k := if k = 0 then vertexSlot else
    if k = 1 then rowCap else workSlot
  inj' := by
    intro x y h
    fin_cases x <;> fin_cases y <;>
      simp [vertexSlot, rowCap, rowSlot, workSlot,
        SourceClauseRowWriterCleanup.rowCell,
        SourceClauseRowWriterOperands.vertex,
        SourceClauseRowWriterOperands.scratch] at h <;> simp_all

def capCopyProgram {q : Nat} (l : BitMachineCopy.Label) :
    TM2.Stmt (fun _ : Stack q => Bool)
      BitMachineCopy.Label (Option Bool) :=
  SourceCSPSecondPassInput.copyProgram capCopyEmbedding l

def dropCapProgram {q : Nat} (_ : Unit) :
    TM2.Stmt (fun _ : Stack q => Bool) Unit (Option Bool) :=
  .pop rowCap (fun _ b => b) .halt

abbrev CapLabel := BitMachineRawSequence.Label BitMachineCopy.Label Unit
abbrev CapControl := Option Bool × Option Bool

def capPrepareProgram {q : Nat} :=
  BitMachineRawSequence.program (capCopyProgram (q := q))
    (dropCapProgram (q := q)) () none none

/-- From the clean staged bank, a physical copy retains the full unary
vertex word while one pop puts the predecessor unary word in the row cap.
Every other cell, including every global cell, is unchanged. -/
theorem cap_prepare_run (q n : Nat) (suffix : List Bool)
    (U : Stack q → List Bool) (hn : 0 < n)
    (hwriter : (fun k : SourceClauseRowWriterOperands.Stack q =>
        U (.inr k)) =
      SourceClauseRowWriterBlank.bank
        (SourceCSPRowQueryFrame.initial suffix []) n 0 [] [] []) :
    ∃ t T, t ≤ 2 * n + 4 ∧
      ((advance (capPrepareProgram (q := q)))^[t])
        (⟨some (.inl .scan), (none, none), U⟩ :
          TM2.Cfg (fun _ : Stack q => Bool) CapLabel CapControl) =
        ⟨none, (none, some true), T⟩ ∧
      (fun x : SourceCSPRowQueryFrame.Stack q => T (rowSlot x)) =
        SourceCSPRowQueryFrame.initial suffix
          (List.replicate (n - 1) true) ∧
      (∀ k : Stack q, k ≠ rowCap → T k = U k) := by
  have hvertex : U vertexSlot = List.replicate n true := by
    change U (.inr SourceClauseRowWriterOperands.vertex) = _
    rw [congrFun hwriter SourceClauseRowWriterOperands.vertex]
    rfl
  have hcapBlank : U rowCap = [] := by
    change U (.inr (SourceClauseRowWriterCleanup.rowCell (.inr 3))) = _
    rw [congrFun hwriter (SourceClauseRowWriterCleanup.rowCell (.inr 3))]
    rfl
  have hworkBlank : U workSlot = [] := by
    change U (.inr SourceClauseRowWriterOperands.scratch) = _
    rw [congrFun hwriter SourceClauseRowWriterOperands.scratch]
    rfl
  obtain ⟨tc, S1, htc, hcopy, hsource1, hcap1, hwork1,
    hother1⟩ :=
    SourceCSPSecondPassInput.copy_framed
      (capCopyEmbedding (q := q)) U (List.replicate n true)
      hvertex hcapBlank hworkBlank
  let T := Function.update S1 rowCap
    (List.replicate (n - 1) true)
  have hcap1' : S1 rowCap =
      true :: List.replicate (n - 1) true := by
    rw [show rowCap (q := q) = capCopyEmbedding 1 by rfl]
    rw [hcap1]
    exact (vertex_word n hn).symm
  have hpop : ((advance (dropCapProgram (q := q)))^[1])
      (⟨some (), none, S1⟩ :
        TM2.Cfg (fun _ : Stack q => Bool) Unit (Option Bool)) =
      ⟨none, some true, T⟩ := by
    simp [advance, TM2.step, TM2.stepAux,
      dropCapProgram, T, hcap1']
  obtain ⟨t, ht, hrun⟩ := BitMachineRawSequence.runs
    (capCopyProgram (q := q)) (dropCapProgram (q := q))
    .scan () none none none (some true)
    U S1 T tc 1
    (by simpa only [capCopyProgram,
      SourceCSPSecondPassInput.copyProgram] using hcopy)
    hpop
  have hrowU : ∀ x : SourceCSPRowQueryFrame.Stack q,
      U (rowSlot x) = SourceCSPRowQueryFrame.initial suffix [] x := by
    intro x
    calc
      U (rowSlot x) =
          SourceClauseRowWriterBlank.bank
            (SourceCSPRowQueryFrame.initial suffix []) n 0 [] [] []
            (SourceClauseRowWriterCleanup.rowCell x) :=
        congrFun hwriter _
      _ = SourceCSPRowQueryFrame.initial suffix [] x := by
        simpa only [rowSlot, SourceClauseRowWriterCleanup.rowCell,
          SourceClauseRowWriterCore.gate_cell] using
          SourceClauseRowWriterBlank.row_word
            (SourceCSPRowQueryFrame.initial suffix []) n 0 [] [] [] x
  have hframe : ∀ k : Stack q, k ≠ rowCap → T k = U k := by
    intro k hk
    rw [show T k = S1 k by
      simp [T, Function.update_of_ne hk]]
    by_cases hv : k = vertexSlot
    · subst k
      exact hsource1.trans hvertex.symm
    by_cases hw : k = workSlot
    · subst k
      exact hwork1.trans hworkBlank.symm
    exact hother1 k
      (by simpa only [capCopyEmbedding, dif_pos] using hv)
      (by simpa only [capCopyEmbedding] using hk)
      (by simpa only [capCopyEmbedding] using hw)
  have hrowT : (fun x : SourceCSPRowQueryFrame.Stack q =>
      T (rowSlot x)) =
      SourceCSPRowQueryFrame.initial suffix
        (List.replicate (n - 1) true) := by
    funext x
    by_cases hx : x = (.inr 3 : SourceCSPRowQueryFrame.Stack q)
    · subst x
      simp [T, rowCap, rowSlot,
        SourceCSPRowQueryFrame.initial]
    · have hne : rowSlot x ≠ rowCap := by
        intro he
        have he' : x = (.inr 3 : SourceCSPRowQueryFrame.Stack q) := by
          simpa only [rowSlot, rowCap,
            SourceClauseRowWriterCleanup.rowCell,
            Sum.inr.injEq, Sum.inl.injEq] using he
        exact hx he'
      rw [hframe _ hne, hrowU x]
      cases x with
      | inl p => rfl
      | inr r =>
          fin_cases r <;>
            simp [SourceCSPRowQueryFrame.initial] at hx ⊢
  refine ⟨t, T, ?_, ?_, hrowT, hframe⟩
  · simp only [List.length_replicate] at htc
    omega
  · simpa only [capPrepareProgram] using hrun

/-- The checked-row reader acts on the writer's row-frame cells only. -/
def readEmbedding {q : Nat} :
    SourceCSPRowQueryFrame.Stack q ↪ Stack q where
  toFun := rowSlot
  inj' := by
    intro x y h
    simpa only [rowSlot, SourceClauseRowWriterCleanup.rowCell,
      Sum.inr.injEq, Sum.inl.injEq] using h

abbrev ReadLabel (q a : Nat) :=
  BitMachineRawSequence.Label
    (SourceCSPRowController.Label q (a ^ q))
    (SourceCSPQueryBank.Label q)
abbrev ReadControl :=
  SourceCSPRowController.Control × SourceCSPQueryBank.Control

def readProgram (q a : Nat) (l : ReadLabel q a) :
    TM2.Stmt (fun _ : Stack q => Bool) (ReadLabel q a) ReadControl :=
  BitMachineStackEmbedding.stmt readEmbedding id id id none
    (SourceCSPRowQueryFrame.combinedProgram q (a ^ q) l)

abbrev readStart (q a : Nat) : ReadLabel q a :=
  BitMachineRawSequence.leftLabel
    (.start 0 : SourceCSPRowController.Label q (a ^ q))
abbrev readInitialControl : ReadControl :=
  ((none, none), (((none, none), (none, false)), none))

/-- The existing parse-and-check machine runs on the physically staged writer
bank. It returns the first row's retained unary query words, truth word, and
unconsumed suffix, while every non-row writer/global cell is unchanged. -/
theorem embedded_valid_first_row {n a q : Nat}
    (row : SourceCSPCodec.Row n a q) (hn : 0 < n)
    (rest : List Bool) (U : Stack q → List Bool)
    (hrow : (fun x : SourceCSPRowQueryFrame.Stack q => U (rowSlot x)) =
      SourceCSPRowQueryFrame.initial
        (SourceCSPCodec.rowFields row ++ rest)
        (List.replicate (n - 1) true)) :
    ∃ (t : Nat) (T : ReadControl × (Stack q → List Bool)),
      t ≤ q * (2 * (SourceCSPCodec.rowFields row ++ rest).length + 4) +
          2 * a ^ q + 3 + q * (100 * (n + 1) ^ 2) + 2 ∧
      ((advance (readProgram q a))^[t])
        (⟨some (readStart q a), readInitialControl, U⟩ :
          TM2.Cfg (fun _ : Stack q => Bool) (ReadLabel q a) ReadControl) =
        ⟨none, T.1, T.2⟩ ∧
      T.2 (rowSlot (.inr 4)) = [true] ∧
      (∀ j : Fin q, T.2 (rowSlot (.inl (j, 1))) =
        List.replicate (row.1 j).val true) ∧
      T.2 (rowSlot (.inr 0)) = rest ∧
      T.2 (rowSlot (.inr 2)) = true :: List.ofFn row.2 ∧
      (∀ k : Stack q, (¬ ∃ x, rowSlot x = k) → T.2 k = U k) := by
  have hword : ∀ j : Fin q, (row.1 j).val.bits.length ≤ n := by
    intro j
    have hbit := UnaryBinaryEncoding.bits_length_le (row.1 j).val
    omega
  obtain ⟨tr, c, htr, hr, hhalt, hstatus, hunary,
    hsource, houtput⟩ :=
    SourceCSPRowQueryUnary.combined_valid_row_unary
      row hn rest n hword (by omega)
  let c0 : TM2.Cfg (fun _ : SourceCSPRowQueryFrame.Stack q => Bool)
      (ReadLabel q a) ReadControl :=
    ⟨some (readStart q a), readInitialControl,
      SourceCSPRowQueryFrame.initial
        (SourceCSPCodec.rowFields row ++ rest)
        (List.replicate (n - 1) true)⟩
  have hstart : BitMachineStackEmbedding.cfg readEmbedding U id id none c0 =
      (⟨some (readStart q a), readInitialControl, U⟩ :
        TM2.Cfg (fun _ : Stack q => Bool) (ReadLabel q a) ReadControl) := by
    unfold BitMachineStackEmbedding.cfg BitMachineStackEmbedding.stackCfg
      BitMachineInline.cfg c0
    congr 1
    exact BitMachineStackEmbedding.bank_eq_self readEmbedding U _
      (fun x => (congrFun hrow x).symm)
  have hlocalhalt : (((advance
      (SourceCSPRowQueryFrame.combinedProgram q (a ^ q)))^[tr]) c0).l = none := by
    rw [show c0 = (⟨some (readStart q a), readInitialControl,
      SourceCSPRowQueryFrame.initial
        (SourceCSPCodec.rowFields row ++ rest)
        (List.replicate (n - 1) true)⟩ :
        TM2.Cfg (fun _ : SourceCSPRowQueryFrame.Stack q => Bool)
          (ReadLabel q a) ReadControl) by rfl, hr]
    exact hhalt
  obtain ⟨t, ht, hrun⟩ := BitMachineStackEmbedding.outputs
    readEmbedding U id id id (by intro v; rfl) none
    (SourceCSPRowQueryFrame.combinedProgram q (a ^ q))
    (readProgram q a) (by intro l; rfl) c0 tr hlocalhalt
  let F := BitMachineStackEmbedding.bank readEmbedding U c.stk
  refine ⟨t, (c.var, F), ht.trans htr, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hstart, hrun, hr]
    simp only [BitMachineStackEmbedding.cfg,
      BitMachineStackEmbedding.stackCfg, BitMachineInline.cfg, hhalt]
    rfl
  · exact (BitMachineStackEmbedding.bank_at readEmbedding U c.stk (.inr 4)).trans hstatus
  · intro j
    exact (BitMachineStackEmbedding.bank_at readEmbedding U c.stk (.inl (j, 1))).trans
      (hunary j)
  · exact (BitMachineStackEmbedding.bank_at readEmbedding U c.stk (.inr 0)).trans hsource
  · exact (BitMachineStackEmbedding.bank_at readEmbedding U c.stk (.inr 2)).trans houtput
  · intro k hk
    exact BitMachineStackEmbedding.bank_outside readEmbedding U c.stk k hk

abbrev FirstLabel (q a : Nat) :=
  BitMachineRawSequence.Label CapLabel (ReadLabel q a)
abbrev FirstControl := CapControl × ReadControl

/-- Actual finite instruction table for cap preparation followed by the
existing bounded typed-row reader. -/
def firstRowProgram (q a : Nat) :=
  BitMachineRawSequence.program (capPrepareProgram (q := q))
    (readProgram q a) (readStart q a)
    ((none, none) : CapControl) readInitialControl

/-- One physically staged validated suffix is parsed into a concrete first
typed row. The global bank and every non-row writer cell are preserved. -/
theorem staged_first_row_run {n m a q : Nat}
    (suffix : List Bool) (rows : Fin m → SourceCSPCodec.Row n a q)
    (U : Stack q → List Bool) (hn : 0 < n) (hm : 0 < m)
    (hwriter : (fun k : SourceClauseRowWriterOperands.Stack q =>
        U (.inr k)) =
      SourceClauseRowWriterBlank.bank
        (SourceCSPRowQueryFrame.initial suffix []) n 0 [] [] [])
    (hread : SourceCSPCodec.readFn (SourceCSPCodec.readRow n a q) m suffix =
      some (rows, [])) :
    ∃ (t : Nat) (T : ReadControl × (Stack q → List Bool))
      (rest : List Bool),
      t ≤ 2 * n + 5 +
        q * (2 * suffix.length + 4) + 2 * a ^ q + 3 +
        q * (100 * (n + 1) ^ 2) + 2 ∧
      ((advance (firstRowProgram q a))^[t])
        (⟨some (BitMachineRawSequence.leftLabel
            (.inl .scan : CapLabel)),
          ((none, none), readInitialControl), U⟩ :
          TM2.Cfg (fun _ : Stack q => Bool)
            (FirstLabel q a) FirstControl) =
        ⟨none, ((none, none), T.1), T.2⟩ ∧
      suffix = SourceCSPCodec.rowFields (rows ⟨0, hm⟩) ++ rest ∧
      T.2 (rowSlot (.inr 4)) = [true] ∧
      (∀ j : Fin q, T.2 (rowSlot (.inl (j, 1))) =
        List.replicate ((rows ⟨0, hm⟩).1 j).val true) ∧
      T.2 (rowSlot (.inr 0)) = rest ∧
      T.2 (rowSlot (.inr 2)) =
        true :: List.ofFn (rows ⟨0, hm⟩).2 ∧
      (∀ k : Stack q, (¬ ∃ x, rowSlot x = k) → T.2 k = U k) := by
  obtain ⟨rest, hsuffix⟩ := first_row_decomposition suffix rows hm hread
  obtain ⟨tc, S1, htc, hcap, hrow1, hframe1⟩ :=
    cap_prepare_run q n suffix U hn hwriter
  have hrow2 : (fun x : SourceCSPRowQueryFrame.Stack q => S1 (rowSlot x)) =
      SourceCSPRowQueryFrame.initial
        (SourceCSPCodec.rowFields (rows ⟨0, hm⟩) ++ rest)
        (List.replicate (n - 1) true) := by
    rw [← hsuffix]
    exact hrow1
  obtain ⟨tr, F, htr, hreader, hstatus, hunary, hsource, houtput,
    hframe2⟩ := embedded_valid_first_row
      (rows ⟨0, hm⟩) hn rest S1 hrow2
  obtain ⟨t, ht, hrun⟩ := BitMachineRawSequence.runs
    (capPrepareProgram (q := q)) (readProgram q a)
    (.inl .scan : CapLabel) (readStart q a)
    ((none, none) : CapControl) (none, some true)
    readInitialControl F.1 U S1 F.2 tc tr hcap hreader
  refine ⟨t, F, rest, ?_, ?_, hsuffix, hstatus,
    hunary, hsource, houtput, ?_⟩
  · rw [hsuffix]
    omega
  · simpa only [firstRowProgram] using hrun
  · intro k hk
    rw [hframe2 k hk]
    apply hframe1 k
    intro he
    exact hk ⟨.inr 3, he.symm⟩

/-- The accepted arm of the actual raw-input selective controller supplies
all parsing and staging premises for the physical first-row program. The
assumption names an accepted global halt, not a parsed row or an abstract
reader result. -/
theorem raw_accepted_first_row_run (a q : Nat) (input : List Bool)
    (ta : Nat)
    (vr : SourceCSPRowLoopController.QueryControl ×
      SourceCSPRowLoopController.ResetControl)
    (Sa : SourceCSPGlobalDecisionProgram.Stack q → List Bool)
    (hactual : ((advance (SourceCSPGlobalDecisionProgram.program a q))^[ta])
      (SourceCSPGlobalDecisionProgram.initial a q input) =
        ⟨none, .row (vr, some true), Sa⟩) :
    ∃ (n m : Nat) (hm : 0 < m) (suffix : List Bool)
      (rows : Fin m → SourceCSPCodec.Row n a q)
      (ts : Nat) (U : Stack q → List Bool)
      (t : Nat) (T : ReadControl × (Stack q → List Bool))
      (rest : List Bool),
      0 < n ∧
      ts ≤ SourceCSPTotalSelectiveScratch.totalSelectiveBound a q input.length ∧
      ((advance (SourceCSPSelectiveStage.program a q))^[ts])
        (SourceCSPSelectiveStage.initial a q input) =
          ⟨none, (SourceCSPSelectiveStage.globalInitialControl a q,
            SourceCSPSelectiveStage.stageInitialControl), U⟩ ∧
      t ≤ 2 * n + 5 + q * (2 * suffix.length + 4) +
        2 * a ^ q + 3 + q * (100 * (n + 1) ^ 2) + 2 ∧
      ((advance (firstRowProgram q a))^[t])
        (⟨some (BitMachineRawSequence.leftLabel
          (.inl .scan : CapLabel)),
          ((none, none), readInitialControl), U⟩ :
          TM2.Cfg (fun _ : Stack q => Bool)
            (FirstLabel q a) FirstControl) =
        ⟨none, ((none, none), T.1), T.2⟩ ∧
      suffix = SourceCSPCodec.rowFields (rows ⟨0, hm⟩) ++ rest ∧
      T.2 (rowSlot (.inr 4)) = [true] ∧
      (∀ j : Fin q, T.2 (rowSlot (.inl (j, 1))) =
        List.replicate ((rows ⟨0, hm⟩).1 j).val true) ∧
      T.2 (rowSlot (.inr 0)) = rest ∧
      T.2 (rowSlot (.inr 2)) =
        true :: List.ofFn (rows ⟨0, hm⟩).2 ∧
      (∀ k : Stack q, (¬ ∃ x, rowSlot x = k) → T.2 k = U k) ∧
      (∀ g : SourceCSPGlobalDecisionProgram.Stack q,
        T.2 (.inl g) = Sa g) := by
  obtain ⟨tg, _, c, S, hglobal, ts, hts, d, U,
    hselect, hcase⟩ :=
    SourceCSPTotalSelectiveScratch.raw_total_selective a q input
  have heq := SourceCSPRowLoopTotalHaltCompare.halted_unique
    (SourceCSPGlobalDecisionProgram.program a q)
    (SourceCSPGlobalDecisionProgram.initial a q input)
    tg ta (by rw [hglobal]) (by rw [hactual])
  rw [hglobal, hactual] at heq
  have hc : c = .row (vr, some true) :=
    congrArg (fun z => z.var) heq
  have hS : S = Sa := congrArg (fun z => z.stk) heq
  rcases hcase with hreje | hzero | hacc
  · have hfalse := hreje.1
    rw [hc] at hfalse
    contradiction
  · have hzeroC := hzero.1
    rw [hc] at hzeroC
    cases hzeroC
  · obtain ⟨n, m, suffix, rows, vr', hc', hd,
      _, hn, hsize, _, hread, hsaved, hcap,
      _, _, _, _, _⟩ := hacc
    have hm : 0 < m := by
      by_contra hnot
      have hm0 : m = 0 := Nat.eq_zero_of_not_pos hnot
      subst m
      simp at hsize
      omega
    have hterminal :
        ((advance (SourceCSPGlobalDecisionProgram.program a q))^[tg])
          (SourceCSPGlobalDecisionProgram.initial a q input) =
          ⟨none, .row (vr', some true), S⟩ := by
      rw [hc'] at hglobal
      exact hglobal
    obtain ⟨_, hleft, hsource, hvertex, hblank⟩ :=
      SourceCSPTotalSelectiveFrame.accepted_any_run_full_frame
        a q input tg ts S vr' suffix
        (List.replicate (n - 1) true) d U
        hterminal hsaved hcap hselect
    have hwriter := staged_writer_eq_blank_bank q n suffix U hn
      hsource hvertex hblank
    obtain ⟨t, T, rest, ht, hrun, hsuffix, hstatus, hunary,
      hsourceFinal, houtput, hframe⟩ :=
      staged_first_row_run suffix rows U hn hm hwriter hread
    refine ⟨n, m, hm, suffix, rows, ts, U, t, T, rest,
      hn, hts, ?_, ht, hrun, hsuffix, hstatus,
      hunary, hsourceFinal, houtput, hframe, ?_⟩
    · rw [hd] at hselect
      exact hselect
    · intro g
      have hnon : ¬ ∃ x : SourceCSPRowQueryFrame.Stack q,
          rowSlot x = (.inl g : Stack q) := by
        rintro ⟨x, hx⟩
        cases hx
      rw [hframe (.inl g) hnon, hleft, hS]







end EthInapproximability.CurrentPaper.SourceCSPStagedFirstRow
