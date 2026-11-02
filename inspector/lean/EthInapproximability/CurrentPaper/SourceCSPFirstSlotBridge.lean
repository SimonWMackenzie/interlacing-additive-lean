import EthInapproximability.CurrentPaper.SourceCSPFirstRowController
import EthInapproximability.CurrentPaper.SourceClauseRowWriterNormalize
import EthInapproximability.CurrentPaper.SourceClauseRowWriterTruthFrame
import EthInapproximability.CurrentPaper.SourceClauseAllSlotsExact

/-! A physical cleanup from the first-row bank to the callback's exact bank shape. -/

namespace EthInapproximability.CurrentPaper.SourceCSPFirstSlotBridge

open Turing BitMachineEncoding BitMachineStackEmbedding
open scoped Classical

abbrev Writer (q : Nat) := SourceClauseRowWriterOperands.Stack q
abbrev Stack (q : Nat) :=
  SourceCSPGlobalDecisionProgram.Stack q ⊕
    SourceClauseRowWriterTruthFrame.Stack q

def writerEmbedding {q : Nat} : Writer q ↪ Stack q where
  toFun k := .inr (.inl k)
  inj' := by
    intro x y h
    exact Sum.inl.inj (Sum.inr.inj h)

def extended {q : Nat}
    (U : SourceCSPFirstRowController.Stack q → List Bool) :
    Stack q → List Bool :=
  Sum.elim (fun g => U (.inl g))
    (Sum.elim (fun k => U (.inr k)) (fun _ => []))

def writer {q : Nat}
    (U : SourceCSPFirstRowController.Stack q → List Bool) :
    Writer q → List Bool := fun k => U (.inr k)

def row {q : Nat}
    (U : SourceCSPFirstRowController.Stack q → List Bool) :
    SourceCSPRowQueryFrame.Stack q → List Bool :=
  fun x => U (SourceCSPStagedFirstRow.rowSlot x)

noncomputable def cleanupTime {q : Nat} (U :
    SourceCSPFirstRowController.Stack q → List Bool) : Nat :=
  (∑ i : Fin (SourceClauseClearExcept.workCount
      (SourceClauseRowWriterCleanup.keep q)),
    (writer U (SourceClauseClearExcept.workBank
      (SourceClauseRowWriterCleanup.keep q) i)).length) +
    SourceClauseClearExcept.workCount
      (SourceClauseRowWriterCleanup.keep q) + 2

noncomputable def cleanupProgram {q : Nat} :=
  fun l => stackStmt (writerEmbedding (q := q))
    (SourceClauseClearExcept.program
      (SourceClauseRowWriterCleanup.keep q) l)

theorem extended_eq_bank {q : Nat}
    (U : SourceCSPFirstRowController.Stack q → List Bool) :
    bank (writerEmbedding (q := q)) (extended U) (writer U) =
      extended U := by
  apply bank_eq_self
  intro k
  rfl

theorem cleanup_run {q : Nat}
    (U : SourceCSPFirstRowController.Stack q → List Bool) :
    ((advance (cleanupProgram (q := q)))^[cleanupTime U])
      (⟨some (.clear 0), ((), none), extended U⟩ :
        TM2.Cfg (fun _ : Stack q => Bool)
          (SourceClauseClearExcept.Label
            (SourceClauseClearExcept.workCount
              (SourceClauseRowWriterCleanup.keep q)))
          (Unit × Option Bool)) =
      ⟨none, ((), none),
        bank writerEmbedding (extended U)
          (SourceClauseRowWriterCleanup.clean (writer U))⟩ := by
  have h := BitMachineStackRun.run
    (writerEmbedding (q := q)) (extended U)
    (SourceClauseClearExcept.program
      (SourceClauseRowWriterCleanup.keep q))
    (⟨some (.clear 0), ((), none), writer U⟩) (cleanupTime U)
  rw [show ((advance (SourceClauseClearExcept.program
      (SourceClauseRowWriterCleanup.keep q)))^[cleanupTime U])
      (⟨some (.clear 0), ((), none), writer U⟩) =
      ⟨none, ((), none), SourceClauseRowWriterCleanup.clean (writer U)⟩
      from SourceClauseRowWriterCleanup.run (writer U)] at h
  simpa only [cleanupProgram, stackCfg, extended_eq_bank] using h

/-- The cleanup is a charged physical transfer to the callback's exact
starting bank. The three accumulated words are read from the incoming bank;
they are not reset. The global bank is untouched. -/
theorem cleanup_to_callback_initial {q : Nat}
    (U : SourceCSPFirstRowController.Stack q → List Bool)
    (n r : Nat) (saved output count : List Bool)
    (hsaved : writer U SourceClauseRowWriterCleanup.savedCell = saved)
    (houtput : writer U SourceClauseRowWriterCleanup.outputCell = output)
    (hcount : writer U SourceClauseRowWriterCleanup.countCell = count)
    (hn : writer U SourceClauseRowWriterOperands.vertex =
      List.replicate n true)
    (hr : writer U SourceClauseRowWriterOperands.rowIndex =
      List.replicate r true) :
    ((advance (cleanupProgram (q := q)))^[cleanupTime U])
      (⟨some (.clear 0), ((), none), extended U⟩ :
        TM2.Cfg (fun _ : Stack q => Bool)
          (SourceClauseClearExcept.Label
            (SourceClauseClearExcept.workCount
              (SourceClauseRowWriterCleanup.keep q)))
          (Unit × Option Bool)) =
      ⟨none, ((), none),
        Sum.elim (fun g => U (.inl g))
          (SourceClauseRowWriterTruthFrame.initial
            (row U) n r saved output count)⟩ := by
  rw [cleanup_run]
  have hnorm : SourceClauseRowWriterCleanup.clean (writer U) =
      SourceClauseRowWriterBlank.bank (row U) n r saved output count := by
    apply SourceClauseRowWriterNormalize.cleanup_blank
    · intro x
      rfl
    · exact hsaved
    · exact houtput
    · exact hcount
    · exact hn
    · exact hr
  rw [hnorm]
  congr 1
  funext x
  cases x with
  | inl g =>
      rw [bank_outside]
      · rfl
      · rintro ⟨k, hk⟩
        cases hk
  | inr x =>
      cases x with
      | inl k =>
          change bank writerEmbedding (extended U)
            (SourceClauseRowWriterBlank.bank (row U) n r saved output count)
              (writerEmbedding k) = _
          rw [bank_at]
          rfl
      | inr i =>
          rw [bank_outside]
          · rfl
          · rintro ⟨k, hk⟩
            cases hk


def truthEmbedding {q : Nat} :
    SourceClauseRowWriterTruthFrame.Stack q ↪ Stack q where
  toFun x := .inr x
  inj' := by
    intro x y h
    exact Sum.inr.inj h

/-- After the charged cleanup, the actual first-row all-slot circuit runs on
the *same enlarged bank*. Existing prefix accumulators are parameters read
from the incoming bank, not overwritten. -/
theorem all_slots_after_cleanup {n m q : Nat}
    (P : SourceBooleanEncoding.CSP n m 2 q) (hq : 0 < q)
    (r : Fin m) (U : SourceCSPFirstRowController.Stack q → List Bool)
    (table : Fin (2 ^ q) → Bool)
    (hrow : row U (.inr 2) = true :: List.ofFn table)
    (hunary : ∀ j : Fin q, row U (.inl (j, 1)) =
      List.replicate (row U (.inl (j, 1))).length true)
    (hquery : ∀ j : Fin q,
      SourceClauseCallback.rowQuery (row U) j = (P.query r j).val)
    (haccept : ∀ k : Fin (2 ^ q),
      table k = P.accept r (SourceClauseRowSchedule.tuple 2 q k))
    (saved output count : List Bool)
    (hsaved : writer U SourceClauseRowWriterCleanup.savedCell = saved)
    (houtput : writer U SourceClauseRowWriterCleanup.outputCell = output)
    (hcount : writer U SourceClauseRowWriterCleanup.countCell = count)
    (hn : writer U SourceClauseRowWriterOperands.vertex =
      List.replicate n true)
    (hr : writer U SourceClauseRowWriterOperands.rowIndex =
      List.replicate r.val true) :
    let C := SourceClauseCallback.AllSlots.allCircuit hq
    let first := cleanupProgram (q := q)
    let second := fun l => stackStmt (truthEmbedding (q := q)) (C.program l)
    let seq := BitMachineRawSequence.program first second
      C.start ((), none) C.initial
    ∃ t ≤ cleanupTime U +
      SourceClauseCallback.AllSlotsClock.allCost hq (row U) n r.val
        table saved output count + 1,
      ((advance seq)^[t])
        (⟨some (BitMachineRawSequence.leftLabel (.clear 0)),
          (((), none), C.initial), extended U⟩ :
          TM2.Cfg (fun _ : Stack q => Bool)
            (BitMachineRawSequence.Label
              (SourceClauseClearExcept.Label
                (SourceClauseClearExcept.workCount
                  (SourceClauseRowWriterCleanup.keep q))) C.Label)
            ((Unit × Option Bool) × C.Control)) =
        ⟨none, (((), none), C.initial),
          Sum.elim (fun g => U (.inl g))
            (SourceClauseRowWriterTruthFrame.initial (row U) n r.val
              ((EncodedCNF.clauseFields
                (SourceClauseCallback.AllSlots.actualListClauses P hq r
                  (List.ofFn (fun k : Fin (2 ^ q) => k)))).reverse ++ saved)
              output
              (List.replicate
                (SourceClauseCallback.AllSlots.actualListClauses P hq r
                  (List.ofFn (fun k : Fin (2 ^ q) => k))).length true ++ count))⟩ := by
  let C := SourceClauseCallback.AllSlots.allCircuit hq
  let B := Sum.elim (fun g => U (.inl g))
    (SourceClauseRowWriterTruthFrame.initial (row U) n r.val
      saved output count)
  let T := SourceClauseRowWriterTruthFrame.initial (row U) n r.val
    ((EncodedCNF.clauseFields
      (SourceClauseCallback.AllSlots.actualListClauses P hq r
        (List.ofFn (fun k : Fin (2 ^ q) => k)))).reverse ++ saved)
    output
    (List.replicate
      (SourceClauseCallback.AllSlots.actualListClauses P hq r
        (List.ofFn (fun k : Fin (2 ^ q) => k))).length true ++ count)
  have hfirst := cleanup_to_callback_initial U n r.val saved output count
    hsaved houtput hcount hn hr
  change ((advance (cleanupProgram (q := q)))^[cleanupTime U])
    (⟨some (.clear 0), ((), none), extended U⟩) =
    ⟨none, ((), none), B⟩ at hfirst
  obtain ⟨ts, hts, hslot⟩ :=
    SourceClauseCallback.AllSlotsExact.all_bounded_exact P hq r
      (row U) table hrow hunary hquery haccept
      saved output count
  have hbank : bank (truthEmbedding (q := q)) B
      (SourceClauseRowWriterTruthFrame.initial (row U) n r.val
        saved output count) = B := by
    apply bank_eq_self
    intro x
    rfl
  have hsecond := BitMachineStackRun.run
    (truthEmbedding (q := q)) B C.program
    (⟨some C.start, C.initial,
      SourceClauseRowWriterTruthFrame.initial (row U) n r.val
        saved output count⟩) ts
  rw [hslot] at hsecond
  have hterminal : bank (truthEmbedding (q := q)) B T =
      Sum.elim (fun g => U (.inl g)) T := by
    funext x
    cases x with
    | inl g =>
        rw [bank_outside]
        · rfl
        · rintro ⟨y, hy⟩
          cases hy
    | inr y =>
        change bank truthEmbedding B T (truthEmbedding y) = _
        rw [bank_at]
        rfl
  have hsecond' : ((advance (fun l => stackStmt truthEmbedding (C.program l)))^[ts])
      (⟨some C.start, C.initial, B⟩) =
      ⟨none, C.initial, Sum.elim (fun g => U (.inl g)) T⟩ := by
    change ((advance (fun l => stackStmt truthEmbedding (C.program l)))^[ts])
      (stackCfg truthEmbedding B
        (⟨some C.start, C.initial,
          SourceClauseRowWriterTruthFrame.initial (row U) n r.val
            saved output count⟩)) =
      ⟨none, C.initial, bank truthEmbedding B T⟩ at hsecond
    simpa only [stackCfg, hbank, hterminal] using hsecond
  obtain ⟨t, ht, hrun⟩ := BitMachineRawSequence.runs
    (cleanupProgram (q := q))
    (fun l => stackStmt truthEmbedding (C.program l))
    (.clear 0) C.start ((), none) ((), none)
    C.initial C.initial (extended U) B
    (Sum.elim (fun g => U (.inl g)) T)
    (cleanupTime U) ts hfirst hsecond'
  refine ⟨t, ?_, ?_⟩
  · omega
  · simpa only [C, B, T] using hrun


/-- The first-row body's physical vertex and row-ordinal cells are ready for
the clause callback. This strengthening uses the original staging and reader
runs, not a reconstructed bank. -/
theorem body_first_row_unary_frame {a q n m : Nat}
    (suffix : List Bool) (rows : Fin m → SourceCSPCodec.Row n a q)
    (hm : 0 < m) (hn : 0 < n)
    (B : SourceCSPFirstRowController.Stack q → List Bool)
    (hsaved : B SourceCSPSecondPassInput.savedSource = suffix)
    (hcap : B SourceCSPSecondPassInput.capSource =
      List.replicate (n - 1) true)
    (hblank : ∀ k : SourceClauseRowWriterOperands.Stack q,
      B (.inr k) = [])
    (hread : SourceCSPCodec.readFn (SourceCSPCodec.readRow n a q) m suffix =
      some (rows, [])) :
    ∃ (t : Nat) (F : SourceCSPStagedFirstRow.ReadControl ×
      (SourceCSPFirstRowController.Stack q → List Bool))
      (rest : List Bool),
      t ≤ SourceCSPFirstRowController.stageBound suffix n +
        SourceCSPFirstRowController.rowBound a q n suffix + 1 ∧
      ((advance (SourceCSPFirstRowController.bodyProgram q a))^[t])
        (⟨some (SourceCSPFirstRowController.bodyStart (q := q) (a := a)),
          SourceCSPFirstRowController.bodyInitial, B⟩ :
          TM2.Cfg (fun _ : SourceCSPFirstRowController.Stack q => Bool)
            (SourceCSPFirstRowController.BodyLabel q a)
            SourceCSPFirstRowController.BodyControl) =
        ⟨none,
          (SourceCSPFirstRowController.stageInitial,
            ((none, none), F.1)), F.2⟩ ∧
      suffix = SourceCSPCodec.rowFields (rows ⟨0, hm⟩) ++ rest ∧
      F.2 (SourceCSPStagedFirstRow.rowSlot (.inr 4)) = [true] ∧
      (∀ j : Fin q,
        F.2 (SourceCSPStagedFirstRow.rowSlot (.inl (j, 1))) =
          List.replicate ((rows ⟨0, hm⟩).1 j).val true) ∧
      F.2 (SourceCSPStagedFirstRow.rowSlot (.inr 0)) = rest ∧
      F.2 (SourceCSPStagedFirstRow.rowSlot (.inr 2)) =
        true :: List.ofFn (rows ⟨0, hm⟩).2 ∧
      (∀ g : SourceCSPGlobalDecisionProgram.Stack q,
        F.2 (.inl g) = B (.inl g)) ∧
      writer F.2 SourceClauseRowWriterOperands.vertex =
        List.replicate n true ∧
      writer F.2 SourceClauseRowWriterOperands.rowIndex = [] := by
  obtain ⟨ts, S1, hts, hstage, hglobal,
    hsource, hvertex, hblank1⟩ :=
    SourceCSPTotalSelectiveFrame.stage_input_full_frame
      q B suffix (List.replicate (n - 1) true)
      hsaved hcap hblank
  have hwriter := SourceCSPStagedFirstRow.staged_writer_eq_blank_bank
    q n suffix S1 hn hsource hvertex hblank1
  obtain ⟨tr, F, rest, htr, hrow, hsuffix, hstatus,
    hunary, hsourceFinal, houtput, hframe⟩ :=
    SourceCSPStagedFirstRow.staged_first_row_run
      suffix rows S1 hn hm hwriter hread
  obtain ⟨t, ht, hrun⟩ := BitMachineRawSequence.runs
    (SourceCSPSecondPassInput.program (q := q))
    (SourceCSPStagedFirstRow.firstRowProgram q a)
    SourceCSPFirstRowController.stageStart
    (SourceCSPFirstRowController.rowStart (q := q) (a := a))
    SourceCSPFirstRowController.stageInitial
    SourceCSPFirstRowController.stageInitial
    SourceCSPFirstRowController.rowInitial ((none, none), F.1)
    B S1 F.2 ts tr hstage hrow
  have hvertexFinal : writer F.2 SourceClauseRowWriterOperands.vertex =
      List.replicate n true := by
    have hnon : ¬ ∃ x : SourceCSPRowQueryFrame.Stack q,
        SourceCSPStagedFirstRow.rowSlot x =
          (.inr SourceClauseRowWriterOperands.vertex :
            SourceCSPFirstRowController.Stack q) := by
      rintro ⟨x, hx⟩
      cases hx
    have hstageVertex := congrFun hwriter SourceClauseRowWriterOperands.vertex
    have hv := hframe (.inr SourceClauseRowWriterOperands.vertex) hnon
    change F.2 (.inr SourceClauseRowWriterOperands.vertex) = _
    rw [hv, hstageVertex]
    exact SourceClauseRowWriterBlank.vertex _ n 0 [] [] []
  have hindexFinal : writer F.2 SourceClauseRowWriterOperands.rowIndex =
      [] := by
    have hnon : ¬ ∃ x : SourceCSPRowQueryFrame.Stack q,
        SourceCSPStagedFirstRow.rowSlot x =
          (.inr SourceClauseRowWriterOperands.rowIndex :
            SourceCSPFirstRowController.Stack q) := by
      rintro ⟨x, hx⟩
      cases hx
    have hstageIndex := congrFun hwriter SourceClauseRowWriterOperands.rowIndex
    have hi := hframe (.inr SourceClauseRowWriterOperands.rowIndex) hnon
    change F.2 (.inr SourceClauseRowWriterOperands.rowIndex) = _
    rw [hi, hstageIndex]
    exact SourceClauseRowWriterBlank.row_index _ n 0 [] [] []
  refine ⟨t, F, rest, ?_, ?_, hsuffix, hstatus,
    hunary, hsourceFinal, houtput, ?_, hvertexFinal, hindexFinal⟩
  · unfold SourceCSPFirstRowController.stageBound
      SourceCSPFirstRowController.rowBound
    simp only [List.length_replicate] at hts
    omega
  · simpa only [SourceCSPFirstRowController.bodyProgram] using hrun
  · intro g
    have hnon : ¬ ∃ x : SourceCSPRowQueryFrame.Stack q,
        SourceCSPStagedFirstRow.rowSlot x =
          (.inl g : SourceCSPFirstRowController.Stack q) := by
      rintro ⟨x, hx⟩
      cases hx
    rw [hframe (.inl g) hnon, hglobal]


/-- Accepted validator output reaches a first-row halt with unary vertex
count and zero row ordinal physically present on its writer bank. -/
theorem accepted_first_row_ready {a q n m : Nat}
    (input suffix : List Bool)
    (rows : Fin m → SourceCSPCodec.Row n a q)
    (tg : Nat)
    (vr : SourceCSPRowLoopController.QueryControl ×
      SourceCSPRowLoopController.ResetControl)
    (S : SourceCSPGlobalDecisionProgram.Stack q → List Bool)
    (hn : 0 < n) (hm : 0 < m)
    (hglobal : ((advance (SourceCSPGlobalDecisionProgram.program a q))^[tg])
      (SourceCSPGlobalDecisionProgram.initial a q input) =
        ⟨none, .row (vr, some true), S⟩)
    (hsaved : S SourceCSPGlobalDecisionProgram.savedSource = suffix)
    (hcap : S SourceCSPHeaderRowBridge.capSource =
      List.replicate (n - 1) true)
    (hread : SourceCSPCodec.readFn (SourceCSPCodec.readRow n a q) m suffix =
      some (rows, [])) :
    ∃ (t : Nat) (U : SourceCSPFirstRowController.Stack q → List Bool)
      (rest : List Bool)
      (v : SourceCSPFirstRowController.Control a q),
      t ≤ tg + 1 + SourceCSPFirstRowController.stageBound suffix n +
        SourceCSPFirstRowController.rowBound a q n suffix + 1 ∧
      ((advance (SourceCSPFirstRowController.program a q))^[t])
        (SourceCSPFirstRowController.initial a q input) =
          ⟨none, v, U⟩ ∧
      suffix = SourceCSPCodec.rowFields (rows ⟨0, hm⟩) ++ rest ∧
      (∀ j : Fin q,
        row U (.inl (j, 1)) =
          List.replicate ((rows ⟨0, hm⟩).1 j).val true) ∧
      row U (.inr 2) = true :: List.ofFn (rows ⟨0, hm⟩).2 ∧
      row U (.inr 0) = rest ∧
      row U (.inr 4) = [true] ∧
      (∀ g : SourceCSPGlobalDecisionProgram.Stack q,
        U (.inl g) = S g) ∧
      writer U SourceClauseRowWriterOperands.vertex =
        List.replicate n true ∧
      writer U SourceClauseRowWriterOperands.rowIndex = [] := by
  obtain ⟨u, B, hu, hglobalRun, hleft, hblank⟩ :=
    SourceCSPFirstRowController.global_handoff a q input tg
      (.row (vr, some true)) S hglobal
  have hsavedB : B SourceCSPSecondPassInput.savedSource = suffix := by
    change B (.inl SourceCSPGlobalDecisionProgram.savedSource) = suffix
    exact (hleft _).trans hsaved
  have hcapB : B SourceCSPSecondPassInput.capSource =
      List.replicate (n - 1) true := by
    change B (.inl SourceCSPHeaderRowBridge.capSource) = _
    exact (hleft _).trans hcap
  obtain ⟨tb, F, rest, htb, hbody, hsuffix,
    _hstatus, hunary, hsource, houtput, hglobalFinal,
    hvertexFinal, hindexFinal⟩ :=
    body_first_row_unary_frame suffix rows hm hn B
      hsavedB hcapB hblank hread
  let cb : TM2.Cfg (fun _ : SourceCSPFirstRowController.Stack q => Bool)
      (SourceCSPFirstRowController.BodyLabel q a)
      SourceCSPFirstRowController.BodyControl :=
    ⟨some (SourceCSPFirstRowController.bodyStart (q := q) (a := a)),
      SourceCSPFirstRowController.bodyInitial, B⟩
  have hbh : (((advance (SourceCSPFirstRowController.bodyProgram q a))^[tb])
      cb).l = none := by
    rw [show cb = (⟨some (SourceCSPFirstRowController.bodyStart
      (q := q) (a := a)), SourceCSPFirstRowController.bodyInitial, B⟩ :
      TM2.Cfg (fun _ : SourceCSPFirstRowController.Stack q => Bool)
        (SourceCSPFirstRowController.BodyLabel q a)
        SourceCSPFirstRowController.BodyControl) by rfl, hbody]
  obtain ⟨vtime, hvtime, hinline⟩ := BitMachineInline.outputs
    BitMachineRawSequence.rightLabel
    (fun w => (SourceCSPSelectiveStage.globalInitialControl a q, w))
    Prod.snd (fun _ => rfl) none
    (SourceCSPFirstRowController.bodyProgram q a)
    (SourceCSPFirstRowController.program a q)
    (by intro l; rfl) cb tb hbh
  have hstart : BitMachineInline.cfg BitMachineRawSequence.rightLabel
      (fun w => (SourceCSPSelectiveStage.globalInitialControl a q, w))
      none cb =
      (⟨some (BitMachineRawSequence.rightLabel
          (SourceCSPFirstRowController.bodyStart (q := q) (a := a))),
        (SourceCSPSelectiveStage.globalInitialControl a q,
          SourceCSPFirstRowController.bodyInitial), B⟩ :
        TM2.Cfg (fun _ : SourceCSPFirstRowController.Stack q => Bool)
          (SourceCSPFirstRowController.Label a q)
          (SourceCSPFirstRowController.Control a q)) := rfl
  have hjoin : ((advance (SourceCSPFirstRowController.program a q))^[
      u + 1 + vtime]) (SourceCSPFirstRowController.initial a q input) =
      ⟨none,
        (SourceCSPSelectiveStage.globalInitialControl a q,
          (SourceCSPFirstRowController.stageInitial,
            ((none, none), F.1))), F.2⟩ := by
    rw [show u + 1 + vtime = vtime + (u + 1) by omega,
      Function.iterate_add_apply,
      Function.iterate_succ_apply', hglobalRun,
      SourceCSPFirstRowController.handoff_accepted a q vr B,
      ← hstart, hinline,
      show cb = (⟨some (SourceCSPFirstRowController.bodyStart
        (q := q) (a := a)),
        SourceCSPFirstRowController.bodyInitial, B⟩ :
        TM2.Cfg (fun _ : SourceCSPFirstRowController.Stack q => Bool)
          (SourceCSPFirstRowController.BodyLabel q a)
          SourceCSPFirstRowController.BodyControl) by rfl,
      hbody]
    rfl
  refine ⟨u + 1 + vtime, F.2, rest,
    (SourceCSPSelectiveStage.globalInitialControl a q,
      (SourceCSPFirstRowController.stageInitial,
        ((none, none), F.1))), ?_, hjoin,
    hsuffix, hunary, houtput, hsource, _hstatus,
    ?_, hvertexFinal, hindexFinal⟩
  · omega
  · intro g
    exact (hglobalFinal g).trans (hleft g)


/-- The callback's source-row correspondence is obtained from the parsed
Boolean row itself. The accumulated words can be whatever the incoming bank
actually contains (for example, after a future prefix-clause phase). -/
theorem typed_first_row_all_slots {n m q : Nat}
    (hq : 0 < q) (hm : 0 < m)
    (rows : Fin m → SourceCSPCodec.Row n 2 q)
    (U : SourceCSPFirstRowController.Stack q → List Bool)
    (htruth : row U (.inr 2) =
      true :: List.ofFn (rows ⟨0, hm⟩).2)
    (hquery : ∀ j : Fin q,
      row U (.inl (j, 1)) =
        List.replicate ((rows ⟨0, hm⟩).1 j).val true)
    (hn : writer U SourceClauseRowWriterOperands.vertex =
      List.replicate n true)
    (hr : writer U SourceClauseRowWriterOperands.rowIndex = []) :
    let P := (SourceCSPCodec.fromRows n m 2 q rows).system
    let r : Fin m := ⟨0, hm⟩
    let saved := writer U SourceClauseRowWriterCleanup.savedCell
    let output := writer U SourceClauseRowWriterCleanup.outputCell
    let count := writer U SourceClauseRowWriterCleanup.countCell
    let C := SourceClauseCallback.AllSlots.allCircuit hq
    let seq := BitMachineRawSequence.program (cleanupProgram (q := q))
      (fun l => stackStmt (truthEmbedding (q := q)) (C.program l))
      C.start ((), none) C.initial
    ∃ t ≤ cleanupTime U +
      SourceClauseCallback.AllSlotsClock.allCost hq (row U) n r.val
        (rows r).2 saved output count + 1,
      ((advance seq)^[t])
        (⟨some (BitMachineRawSequence.leftLabel (.clear 0)),
          (((), none), C.initial), extended U⟩ :
          TM2.Cfg (fun _ : Stack q => Bool)
            (BitMachineRawSequence.Label
              (SourceClauseClearExcept.Label
                (SourceClauseClearExcept.workCount
                  (SourceClauseRowWriterCleanup.keep q))) C.Label)
            ((Unit × Option Bool) × C.Control)) =
        ⟨none, (((), none), C.initial),
          Sum.elim (fun g => U (.inl g))
            (SourceClauseRowWriterTruthFrame.initial (row U) n r.val
              ((EncodedCNF.clauseFields
                (SourceClauseCallback.AllSlots.actualListClauses P hq r
                  (List.ofFn (fun k : Fin (2 ^ q) => k)))).reverse ++ saved)
              output
              (List.replicate
                (SourceClauseCallback.AllSlots.actualListClauses P hq r
                  (List.ofFn (fun k : Fin (2 ^ q) => k))).length true ++ count))⟩ := by
  let P := (SourceCSPCodec.fromRows n m 2 q rows).system
  let r : Fin m := ⟨0, hm⟩
  have hu : ∀ j : Fin q, row U (.inl (j, 1)) =
      List.replicate (row U (.inl (j, 1))).length true := by
    intro j
    rw [hquery j]
    simp
  have hqP : ∀ j : Fin q,
      SourceClauseCallback.rowQuery (row U) j = (P.query r j).val := by
    intro j
    simp [SourceClauseCallback.rowQuery, P,
      SourceCSPCodec.fromRows, hquery j, r]
  have haP : ∀ k : Fin (2 ^ q),
      (rows r).2 k = P.accept r (SourceClauseRowSchedule.tuple 2 q k) := by
    intro k
    simp [P, r, SourceCSPCodec.fromRows,
      SourceClauseRowSchedule.tuple]
  simpa only [P, r] using
    all_slots_after_cleanup P hq r U (rows r).2
      htruth hu hqP haP
      (writer U SourceClauseRowWriterCleanup.savedCell)
      (writer U SourceClauseRowWriterCleanup.outputCell)
      (writer U SourceClauseRowWriterCleanup.countCell)
      rfl rfl rfl hn (by simpa using hr)


end EthInapproximability.CurrentPaper.SourceCSPFirstSlotBridge
