import EthInapproximability.CurrentPaper.SourceCSPFirstSlotBridge
import EthInapproximability.CurrentPaper.SourceCSPRowLoopReset
import EthInapproximability.CurrentPaper.SourceClauseRowWriterRowAdvance

/-! Physical next-row restart on the callback's global-plus-writer bank. -/

namespace EthInapproximability.CurrentPaper.SourceCSPNextRowBridge

open Turing BitMachineEncoding BitMachineStackEmbedding
open scoped Classical

abbrev Stack (q : Nat) := SourceCSPFirstSlotBridge.Stack q

def resetCell {q : Nat} : SourceCSPRowLoopReset.Stack q → Stack q
  | .inl x => .inr (SourceClauseRowWriterTruthFrame.rowCell x)
  | .inr 0 => .inr (.inl SourceClauseRowWriterOperands.rowIndex)
  | .inr 1 => .inl SourceCSPHeaderRowBridge.capSource
  | .inr 2 => .inr (.inl SourceClauseRowWriterCleanup.savedCell)
  | .inr 3 => .inr (.inl SourceClauseRowWriterOperands.scratch)

def resetEmbedding {q : Nat} : SourceCSPRowLoopReset.Stack q ↪ Stack q where
  toFun := resetCell
  inj' := by
    intro x y h
    cases x with
    | inl x =>
        cases y with
        | inl y =>
            simp [resetCell, SourceClauseRowWriterTruthFrame.rowCell,
              SourceClauseRowWriterCleanup.rowCell] at h
            exact congrArg Sum.inl h
        | inr y => fin_cases y <;>
            simp [resetCell, SourceClauseRowWriterTruthFrame.rowCell,
              SourceClauseRowWriterCleanup.rowCell,
              SourceClauseRowWriterOperands.rowIndex,
              SourceClauseRowWriterOperands.scratch,
              SourceClauseRowWriterCleanup.savedCell] at h
    | inr x =>
        cases y with
        | inl y => fin_cases x <;>
            simp [resetCell, SourceClauseRowWriterTruthFrame.rowCell,
              SourceClauseRowWriterCleanup.rowCell,
              SourceClauseRowWriterOperands.rowIndex,
              SourceClauseRowWriterOperands.scratch,
              SourceClauseRowWriterCleanup.savedCell] at h
        | inr y => fin_cases x <;> fin_cases y <;>
            simp [resetCell, SourceClauseRowWriterOperands.rowIndex,
              SourceClauseRowWriterOperands.scratch,
              SourceClauseRowWriterCleanup.savedCell] at h ⊢

def rowEmbedding {q : Nat} : SourceCSPRowQueryFrame.Stack q ↪ Stack q :=
  ⟨fun x => resetEmbedding (.inl x), by
    intro x y h
    exact Sum.inl.inj (resetEmbedding.injective h)⟩

def resetProjection {q : Nat} (B : Stack q → List Bool) :
    SourceCSPRowLoopReset.Stack q → List Bool :=
  fun x => B (resetEmbedding x)

noncomputable def resetResult {q : Nat} (B : Stack q → List Bool)
    (rest cap : List Bool) : Stack q → List Bool :=
  bank resetEmbedding B
    (Sum.elim (SourceCSPRowQueryFrame.initial rest cap)
      (fun k => resetProjection B (.inr k)))

noncomputable def resetCost {q : Nat} (B : Stack q → List Bool)
    (cap : List Bool) : Nat :=
  (∑ i : Fin (q * 5 + 4),
    (resetProjection B (SourceCSPRowLoopClear.scratch q i)).length) +
      (q * 5 + 4) + 2 + (2 * cap.length + 2) + 1

noncomputable def resetProgram (q : Nat) :=
  fun l => stackStmt (resetEmbedding (q := q))
    (SourceCSPRowLoopReset.program q l)

/-- The existing row-loop reset physically clears the old row/query/status
region and restores the cap from the global validator bank. -/
theorem reset_run (q : Nat) (B : Stack q → List Bool)
    (rest cap : List Bool)
    (hrest : B (rowEmbedding (.inr 0)) = rest)
    (hcap : B (.inl SourceCSPHeaderRowBridge.capSource) = cap)
    (hscratch : B (.inr (.inl SourceClauseRowWriterOperands.scratch)) = []) :
    ∃ t ≤ resetCost B cap,
      ((advance (resetProgram q))^[t])
        (⟨some (BitMachineRawSequence.leftLabel 0),
          (((), none), none), B⟩ :
          TM2.Cfg (fun _ : Stack q => Bool)
            (SourceCSPRowLoopReset.Label q)
            SourceCSPRowLoopReset.Control) =
        ⟨none, (((), none), none), resetResult B rest cap⟩ := by
  let R := resetProjection B
  have hbank : bank resetEmbedding B R = B := by
    apply bank_eq_self
    intro x
    rfl
  have hr : R (.inl (.inr 0)) = rest := by
    simpa only [R, resetProjection, rowEmbedding, resetEmbedding,
      resetCell] using hrest
  have hc : R (.inr 1) = cap := by
    simpa only [R, resetProjection, resetEmbedding,
      resetCell] using hcap
  have hs : R (.inr 3) = [] := by
    simpa only [R, resetProjection, resetEmbedding,
      resetCell] using hscratch
  obtain ⟨t, ht, hrun⟩ :=
    SourceCSPRowLoopReset.reset_run q R rest cap hr hc hs
  have hinline := BitMachineStackRun.run resetEmbedding B
    (SourceCSPRowLoopReset.program q)
    (⟨some (BitMachineRawSequence.leftLabel 0),
      (((), none), none), R⟩) t
  rw [hrun] at hinline
  refine ⟨t, ?_, ?_⟩
  · simpa only [resetCost, R, resetProjection] using ht
  · simpa only [resetProgram, stackCfg, hbank,
      resetResult, R, resetProjection] using hinline

theorem reset_row_initial {q : Nat} (B : Stack q → List Bool)
    (rest cap : List Bool) (x : SourceCSPRowQueryFrame.Stack q) :
    resetResult B rest cap (rowEmbedding x) =
      SourceCSPRowQueryFrame.initial rest cap x := by
  change bank resetEmbedding B _ (resetEmbedding (.inl x)) = _
  rw [bank_at]
  rfl

theorem reset_global_frame {q : Nat} (B : Stack q → List Bool)
    (rest cap : List Bool)
    (g : SourceCSPGlobalDecisionProgram.Stack q) :
    resetResult B rest cap (.inl g) = B (.inl g) := by
  by_cases hg : g = SourceCSPHeaderRowBridge.capSource
  · subst g
    change bank resetEmbedding B _ (resetEmbedding (.inr 1)) = _
    rw [bank_at]
    rfl
  · apply bank_outside
    rintro ⟨x, hx⟩
    cases x with
    | inl x => cases hx
    | inr i =>
        fin_cases i <;>
          simp [resetEmbedding, resetCell] at hx
        exact hg hx.symm

theorem reset_nonrow_frame {q : Nat} (B : Stack q → List Bool)
    (rest cap : List Bool)
    (k : SourceClauseRowWriterOperands.Stack q)
    (hk : ∀ x : SourceCSPRowQueryFrame.Stack q,
      k ≠ SourceClauseRowWriterCleanup.rowCell x) :
    resetResult B rest cap
      (SourceCSPFirstSlotBridge.writerEmbedding k) =
        B (SourceCSPFirstSlotBridge.writerEmbedding k) := by
  by_cases h : ∃ x, resetEmbedding x =
      SourceCSPFirstSlotBridge.writerEmbedding k
  · obtain ⟨x, hx⟩ := h
    cases x with
    | inl x =>
        have he : k = SourceClauseRowWriterCleanup.rowCell x := by
          have hh := Sum.inl.inj (Sum.inr.inj hx.symm)
          exact hh
        exact False.elim (hk x he)
    | inr i =>
        rw [← hx, resetResult, bank_at]
        rfl
  · exact bank_outside resetEmbedding B _ _ h

theorem reset_cursor_frame {q : Nat} (B : Stack q → List Bool)
    (rest cap : List Bool) (i : Fin 2) :
    resetResult B rest cap (.inr (.inr i)) = B (.inr (.inr i)) := by
  apply bank_outside
  rintro ⟨x, hx⟩
  cases x with
  | inl x => cases hx
  | inr j => fin_cases j <;> cases hx

noncomputable def parseProgram (q a : Nat) :=
  fun l => stackStmt (rowEmbedding (q := q))
    (SourceCSPRowQueryFrame.combinedProgram q (a ^ q) l)

/-- A typed next row is read from the exact remaining source word. The
query labels and truth bits are produced by the physical parser and range
checker; no query-answer oracle enters the starting configuration. -/
theorem parse_next_row {n a q : Nat}
    (next : SourceCSPCodec.Row n a q)
    (B : Stack q → List Bool) (rest tail : List Bool) (L : Nat)
    (hn : 0 < n)
    (hrest : rest = SourceCSPCodec.rowFields next ++ tail)
    (hword : ∀ j : Fin q, (next.1 j).val.bits.length ≤ L)
    (hcapL : n - 1 ≤ L) :
    ∃ (t : Nat)
      (v : SourceCSPRowController.Control × SourceCSPQueryBank.Control)
      (V : SourceCSPRowQueryFrame.Stack q → List Bool),
      t ≤ q * (2 * (SourceCSPCodec.rowFields next ++ tail).length + 4) +
        2 * a ^ q + 3 + q * (100 * (L + 1) ^ 2) + 2 ∧
      ((advance (parseProgram q a))^[t])
        (⟨some (BitMachineRawSequence.leftLabel
            (.start 0 : SourceCSPRowController.Label q (a ^ q))),
          ((none, none), (((none, none), (none, false)), none)),
          resetResult B rest (List.replicate (n - 1) true)⟩ :
          TM2.Cfg (fun _ : Stack q => Bool)
            (BitMachineRawSequence.Label
              (SourceCSPRowController.Label q (a ^ q))
              (SourceCSPQueryBank.Label q))
            (SourceCSPRowController.Control × SourceCSPQueryBank.Control)) =
        ⟨none, v,
          bank rowEmbedding
            (resetResult B rest (List.replicate (n - 1) true)) V⟩ ∧
      V (.inr 0) = tail ∧ V (.inr 4) = [true] ∧
      (∀ j : Fin q, V (.inl (j, 1)) =
        List.replicate (next.1 j).val true) ∧
      V (.inr 2) = true :: List.ofFn next.2 := by
  obtain ⟨t, c, ht, hrun, hhalt, hstatus,
    hunary, hsource, houtput⟩ :=
    SourceCSPRowQueryUnary.combined_valid_row_unary
      next hn tail L hword hcapL
  let R := resetResult B rest (List.replicate (n - 1) true)
  let C : TM2.Cfg (fun _ : SourceCSPRowQueryFrame.Stack q => Bool)
      (BitMachineRawSequence.Label
        (SourceCSPRowController.Label q (a ^ q))
        (SourceCSPQueryBank.Label q))
      (SourceCSPRowController.Control × SourceCSPQueryBank.Control) :=
    ⟨some (BitMachineRawSequence.leftLabel
        (.start 0 : SourceCSPRowController.Label q (a ^ q))),
      ((none, none), (((none, none), (none, false)), none)),
      SourceCSPRowQueryFrame.initial
        (SourceCSPCodec.rowFields next ++ tail)
        (List.replicate (n - 1) true)⟩
  have hR : bank rowEmbedding R C.stk = R := by
    apply bank_eq_self
    intro x
    change SourceCSPRowQueryFrame.initial
      (SourceCSPCodec.rowFields next ++ tail)
      (List.replicate (n - 1) true) x =
      resetResult B rest (List.replicate (n - 1) true)
        (rowEmbedding x)
    rw [reset_row_initial]
    rw [hrest]
  have he := BitMachineStackRun.run rowEmbedding R
    (SourceCSPRowQueryFrame.combinedProgram q (a ^ q)) C t
  rw [show ((advance (SourceCSPRowQueryFrame.combinedProgram q (a ^ q)))^[t])
      C = c from hrun] at he
  rcases c with ⟨lc, vc, V⟩
  cases lc with
  | some l => cases hhalt
  | none =>
      refine ⟨t, vc, V, ht, ?_, hsource, hstatus, hunary, houtput⟩
      simpa only [parseProgram, stackCfg, hR, C, R] using he

theorem parsed_nonrow_frame {q : Nat} (B : Stack q → List Bool)
    (V : SourceCSPRowQueryFrame.Stack q → List Bool)
    (k : SourceClauseRowWriterOperands.Stack q)
    (hk : ∀ x : SourceCSPRowQueryFrame.Stack q,
      k ≠ SourceClauseRowWriterCleanup.rowCell x) :
    bank rowEmbedding B V
      (SourceCSPFirstSlotBridge.writerEmbedding k) =
        B (SourceCSPFirstSlotBridge.writerEmbedding k) := by
  apply bank_outside
  rintro ⟨x, hx⟩
  have he : k = SourceClauseRowWriterCleanup.rowCell x :=
    Sum.inl.inj (Sum.inr.inj hx.symm)
  exact hk x he

theorem parsed_global_frame {q : Nat} (B : Stack q → List Bool)
    (V : SourceCSPRowQueryFrame.Stack q → List Bool)
    (g : SourceCSPGlobalDecisionProgram.Stack q) :
    bank rowEmbedding B V (.inl g) = B (.inl g) := by
  apply bank_outside
  rintro ⟨x, hx⟩
  cases hx

theorem parsed_cursor_frame {q : Nat} (B : Stack q → List Bool)
    (V : SourceCSPRowQueryFrame.Stack q → List Bool)
    (i : Fin 2) :
    bank rowEmbedding B V (.inr (.inr i)) = B (.inr (.inr i)) := by
  apply bank_outside
  rintro ⟨x, hx⟩
  cases hx

def writerProjection {q : Nat} (B : Stack q → List Bool) :
    SourceClauseRowWriterOperands.Stack q → List Bool :=
  fun k => B (SourceCSPFirstSlotBridge.writerEmbedding k)

noncomputable def advanceResult {q : Nat} (B : Stack q → List Bool) :
    Stack q → List Bool :=
  bank SourceCSPFirstSlotBridge.writerEmbedding B
    (Function.update (writerProjection B)
      SourceClauseRowWriterOperands.rowIndex
      (true :: writerProjection B SourceClauseRowWriterOperands.rowIndex))

noncomputable def advanceProgram (q : Nat) :=
  fun l => stackStmt (SourceCSPFirstSlotBridge.writerEmbedding (q := q))
    (SourceClauseRowWriterRowAdvance.program l)

theorem advance_run (q : Nat) (B : Stack q → List Bool) :
    ((advance (advanceProgram q))^[2])
      (⟨some .push, (), B⟩ :
        TM2.Cfg (fun _ : Stack q => Bool)
          SourceClauseRowWriterRowAdvance.Label Unit) =
      ⟨none, (), advanceResult B⟩ := by
  have hbank : bank SourceCSPFirstSlotBridge.writerEmbedding B
      (writerProjection B) = B := by
    apply bank_eq_self
    intro x
    rfl
  have he := BitMachineStackRun.run
    (SourceCSPFirstSlotBridge.writerEmbedding (q := q)) B
    (SourceClauseRowWriterRowAdvance.program (q := q))
    (⟨some .push, (), writerProjection B⟩) 2
  rw [SourceClauseRowWriterRowAdvance.run] at he
  simpa only [advanceProgram, stackCfg, hbank, advanceResult] using he

theorem advance_index {q : Nat} (B : Stack q → List Bool)
    (r : Nat)
    (hr : writerProjection B SourceClauseRowWriterOperands.rowIndex =
      List.replicate r true) :
    advanceResult B
      (SourceCSPFirstSlotBridge.writerEmbedding
        SourceClauseRowWriterOperands.rowIndex) =
        List.replicate (r + 1) true := by
  change bank SourceCSPFirstSlotBridge.writerEmbedding B
    (Function.update (writerProjection B)
      SourceClauseRowWriterOperands.rowIndex
      (true :: writerProjection B SourceClauseRowWriterOperands.rowIndex))
      (SourceCSPFirstSlotBridge.writerEmbedding
        SourceClauseRowWriterOperands.rowIndex) = _
  rw [bank_at]
  exact SourceClauseRowWriterRowAdvance.row_increment
    (writerProjection B) r hr

theorem advance_writer_frame {q : Nat} (B : Stack q → List Bool)
    (k : SourceClauseRowWriterOperands.Stack q)
    (hk : k ≠ SourceClauseRowWriterOperands.rowIndex) :
    advanceResult B (SourceCSPFirstSlotBridge.writerEmbedding k) =
      B (SourceCSPFirstSlotBridge.writerEmbedding k) := by
  change bank SourceCSPFirstSlotBridge.writerEmbedding B
    (Function.update (writerProjection B)
      SourceClauseRowWriterOperands.rowIndex
      (true :: writerProjection B SourceClauseRowWriterOperands.rowIndex))
      (SourceCSPFirstSlotBridge.writerEmbedding k) = _
  rw [bank_at, Function.update_of_ne hk]
  rfl

theorem advance_row_frame {q : Nat} (B : Stack q → List Bool)
    (x : SourceCSPRowQueryFrame.Stack q) :
    advanceResult B (rowEmbedding x) = B (rowEmbedding x) := by
  apply advance_writer_frame
  cases x <;> simp [SourceClauseRowWriterCleanup.rowCell,
    SourceClauseRowWriterOperands.rowIndex]

theorem advance_global_frame {q : Nat} (B : Stack q → List Bool)
    (g : SourceCSPGlobalDecisionProgram.Stack q) :
    advanceResult B (.inl g) = B (.inl g) := by
  apply bank_outside
  rintro ⟨k, hk⟩
  cases hk

theorem advance_cursor_frame {q : Nat} (B : Stack q → List Bool)
    (i : Fin 2) :
    advanceResult B (.inr (.inr i)) = B (.inr (.inr i)) := by
  apply bank_outside
  rintro ⟨k, hk⟩
  cases hk

noncomputable def parsedResult {q : Nat} (B : Stack q → List Bool)
    (rest cap : List Bool)
    (V : SourceCSPRowQueryFrame.Stack q → List Bool) : Stack q → List Bool :=
  bank rowEmbedding (resetResult B rest cap) V

noncomputable def steppedResult {q : Nat} (B : Stack q → List Bool)
    (rest cap : List Bool)
    (V : SourceCSPRowQueryFrame.Stack q → List Bool) : Stack q → List Bool :=
  advanceResult (parsedResult B rest cap V)

theorem stepped_writer_frame {q : Nat} (B : Stack q → List Bool)
    (rest cap : List Bool)
    (V : SourceCSPRowQueryFrame.Stack q → List Bool)
    (k : SourceClauseRowWriterOperands.Stack q)
    (hkrow : ∀ x : SourceCSPRowQueryFrame.Stack q,
      k ≠ SourceClauseRowWriterCleanup.rowCell x)
    (hkindex : k ≠ SourceClauseRowWriterOperands.rowIndex) :
    steppedResult B rest cap V
      (SourceCSPFirstSlotBridge.writerEmbedding k) =
        B (SourceCSPFirstSlotBridge.writerEmbedding k) := by
  rw [steppedResult, advance_writer_frame _ k hkindex,
    parsedResult, parsed_nonrow_frame _ V k hkrow,
    reset_nonrow_frame B rest cap k hkrow]

theorem stepped_row (B : Stack q → List Bool)
    (rest cap : List Bool)
    (V : SourceCSPRowQueryFrame.Stack q → List Bool) :
    (fun x => steppedResult B rest cap V (rowEmbedding x)) = V := by
  funext x
  rw [steppedResult, advance_row_frame,
    parsedResult, bank_at]

theorem stepped_global (B : Stack q → List Bool)
    (rest cap : List Bool)
    (V : SourceCSPRowQueryFrame.Stack q → List Bool)
    (g : SourceCSPGlobalDecisionProgram.Stack q) :
    steppedResult B rest cap V (.inl g) = B (.inl g) := by
  rw [steppedResult, advance_global_frame, parsedResult,
    parsed_global_frame, reset_global_frame]

theorem stepped_cursor (B : Stack q → List Bool)
    (rest cap : List Bool)
    (V : SourceCSPRowQueryFrame.Stack q → List Bool)
    (i : Fin 2) :
    steppedResult B rest cap V (.inr (.inr i)) =
      B (.inr (.inr i)) := by
  rw [steppedResult, advance_cursor_frame, parsedResult,
    parsed_cursor_frame, reset_cursor_frame]

theorem stepped_index (B : Stack q → List Bool)
    (rest cap : List Bool)
    (V : SourceCSPRowQueryFrame.Stack q → List Bool)
    (r : Nat)
    (hr : writerProjection B SourceClauseRowWriterOperands.rowIndex =
      List.replicate r true) :
    writerProjection (steppedResult B rest cap V)
      SourceClauseRowWriterOperands.rowIndex =
        List.replicate (r + 1) true := by
  have hk : ∀ x : SourceCSPRowQueryFrame.Stack q,
      SourceClauseRowWriterOperands.rowIndex ≠
        SourceClauseRowWriterCleanup.rowCell x := by
    intro x
    cases x <;> simp [SourceClauseRowWriterOperands.rowIndex,
      SourceClauseRowWriterCleanup.rowCell]
  apply advance_index
  rw [writerProjection, parsedResult,
    parsed_nonrow_frame _ V _ hk,
    reset_nonrow_frame B rest cap _ hk]
  exact hr

theorem remaining_rows_succ {n a q m : Nat}
    (rows : Fin (m + 1) → SourceCSPCodec.Row n a q) :
    SourceCSPCodec.fnFields SourceCSPCodec.rowFields rows =
      SourceCSPCodec.rowFields (rows 0) ++
        SourceCSPCodec.fnFields SourceCSPCodec.rowFields
          (fun j : Fin m => rows j.succ) :=
  SourceCSPCodec.fnFields_succ SourceCSPCodec.rowFields rows

def currentRow {q : Nat} (B : Stack q → List Bool) :
    SourceCSPRowQueryFrame.Stack q → List Bool :=
  fun x => B (rowEmbedding x)

noncomputable def callbackResult {q : Nat}
    (B : Stack q → List Bool) (n r : Nat) : Stack q → List Bool :=
  Sum.elim (fun g => B (.inl g))
    (SourceClauseRowWriterTruthFrame.initial
      (currentRow B) n r
      (writerProjection B SourceClauseRowWriterCleanup.savedCell)
      (writerProjection B SourceClauseRowWriterCleanup.outputCell)
      (writerProjection B SourceClauseRowWriterCleanup.countCell))

noncomputable def callbackCleanupTime {q : Nat}
    (B : Stack q → List Bool) : Nat :=
  (∑ i : Fin (SourceClauseClearExcept.workCount
      (SourceClauseRowWriterCleanup.keep q)),
    (writerProjection B (SourceClauseClearExcept.workBank
      (SourceClauseRowWriterCleanup.keep q) i)).length) +
    SourceClauseClearExcept.workCount
      (SourceClauseRowWriterCleanup.keep q) + 2

/-- Normalization runs on the current bank. It keeps existing accumulator
words, and its only extra premise is that the two callback cursor cells are
already empty (as they are at AllSlotsExact's terminal bank). -/
theorem callback_cleanup_run {q : Nat} (B : Stack q → List Bool)
    (n r : Nat)
    (hcursor : ∀ i : Fin 2, B (.inr (.inr i)) = [])
    (hn : writerProjection B SourceClauseRowWriterOperands.vertex =
      List.replicate n true)
    (hr : writerProjection B SourceClauseRowWriterOperands.rowIndex =
      List.replicate r true) :
    ((advance (SourceCSPFirstSlotBridge.cleanupProgram (q := q)))^[
      callbackCleanupTime B])
      (⟨some (.clear 0), ((), none), B⟩ :
        TM2.Cfg (fun _ : Stack q => Bool)
          (SourceClauseClearExcept.Label
            (SourceClauseClearExcept.workCount
              (SourceClauseRowWriterCleanup.keep q)))
          (Unit × Option Bool)) =
      ⟨none, ((), none), callbackResult B n r⟩ := by
  let W := writerProjection B
  have hbank : bank SourceCSPFirstSlotBridge.writerEmbedding B W = B := by
    apply bank_eq_self
    intro k
    rfl
  have hnorm : SourceClauseRowWriterCleanup.clean W =
      SourceClauseRowWriterBlank.bank (currentRow B) n r
        (W SourceClauseRowWriterCleanup.savedCell)
        (W SourceClauseRowWriterCleanup.outputCell)
        (W SourceClauseRowWriterCleanup.countCell) := by
    apply SourceClauseRowWriterNormalize.cleanup_blank
    · intro x
      rfl
    · rfl
    · rfl
    · rfl
    · exact hn
    · exact hr
  have he := BitMachineStackRun.run
    (SourceCSPFirstSlotBridge.writerEmbedding (q := q)) B
    (SourceClauseClearExcept.program
      (SourceClauseRowWriterCleanup.keep q))
    (⟨some (.clear 0), ((), none), W⟩) (callbackCleanupTime B)
  rw [show ((advance (SourceClauseClearExcept.program
      (SourceClauseRowWriterCleanup.keep q)))^[callbackCleanupTime B])
      (⟨some (.clear 0), ((), none), W⟩) =
      ⟨none, ((), none), SourceClauseRowWriterCleanup.clean W⟩
      from SourceClauseRowWriterCleanup.run W] at he
  rw [hnorm] at he
  change ((advance (SourceCSPFirstSlotBridge.cleanupProgram (q := q)))^[
    callbackCleanupTime B]) (⟨some (.clear 0), ((), none),
      bank SourceCSPFirstSlotBridge.writerEmbedding B W⟩) =
    ⟨none, ((), none), bank SourceCSPFirstSlotBridge.writerEmbedding B
      (SourceClauseRowWriterBlank.bank (currentRow B) n r
        (W SourceClauseRowWriterCleanup.savedCell)
        (W SourceClauseRowWriterCleanup.outputCell)
        (W SourceClauseRowWriterCleanup.countCell))⟩ at he
  rw [hbank] at he
  have hresult : bank SourceCSPFirstSlotBridge.writerEmbedding B
      (SourceClauseRowWriterBlank.bank (currentRow B) n r
        (W SourceClauseRowWriterCleanup.savedCell)
        (W SourceClauseRowWriterCleanup.outputCell)
        (W SourceClauseRowWriterCleanup.countCell)) =
      callbackResult B n r := by
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
            change bank SourceCSPFirstSlotBridge.writerEmbedding B _
              (SourceCSPFirstSlotBridge.writerEmbedding k) = _
            rw [bank_at]
            rfl
        | inr i =>
            rw [bank_outside]
            · exact hcursor i
            · rintro ⟨k, hk⟩
              cases hk
  simpa only [hresult] using he

theorem callback_bank_after_step {q : Nat} (B : Stack q → List Bool)
    (rest cap saved output count : List Bool)
    (V : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r : Nat)
    (hsaved : writerProjection B SourceClauseRowWriterCleanup.savedCell = saved)
    (houtput : writerProjection B SourceClauseRowWriterCleanup.outputCell = output)
    (hcount : writerProjection B SourceClauseRowWriterCleanup.countCell = count) :
    callbackResult (steppedResult B rest cap V) n (r + 1) =
      Sum.elim (fun g => B (.inl g))
        (SourceClauseRowWriterTruthFrame.initial
          V n (r + 1) saved output count) := by
  have hrow : currentRow (steppedResult B rest cap V) = V := by
    funext x
    exact congrFun (stepped_row B rest cap V) x
  have hsaved' : writerProjection (steppedResult B rest cap V)
      SourceClauseRowWriterCleanup.savedCell = saved := by
    rw [writerProjection, stepped_writer_frame]
    · exact hsaved
    · intro x
      cases x <;> simp [SourceClauseRowWriterCleanup.savedCell,
        SourceClauseRowWriterCleanup.rowCell]
    · simp [SourceClauseRowWriterCleanup.savedCell,
        SourceClauseRowWriterOperands.rowIndex]
  have houtput' : writerProjection (steppedResult B rest cap V)
      SourceClauseRowWriterCleanup.outputCell = output := by
    rw [writerProjection, stepped_writer_frame]
    · exact houtput
    · intro x
      cases x <;> simp [SourceClauseRowWriterCleanup.outputCell,
        SourceClauseRowWriterCleanup.rowCell]
    · simp [SourceClauseRowWriterCleanup.outputCell,
        SourceClauseRowWriterOperands.rowIndex]
  have hcount' : writerProjection (steppedResult B rest cap V)
      SourceClauseRowWriterCleanup.countCell = count := by
    rw [writerProjection, stepped_writer_frame]
    · exact hcount
    · intro x
      cases x <;> simp [SourceClauseRowWriterCleanup.countCell,
        SourceClauseRowWriterCleanup.rowCell]
    · simp [SourceClauseRowWriterCleanup.countCell,
        SourceClauseRowWriterOperands.rowIndex]
  funext x
  cases x with
  | inl g =>
      simpa only [callbackResult, Sum.elim_inl] using
        stepped_global B rest cap V g
  | inr k =>
      simp only [callbackResult, Sum.elim_inr]
      rw [hrow, hsaved', houtput', hcount']

/-- One physical next-row iteration from a post-callback bank. The input
`rest` is exactly a typed row followed by `tail`; the parser derives all
query unary words and truth bits from that source suffix. The output bank
is the next callback's *actual* initial shape with the old accumulated
clause payload and unary count unchanged. -/
theorem next_row_iteration {n a q : Nat}
    (next : SourceCSPCodec.Row n a q)
    (B : Stack q → List Bool) (rest tail saved output count : List Bool)
    (r L : Nat)
    (hn : 0 < n)
    (hrest : rest = SourceCSPCodec.rowFields next ++ tail)
    (hsource : B (rowEmbedding (.inr 0)) = rest)
    (hcap : B (.inl SourceCSPHeaderRowBridge.capSource) =
      List.replicate (n - 1) true)
    (hscratch : B (.inr (.inl SourceClauseRowWriterOperands.scratch)) = [])
    (hcursor : ∀ i : Fin 2, B (.inr (.inr i)) = [])
    (hvertex : writerProjection B SourceClauseRowWriterOperands.vertex =
      List.replicate n true)
    (hindex : writerProjection B SourceClauseRowWriterOperands.rowIndex =
      List.replicate r true)
    (hsaved : writerProjection B SourceClauseRowWriterCleanup.savedCell = saved)
    (houtput : writerProjection B SourceClauseRowWriterCleanup.outputCell = output)
    (hcount : writerProjection B SourceClauseRowWriterCleanup.countCell = count)
    (hword : ∀ j : Fin q, (next.1 j).val.bits.length ≤ L)
    (hcapL : n - 1 ≤ L) :
    let cap := List.replicate (n - 1) true
    ∃ (tR tP : Nat)
      (v : SourceCSPRowController.Control × SourceCSPQueryBank.Control)
      (V : SourceCSPRowQueryFrame.Stack q → List Bool),
      tR ≤ resetCost B cap ∧
      ((advance (resetProgram q))^[tR])
        (⟨some (BitMachineRawSequence.leftLabel 0),
          (((), none), none), B⟩ :
          TM2.Cfg (fun _ : Stack q => Bool)
            (SourceCSPRowLoopReset.Label q)
            SourceCSPRowLoopReset.Control) =
        ⟨none, (((), none), none), resetResult B rest cap⟩ ∧
      tP ≤ q * (2 * (SourceCSPCodec.rowFields next ++ tail).length + 4) +
        2 * a ^ q + 3 + q * (100 * (L + 1) ^ 2) + 2 ∧
      ((advance (parseProgram q a))^[tP])
        (⟨some (BitMachineRawSequence.leftLabel
            (.start 0 : SourceCSPRowController.Label q (a ^ q))),
          ((none, none), (((none, none), (none, false)), none)),
          resetResult B rest cap⟩ :
          TM2.Cfg (fun _ : Stack q => Bool)
            (BitMachineRawSequence.Label
              (SourceCSPRowController.Label q (a ^ q))
              (SourceCSPQueryBank.Label q))
            (SourceCSPRowController.Control × SourceCSPQueryBank.Control)) =
        ⟨none, v, parsedResult B rest cap V⟩ ∧
      ((advance (advanceProgram q))^[2])
        (⟨some .push, (), parsedResult B rest cap V⟩ :
          TM2.Cfg (fun _ : Stack q => Bool)
            SourceClauseRowWriterRowAdvance.Label Unit) =
        ⟨none, (), steppedResult B rest cap V⟩ ∧
      ((advance (SourceCSPFirstSlotBridge.cleanupProgram (q := q)))^[
        callbackCleanupTime (steppedResult B rest cap V)])
        (⟨some (.clear 0), ((), none), steppedResult B rest cap V⟩ :
          TM2.Cfg (fun _ : Stack q => Bool)
            (SourceClauseClearExcept.Label
              (SourceClauseClearExcept.workCount
                (SourceClauseRowWriterCleanup.keep q)))
            (Unit × Option Bool)) =
        ⟨none, ((), none), callbackResult (steppedResult B rest cap V)
          n (r + 1)⟩ ∧
      callbackResult (steppedResult B rest cap V) n (r + 1) =
        Sum.elim (fun g => B (.inl g))
          (SourceClauseRowWriterTruthFrame.initial V n (r + 1)
            saved output count) ∧
      V (.inr 0) = tail ∧ V (.inr 4) = [true] ∧
      (∀ j : Fin q, V (.inl (j, 1)) =
        List.replicate (next.1 j).val true) ∧
      V (.inr 2) = true :: List.ofFn next.2 := by
  let cap := List.replicate (n - 1) true
  obtain ⟨tR, htR, hrunR⟩ :=
    reset_run q B rest cap hsource hcap hscratch
  obtain ⟨tP, v, V, htP, hrunP, htail, hstatus,
    hquery, htruth⟩ :=
    parse_next_row next B rest tail L hn hrest hword hcapL
  have hcursor' : ∀ i : Fin 2,
      steppedResult B rest cap V (.inr (.inr i)) = [] := by
    intro i
    rw [stepped_cursor]
    exact hcursor i
  have hvertex' : writerProjection (steppedResult B rest cap V)
      SourceClauseRowWriterOperands.vertex = List.replicate n true := by
    rw [writerProjection, stepped_writer_frame]
    · exact hvertex
    · intro x
      cases x <;> simp [SourceClauseRowWriterOperands.vertex,
        SourceClauseRowWriterCleanup.rowCell]
    · simp [SourceClauseRowWriterOperands.vertex,
        SourceClauseRowWriterOperands.rowIndex]
  have hindex' := stepped_index B rest cap V r hindex
  refine ⟨tR, tP, v, V, htR, hrunR, htP, ?_, ?_, ?_, ?_,
    htail, hstatus, hquery, htruth⟩
  · simpa only [parsedResult, cap] using hrunP
  · simpa only [steppedResult] using
      advance_run q (parsedResult B rest cap V)
  · exact callback_cleanup_run (steppedResult B rest cap V)
      n (r + 1) hcursor' hvertex' hindex'
  · exact callback_bank_after_step B rest cap saved output count V
      n r hsaved houtput hcount

def parseStart {q a : Nat} :
    BitMachineRawSequence.Label
      (SourceCSPRowController.Label q (a ^ q))
      (SourceCSPQueryBank.Label q) :=
  BitMachineRawSequence.leftLabel (.start 0)

def parseControlStart :
    SourceCSPRowController.Control × SourceCSPQueryBank.Control :=
  ((none, none), (((none, none), (none, false)), none))

noncomputable def readProgram (q a : Nat) :=
  BitMachineRawSequence.program (resetProgram q) (parseProgram q a)
    (parseStart (q := q) (a := a)) (((), none), none) parseControlStart

noncomputable def finishProgram (q : Nat) :=
  BitMachineRawSequence.program (advanceProgram q)
    (SourceCSPFirstSlotBridge.cleanupProgram (q := q))
    (.clear 0) () ((), none)

noncomputable def nextProgram (q a : Nat) :=
  BitMachineRawSequence.program (readProgram q a) (finishProgram q)
    (BitMachineRawSequence.leftLabel .push)
    ((((), none), none), parseControlStart)
    ((), ((), none))

/-- The four physical stages are one fixed instruction table for each
`q,a`. Input-specific row data, row index, remaining-row count, and clause
accumulator stay solely in the bank. -/
theorem next_row_single_program {n a q : Nat}
    (next : SourceCSPCodec.Row n a q)
    (B : Stack q → List Bool) (rest tail saved output count : List Bool)
    (r L : Nat)
    (hn : 0 < n)
    (hrest : rest = SourceCSPCodec.rowFields next ++ tail)
    (hsource : B (rowEmbedding (.inr 0)) = rest)
    (hcap : B (.inl SourceCSPHeaderRowBridge.capSource) =
      List.replicate (n - 1) true)
    (hscratch : B (.inr (.inl SourceClauseRowWriterOperands.scratch)) = [])
    (hcursor : ∀ i : Fin 2, B (.inr (.inr i)) = [])
    (hvertex : writerProjection B SourceClauseRowWriterOperands.vertex =
      List.replicate n true)
    (hindex : writerProjection B SourceClauseRowWriterOperands.rowIndex =
      List.replicate r true)
    (hsaved : writerProjection B SourceClauseRowWriterCleanup.savedCell = saved)
    (houtput : writerProjection B SourceClauseRowWriterCleanup.outputCell = output)
    (hcount : writerProjection B SourceClauseRowWriterCleanup.countCell = count)
    (hword : ∀ j : Fin q, (next.1 j).val.bits.length ≤ L)
    (hcapL : n - 1 ≤ L) :
    let cap := List.replicate (n - 1) true
    ∃ (t : Nat) (V : SourceCSPRowQueryFrame.Stack q → List Bool),
      t ≤ resetCost B cap +
        (q * (2 * (SourceCSPCodec.rowFields next ++ tail).length + 4) +
          2 * a ^ q + 3 + q * (100 * (L + 1) ^ 2) + 2) +
        2 + callbackCleanupTime (steppedResult B rest cap V) + 3 ∧
      ((advance (nextProgram q a))^[t])
        (⟨some (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel
              (BitMachineRawSequence.leftLabel 0))),
          (((((), none), none), parseControlStart), ((), ((), none))), B⟩ :
          TM2.Cfg (fun _ : Stack q => Bool) _ _) =
        ⟨none, (((((), none), none), parseControlStart), ((), ((), none))),
          Sum.elim (fun g => B (.inl g))
            (SourceClauseRowWriterTruthFrame.initial V n (r + 1)
              saved output count)⟩ ∧
      V (.inr 0) = tail ∧ V (.inr 4) = [true] ∧
      (∀ j : Fin q, V (.inl (j, 1)) =
        List.replicate (next.1 j).val true) ∧
      V (.inr 2) = true :: List.ofFn next.2 := by
  let cap := List.replicate (n - 1) true
  obtain ⟨tR, tP, v, V, htR, hrunR, htP, hrunP, hrunA,
    hrunC, hbank, htail, hstatus, hquery, htruth⟩ :=
    next_row_iteration next B rest tail saved output count r L
      hn hrest hsource hcap hscratch hcursor hvertex hindex
      hsaved houtput hcount hword hcapL
  obtain ⟨tRead, htRead, hrunRead⟩ :=
    BitMachineRawSequence.runs (resetProgram q) (parseProgram q a)
      (BitMachineRawSequence.leftLabel 0)
      (parseStart (q := q) (a := a))
      (((), none), none) (((), none), none)
      parseControlStart v B (resetResult B rest cap)
      (parsedResult B rest cap V) tR tP hrunR hrunP
  obtain ⟨tFinish, htFinish, hrunFinish⟩ :=
    BitMachineRawSequence.runs (advanceProgram q)
      (SourceCSPFirstSlotBridge.cleanupProgram (q := q))
      (.push) (.clear 0) () () ((), none) ((), none)
      (parsedResult B rest cap V) (steppedResult B rest cap V)
      (callbackResult (steppedResult B rest cap V) n (r + 1))
      2 (callbackCleanupTime (steppedResult B rest cap V))
      hrunA hrunC
  obtain ⟨t, ht, hrun⟩ :=
    BitMachineRawSequence.runs (readProgram q a) (finishProgram q)
      (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel 0))
      (BitMachineRawSequence.leftLabel .push)
      ((((), none), none), parseControlStart)
      ((((), none), none), v)
      ((), ((), none)) ((), ((), none))
      B (parsedResult B rest cap V)
      (callbackResult (steppedResult B rest cap V) n (r + 1))
      tRead tFinish hrunRead hrunFinish
  dsimp only [cap] at *
  refine ⟨t, V, ?_, ?_, htail, hstatus, hquery, htruth⟩
  · omega
  · rw [hbank] at hrun
    simpa only [nextProgram, readProgram, finishProgram,
      parseStart] using hrun

noncomputable def callbackBank {q : Nat}
    (S : SourceCSPGlobalDecisionProgram.Stack q → List Bool)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r : Nat) (saved output count : List Bool) : Stack q → List Bool :=
  Sum.elim S
    (SourceClauseRowWriterTruthFrame.initial row n r saved output count)

theorem callback_bank_row {q : Nat}
    (S : SourceCSPGlobalDecisionProgram.Stack q → List Bool)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r : Nat) (saved output count : List Bool)
    (x : SourceCSPRowQueryFrame.Stack q) :
    callbackBank S row n r saved output count (rowEmbedding x) = row x := by
  rfl

theorem callback_bank_fields {q : Nat}
    (S : SourceCSPGlobalDecisionProgram.Stack q → List Bool)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r : Nat) (saved output count : List Bool) :
    callbackBank S row n r saved output count
      (.inl SourceCSPHeaderRowBridge.capSource) =
        S SourceCSPHeaderRowBridge.capSource ∧
    callbackBank S row n r saved output count
      (.inr (.inl SourceClauseRowWriterOperands.scratch)) = [] ∧
    (∀ i : Fin 2,
      callbackBank S row n r saved output count (.inr (.inr i)) = []) ∧
    writerProjection (callbackBank S row n r saved output count)
      SourceClauseRowWriterOperands.vertex = List.replicate n true ∧
    writerProjection (callbackBank S row n r saved output count)
      SourceClauseRowWriterOperands.rowIndex = List.replicate r true ∧
    writerProjection (callbackBank S row n r saved output count)
      SourceClauseRowWriterCleanup.savedCell = saved ∧
    writerProjection (callbackBank S row n r saved output count)
      SourceClauseRowWriterCleanup.outputCell = output ∧
    writerProjection (callbackBank S row n r saved output count)
      SourceClauseRowWriterCleanup.countCell = count := by
  refine ⟨rfl, rfl, ?_, rfl, rfl, rfl, rfl, rfl⟩
  intro i
  fin_cases i <;> rfl

/-- Direct restart from the exact `AllSlotsExact` terminal bank shape.
The unread source is the encoding of the nonempty remaining typed-row list;
its head/tail split is proved by `remaining_rows_succ`, not supplied as an
extra parsed witness. `saved`, `output`, and `count` may already encode an
arbitrary prefix of emitted clauses. -/
theorem next_row_after_callback {n a q m : Nat}
    (rows : Fin (m + 1) → SourceCSPCodec.Row n a q)
    (S : SourceCSPGlobalDecisionProgram.Stack q → List Bool)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (saved output count : List Bool) (r L : Nat)
    (hn : 0 < n)
    (hsource : row (.inr 0) =
      SourceCSPCodec.fnFields SourceCSPCodec.rowFields rows)
    (hcap : S SourceCSPHeaderRowBridge.capSource =
      List.replicate (n - 1) true)
    (hword : ∀ j : Fin q, ((rows 0).1 j).val.bits.length ≤ L)
    (hcapL : n - 1 ≤ L) :
    let rest := SourceCSPCodec.fnFields SourceCSPCodec.rowFields rows
    let tail := SourceCSPCodec.fnFields SourceCSPCodec.rowFields
      (fun j : Fin m => rows j.succ)
    let B := callbackBank S row n r saved output count
    let cap := List.replicate (n - 1) true
    ∃ (t : Nat) (V : SourceCSPRowQueryFrame.Stack q → List Bool),
      t ≤ resetCost B cap +
        (q * (2 * (SourceCSPCodec.rowFields (rows 0) ++ tail).length + 4) +
          2 * a ^ q + 3 + q * (100 * (L + 1) ^ 2) + 2) +
        2 + callbackCleanupTime (steppedResult B rest cap V) + 3 ∧
      ((advance (nextProgram q a))^[t])
        (⟨some (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel
              (BitMachineRawSequence.leftLabel 0))),
          (((((), none), none), parseControlStart), ((), ((), none))), B⟩ :
          TM2.Cfg (fun _ : Stack q => Bool) _ _) =
        ⟨none, (((((), none), none), parseControlStart), ((), ((), none))),
          callbackBank S V n (r + 1) saved output count⟩ ∧
      V (.inr 0) = tail ∧ V (.inr 4) = [true] ∧
      (∀ j : Fin q, V (.inl (j, 1)) =
        List.replicate ((rows 0).1 j).val true) ∧
      V (.inr 2) = true :: List.ofFn (rows 0).2 := by
  let rest := SourceCSPCodec.fnFields SourceCSPCodec.rowFields rows
  let tail := SourceCSPCodec.fnFields SourceCSPCodec.rowFields
    (fun j : Fin m => rows j.succ)
  let B := callbackBank S row n r saved output count
  let cap := List.replicate (n - 1) true
  obtain ⟨hcapB, hscratch, hcursor, hvertex, hindex,
    hsaved, houtput, hcount⟩ :=
    callback_bank_fields S row n r saved output count
  have hsourceB : B (rowEmbedding (.inr 0)) = rest := by
    change callbackBank S row n r saved output count
      (rowEmbedding (.inr 0)) = rest
    rw [callback_bank_row]
    exact hsource
  have hrest : rest = SourceCSPCodec.rowFields (rows 0) ++ tail :=
    remaining_rows_succ rows
  obtain ⟨t, V, ht, hrun, htail, hstatus, hquery, htruth⟩ :=
    next_row_single_program (rows 0) B rest tail saved output count
      r L hn hrest hsourceB (hcapB.trans hcap)
      hscratch hcursor hvertex hindex hsaved houtput hcount
      hword hcapL
  refine ⟨t, V, ht, ?_, htail, hstatus, hquery, htruth⟩
  simpa only [B, callbackBank] using hrun


end EthInapproximability.CurrentPaper.SourceCSPNextRowBridge
