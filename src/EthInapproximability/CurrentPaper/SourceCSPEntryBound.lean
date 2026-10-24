import EthInapproximability.CurrentPaper.SourceCSPFirstSlotBridge
import EthInapproximability.CurrentPaper.SourceCSPAllRowLoopPolynomial
import EthInapproximability.CurrentPaper.SourceCSPRawCanonicalReadback
import EthInapproximability.CurrentPaper.SourceCSPAcceptedCount
import EthInapproximability.CurrentPaper.SourceClauseRowPrefixPolynomial
import EthInapproximability.CurrentPaper.BitMachineStackGrowth

namespace EthInapproximability.CurrentPaper.SourceCSPEntryBound

open Turing Turing.TM2.Stmt BitMachineEncoding
open scoped Classical

noncomputable def firstEnvelope (q L : Nat) : Nat :=
  L + BitMachineStackGrowth.perStep
    (SourceCSPFirstRowController.program 2 q) *
    (SourceCSPFirstRowController.cubicCoefficient 2 q * (L + 1) ^ 3)

theorem first_initial_length_le (q : Nat) (input : List Bool)
    (x : SourceCSPFirstRowController.Stack q) :
    ((SourceCSPFirstRowController.initial 2 q input).stk x).length ≤
      input.length := by
  cases x with
  | inl g =>
      change ((SourceCSPSecondPassGlobalLift.initial 2 q input).stk (.inl g)).length ≤ _
      rw [SourceCSPSecondPassGlobalLift.initial_left]
      simp [SourceCSPGlobalDecisionProgram.initial,
        SourceCSPHeaderRowBridge.initial,
        SourceCSPPositiveHeader.initial,
        SourceCSPInputFrame.initial,
        SourceCSPHeaderCheck.parserInitial,
        SourceCSPRowController.contents]
      all_goals aesop
  | inr k =>
      rw [show (SourceCSPFirstRowController.initial 2 q input).stk (.inr k) = []
        from SourceCSPSecondPassGlobalLift.initial_writer_blank 2 q input k]
      simp

theorem actual_first_bank_le (q : Nat) (input : List Bool)
    (t : Nat) (v : SourceCSPFirstRowController.Control 2 q)
    (U : SourceCSPFirstRowController.Stack q → List Bool)
    (ht : t ≤ SourceCSPFirstRowController.cubicCoefficient 2 q *
      (input.length + 1) ^ 3)
    (hrun : ((advance (SourceCSPFirstRowController.program 2 q))^[t])
      (SourceCSPFirstRowController.initial 2 q input) = ⟨none, v, U⟩) :
    ∀ x, (U x).length ≤ firstEnvelope q input.length := by
  intro x
  have hg := BitMachineStackGrowth.run_growth
    (SourceCSPFirstRowController.program 2 q)
    (SourceCSPFirstRowController.initial 2 q input) t x
  rw [hrun] at hg
  have hi := first_initial_length_le q input x
  dsimp [firstEnvelope]
  nlinarith

theorem actual_rows_query_width {n m q : Nat}
    (rows : Fin m → SourceCSPCodec.Row n 2 q) :
    ∀ i : Fin m, ∀ j : Fin q,
      ((rows i).1 j).val.bits.length ≤ n := by
  intro i j
  have hb := UnaryBinaryEncoding.bits_length_le ((rows i).1 j).val
  omega

theorem raw_source_parameters_le {n m q : Nat}
    (input suffix : List Bool)
    (rows : Fin m → SourceCSPCodec.Row n 2 q)
    (hinput : input = SourceCSPHeaderParse.header n m 2 q ++ suffix)
    (hread : SourceCSPCodec.readFn (SourceCSPCodec.readRow n 2 q) m suffix =
      some (rows, []))
    (hsize : n ≤ q * m) :
    n ≤ q * input.length ∧ m ≤ input.length ∧
      suffix.length ≤ input.length := by
  have hm := (RawCanonicalReadback.successful_rows_length_bounds
    input suffix rows hinput hread).2
  have hs : suffix.length ≤ input.length := by simp [hinput]
  constructor
  · exact hsize.trans (Nat.mul_le_mul_left q hm)
  · exact ⟨hm, hs⟩

noncomputable def callbackProgram (q : Nat) (hq : 0 < q) :=
  let C := SourceClauseCallback.AllSlots.allCircuit hq
  BitMachineRawSequence.program (SourceCSPFirstSlotBridge.cleanupProgram (q := q))
    (fun l => BitMachineStackEmbedding.stackStmt
      (SourceCSPFirstSlotBridge.truthEmbedding (q := q)) (C.program l))
    C.start ((), none) C.initial

noncomputable def callbackEnvelope (q : Nat) (hq : 0 < q)
    (B : Nat) : Nat :=
  let W := SourceClauseClearExcept.workCount
    (SourceClauseRowWriterCleanup.keep q)
  B + (by
    let C := SourceClauseCallback.AllSlots.allCircuit hq
    letI : Finite C.Label := C.labelsFinite
    letI : Fintype C.Label := Fintype.ofFinite C.Label
    exact BitMachineStackGrowth.perStep (callbackProgram q hq)) *
    (W * (B + 1) + 2 +
      SourceClauseCallbackAllSlotPolynomial.allCoefficient q * (B + 1) ^ 2 + 1)

theorem cleanupTime_le {q B : Nat}
    (U : SourceCSPFirstRowController.Stack q → List Bool)
    (hU : ∀ x, (U x).length ≤ B) :
    SourceCSPFirstSlotBridge.cleanupTime U ≤
      SourceClauseClearExcept.workCount
        (SourceClauseRowWriterCleanup.keep q) * (B + 1) + 2 := by
  let W := SourceClauseClearExcept.workCount
    (SourceClauseRowWriterCleanup.keep q)
  have hs : (∑ i : Fin (SourceClauseClearExcept.workCount
      (SourceClauseRowWriterCleanup.keep q)),
      (SourceCSPFirstSlotBridge.writer U
        (SourceClauseClearExcept.workBank
          (SourceClauseRowWriterCleanup.keep q) i)).length) ≤
      ∑ _i : Fin (SourceClauseClearExcept.workCount
        (SourceClauseRowWriterCleanup.keep q)), B := by
    apply Finset.sum_le_sum
    intro i _
    exact hU _
  simp only [Finset.sum_const, Finset.card_fin, nsmul_eq_mul] at hs
  dsimp [SourceCSPFirstSlotBridge.cleanupTime, W]
  nlinarith

noncomputable def callbackInitial (q : Nat) (hq : 0 < q)
    (U : SourceCSPFirstRowController.Stack q → List Bool) :=
  let C := SourceClauseCallback.AllSlots.allCircuit hq
  (⟨some (BitMachineRawSequence.leftLabel (.clear 0)),
    (((), none), C.initial), SourceCSPFirstSlotBridge.extended U⟩ :
    TM2.Cfg (fun _ : SourceCSPFirstSlotBridge.Stack q => Bool)
      (BitMachineRawSequence.Label
        (SourceClauseClearExcept.Label
          (SourceClauseClearExcept.workCount
            (SourceClauseRowWriterCleanup.keep q))) C.Label)
      ((Unit × Option Bool) × C.Control))

theorem callback_initial_length_le (q : Nat) (hq : 0 < q)
    (U : SourceCSPFirstRowController.Stack q → List Bool)
    (B : Nat) (hU : ∀ x, (U x).length ≤ B)
    (x : SourceCSPFirstSlotBridge.Stack q) :
    ((callbackInitial q hq U).stk x).length ≤ B := by
  cases x with
  | inl g => exact hU _
  | inr k =>
      cases k with
      | inl w => exact hU _
      | inr i => simp [callbackInitial, SourceCSPFirstSlotBridge.extended]

theorem callback_terminal_bank_le (q : Nat) (hq : 0 < q)
    (U : SourceCSPFirstRowController.Stack q → List Bool)
    (B n : Nat) (t : Nat)
    (table : Fin (2 ^ q) → Bool)
    (V : SourceCSPFirstSlotBridge.Stack q → List Bool)
    (hU : ∀ x, (U x).length ≤ B) (hn : n ≤ B)
    (hquery : ∀ j : Fin q,
      SourceCSPFirstSlotBridge.row U (.inl (j, 1)) =
        List.replicate
          (SourceCSPFirstSlotBridge.row U (.inl (j, 1))).length true)
    (ht : t ≤ SourceCSPFirstSlotBridge.cleanupTime U +
      SourceClauseCallback.AllSlotsClock.allCost hq
        (SourceCSPFirstSlotBridge.row U) n 0 table
        (SourceCSPFirstSlotBridge.writer U
          SourceClauseRowWriterCleanup.savedCell)
        (SourceCSPFirstSlotBridge.writer U
          SourceClauseRowWriterCleanup.outputCell)
        (SourceCSPFirstSlotBridge.writer U
          SourceClauseRowWriterCleanup.countCell) + 1)
    (hrun : ((advance (callbackProgram q hq))^[t])
      (callbackInitial q hq U) =
        ⟨none, (((), none),
          (SourceClauseCallback.AllSlots.allCircuit hq).initial), V⟩) :
    ∀ x, (V x).length ≤ callbackEnvelope q hq B := by
  classical
  let C := SourceClauseCallback.AllSlots.allCircuit hq
  letI : Finite C.Label := C.labelsFinite
  letI : Fintype C.Label := Fintype.ofFinite C.Label
  intro x
  have hg := BitMachineStackGrowth.run_growth
    (callbackProgram q hq) (callbackInitial q hq U) t x
  rw [hrun] at hg
  have hi := callback_initial_length_le q hq U B hU x
  have hc := cleanupTime_le U hU
  have ha := SourceClauseCallbackAllSlotPolynomial.allCost_le_quadratic
    hq (SourceCSPFirstSlotBridge.row U) n 0 B table
      (SourceCSPFirstSlotBridge.writer U
        SourceClauseRowWriterCleanup.savedCell)
      (SourceCSPFirstSlotBridge.writer U
        SourceClauseRowWriterCleanup.outputCell)
      (SourceCSPFirstSlotBridge.writer U
        SourceClauseRowWriterCleanup.countCell)
      hn (Nat.zero_le B) (fun y => hU _)
      (hU _) (hU _) (hU _) hquery
  dsimp [callbackEnvelope]
  nlinarith

noncomputable def prefixBank {q : Nat}
    (U : SourceCSPFirstRowController.Stack q → List Bool)
    (saved output count : List Bool) :
    SourceCSPFirstRowController.Stack q → List Bool :=
  Function.update
    (Function.update
      (Function.update U
        (.inr SourceClauseRowWriterCleanup.savedCell) saved)
      (.inr SourceClauseRowWriterCleanup.outputCell) output)
    (.inr SourceClauseRowWriterCleanup.countCell) count

noncomputable def entryBase (q L A : Nat) : Nat :=
  firstEnvelope q L + (q + 1) * L + A + 2 ^ q + 1

theorem prefixBank_length_le (q : Nat) (input : List Bool)
    (U : SourceCSPFirstRowController.Stack q → List Bool)
    (saved output count : List Bool)
    (hU : ∀ x, (U x).length ≤ firstEnvelope q input.length) :
    ∀ x, (prefixBank U saved output count x).length ≤
      entryBase q input.length
        (saved.length + output.length + count.length) := by
  intro x
  have hu := hU x
  have hp : 0 < 2 ^ q := pow_pos (by omega) _
  simp only [prefixBank, Function.update_apply]
  split_ifs <;> change _ ≤ firstEnvelope q input.length +
    (q + 1) * input.length +
    (saved.length + output.length + count.length) + 2 ^ q + 1 <;>
    omega

theorem prefixBank_global {q : Nat}
    (U : SourceCSPFirstRowController.Stack q → List Bool)
    (saved output count : List Bool)
    (g : SourceCSPGlobalDecisionProgram.Stack q) :
    prefixBank U saved output count (.inl g) = U (.inl g) := by
  simp [prefixBank]

theorem prefixBank_row {q : Nat}
    (U : SourceCSPFirstRowController.Stack q → List Bool)
    (saved output count : List Bool)
    (x : SourceCSPRowQueryFrame.Stack q) :
    SourceCSPFirstSlotBridge.row (prefixBank U saved output count) x =
      SourceCSPFirstSlotBridge.row U x := by
  simp [SourceCSPFirstSlotBridge.row, prefixBank,
    SourceCSPStagedFirstRow.rowSlot,
    SourceClauseRowWriterCleanup.savedCell,
    SourceClauseRowWriterCleanup.outputCell,
    SourceClauseRowWriterCleanup.countCell,
    SourceClauseRowWriterCleanup.rowCell]

theorem prefixBank_vertex {q : Nat}
    (U : SourceCSPFirstRowController.Stack q → List Bool)
    (saved output count : List Bool) :
    SourceCSPFirstSlotBridge.writer (prefixBank U saved output count)
      SourceClauseRowWriterOperands.vertex =
    SourceCSPFirstSlotBridge.writer U SourceClauseRowWriterOperands.vertex := by
  simp [SourceCSPFirstSlotBridge.writer, prefixBank,
    SourceClauseRowWriterCleanup.savedCell,
    SourceClauseRowWriterCleanup.outputCell,
    SourceClauseRowWriterCleanup.countCell,
    SourceClauseRowWriterOperands.vertex]

theorem prefixBank_rowIndex {q : Nat}
    (U : SourceCSPFirstRowController.Stack q → List Bool)
    (saved output count : List Bool) :
    SourceCSPFirstSlotBridge.writer (prefixBank U saved output count)
      SourceClauseRowWriterOperands.rowIndex =
    SourceCSPFirstSlotBridge.writer U SourceClauseRowWriterOperands.rowIndex := by
  simp [SourceCSPFirstSlotBridge.writer, prefixBank,
    SourceClauseRowWriterCleanup.savedCell,
    SourceClauseRowWriterCleanup.outputCell,
    SourceClauseRowWriterCleanup.countCell,
    SourceClauseRowWriterOperands.rowIndex]

theorem prefixBank_saved {q : Nat}
    (U : SourceCSPFirstRowController.Stack q → List Bool)
    (saved output count : List Bool) :
    SourceCSPFirstSlotBridge.writer (prefixBank U saved output count)
      SourceClauseRowWriterCleanup.savedCell = saved := by
  simp [SourceCSPFirstSlotBridge.writer, prefixBank,
    SourceClauseRowWriterCleanup.savedCell,
    SourceClauseRowWriterCleanup.outputCell,
    SourceClauseRowWriterCleanup.countCell]

theorem prefixBank_output {q : Nat}
    (U : SourceCSPFirstRowController.Stack q → List Bool)
    (saved output count : List Bool) :
    SourceCSPFirstSlotBridge.writer (prefixBank U saved output count)
      SourceClauseRowWriterCleanup.outputCell = output := by
  simp [SourceCSPFirstSlotBridge.writer, prefixBank,
    SourceClauseRowWriterCleanup.savedCell,
    SourceClauseRowWriterCleanup.outputCell,
    SourceClauseRowWriterCleanup.countCell]

theorem prefixBank_count {q : Nat}
    (U : SourceCSPFirstRowController.Stack q → List Bool)
    (saved output count : List Bool) :
    SourceCSPFirstSlotBridge.writer (prefixBank U saved output count)
      SourceClauseRowWriterCleanup.countCell = count := by
  simp [SourceCSPFirstSlotBridge.writer, prefixBank,
    SourceClauseRowWriterCleanup.savedCell,
    SourceClauseRowWriterCleanup.outputCell,
    SourceClauseRowWriterCleanup.countCell]

theorem raw_accepted_source (q : Nat) (input : List Bool)
    (tg : Nat)
    (vr : SourceCSPRowLoopController.QueryControl ×
      SourceCSPRowLoopController.ResetControl)
    (S : SourceCSPGlobalDecisionProgram.Stack q → List Bool)
    (hacc : ((advance (SourceCSPGlobalDecisionProgram.program 2 q))^[tg])
      (SourceCSPGlobalDecisionProgram.initial 2 q input) =
        ⟨none, .row (vr, some true), S⟩) :
    ∃ (n m : Nat) (suffix : List Bool)
      (rows : Fin m → SourceCSPCodec.Row n 2 q),
      0 < n ∧ 0 < m ∧ n ≤ q * m ∧ m ≤ input.length ∧
      input = SourceCSPHeaderParse.header n m 2 q ++ suffix ∧
      SourceCSPCodec.readFn (SourceCSPCodec.readRow n 2 q) m suffix =
        some (rows, []) ∧
      S SourceCSPGlobalDecisionProgram.savedSource = suffix ∧
      S SourceCSPHeaderRowBridge.capSource =
        List.replicate (n - 1) true ∧
      S SourceCSPHeaderRowBridge.count = List.replicate m true := by
  obtain ⟨tg', _, c, S', hglobal, ts, _, d, W, hselect, hcase⟩ :=
    SourceCSPTotalSelectiveScratch.raw_total_selective 2 q input
  have heq := SourceCSPRowLoopTotalHaltCompare.halted_unique
    (SourceCSPGlobalDecisionProgram.program 2 q)
    (SourceCSPGlobalDecisionProgram.initial 2 q input)
    tg' tg (by rw [hglobal]) (by rw [hacc])
  have hc : c = .row (vr, some true) := by
    have h := congrArg (fun z => z.var) heq
    simpa only [hglobal, hacc] using h
  have hS : S' = S := by
    have h := congrArg (fun z => z.stk) heq
    simpa only [hglobal, hacc] using h
  rcases hcase with hreje | hzero | hgood
  · have hf := hreje.1
    rw [hc] at hf
    contradiction
  · have hf := hzero.1
    rw [hc] at hf
    cases hf
  · obtain ⟨n, m, suffix, rows, vr', hc', _, hinput,
      hn, hsize, hmL, hread, hsaved, hcap, _⟩ := hgood
    have hm : 0 < m := by
      by_contra hnot
      have hm0 : m = 0 := Nat.eq_zero_of_not_pos hnot
      subst m
      simp at hsize
      omega
    subst S'
    refine ⟨n, m, suffix, rows, hn, hm, hsize, hmL,
      hinput, hread, hsaved, hcap, ?_⟩
    exact SourceCSPAcceptedCount.raw_accepted_count_at 2 q n m
      input suffix hinput tg vr S hacc

theorem bounded_accepted_global (q : Nat) (input : List Bool)
    (ta : Nat)
    (vr : SourceCSPRowLoopController.QueryControl ×
      SourceCSPRowLoopController.ResetControl)
    (Sa : SourceCSPGlobalDecisionProgram.Stack q → List Bool)
    (hacc : ((advance (SourceCSPGlobalDecisionProgram.program 2 q))^[ta])
      (SourceCSPGlobalDecisionProgram.initial 2 q input) =
        ⟨none, .row (vr, some true), Sa⟩) :
    ∃ tg ≤ SourceCSPGlobalTotalValidation.totalBound 2 q input.length + 1,
      ((advance (SourceCSPGlobalDecisionProgram.program 2 q))^[tg])
        (SourceCSPGlobalDecisionProgram.initial 2 q input) =
          ⟨none, .row (vr, some true), Sa⟩ := by
  obtain ⟨tg, c, S, _t, _v, _U, htg, hglobal, _ht, _hrun,
    _hleft, _hcase⟩ := SourceCSPFirstRowController.raw_total_first_row
      2 q input
  have heq := SourceCSPRowLoopTotalHaltCompare.halted_unique
    (SourceCSPGlobalDecisionProgram.program 2 q)
    (SourceCSPGlobalDecisionProgram.initial 2 q input)
    tg ta (by rw [hglobal]) (by rw [hacc])
  have hc : c = .row (vr, some true) := by
    have h := congrArg (fun z => z.var) heq
    simpa only [hglobal, hacc] using h
  have hS : S = Sa := by
    have h := congrArg (fun z => z.stk) heq
    simpa only [hglobal, hacc] using h
  subst c
  subst S
  exact ⟨tg, htg, hglobal⟩

/-- A charged physical prelude removes the validator's private loop counter
before the all-row controller copies the retained public row count. -/
def clearLoopProgram (q : Nat) : Fin 2 →
    TM2.Stmt (fun _ : SourceCSPAllRowLoop.Stack q => Bool)
      (Fin 2) (Unit × Option Bool)
  | 0 => BitMachineClearBank.clearStep
      (.inl SourceCSPHeaderRowBridge.loopCount) 0 1
  | 1 => halt

theorem clear_loop_run (q : Nat)
    (B : SourceCSPAllRowLoop.Stack q → List Bool) :
    ((advance (clearLoopProgram q))^[
      (B (.inl SourceCSPHeaderRowBridge.loopCount)).length + 2])
      (⟨some 0, ((), none), B⟩ :
        TM2.Cfg (fun _ : SourceCSPAllRowLoop.Stack q => Bool)
          (Fin 2) (Unit × Option Bool)) =
      ⟨none, ((), none),
        Function.update B (.inl SourceCSPHeaderRowBridge.loopCount) []⟩ := by
  have h := BitMachineClearBank.clear_one_run
    (clearLoopProgram q) (.inl SourceCSPHeaderRowBridge.loopCount)
    0 1 rfl () B
  rw [show (B (.inl SourceCSPHeaderRowBridge.loopCount)).length + 2 =
      (B (.inl SourceCSPHeaderRowBridge.loopCount)).length + 1 + 1 by omega,
    Function.iterate_succ_apply', h]
  rfl

theorem clear_callback_bank {q n r : Nat}
    (S : SourceCSPGlobalDecisionProgram.Stack q → List Bool)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (saved output count : List Bool) :
    Function.update
      (SourceCSPNextRowBridge.callbackBank S row n r saved output count)
      (.inl SourceCSPHeaderRowBridge.loopCount) [] =
    SourceCSPNextRowBridge.callbackBank
      (Function.update S SourceCSPHeaderRowBridge.loopCount [])
      row n r saved output count := by
  funext x
  cases x with
  | inl g =>
      by_cases hg : g = SourceCSPHeaderRowBridge.loopCount
      · subst g
        simp [SourceCSPNextRowBridge.callbackBank]
      · simp [SourceCSPNextRowBridge.callbackBank,
          Function.update_of_ne, hg]
  | inr x =>
      simp [SourceCSPNextRowBridge.callbackBank]

/-- The counter-clear phase is a real bit-machine run, starting at the
post-callback bank and ending at precisely the bank required by the row loop.
Its time is the existing counter-word length plus two halt/empty tests. -/
theorem clear_callback_bank_run {q n r : Nat}
    (S : SourceCSPGlobalDecisionProgram.Stack q → List Bool)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (saved output count : List Bool) :
    ((advance (clearLoopProgram q))^[(S SourceCSPHeaderRowBridge.loopCount).length + 2])
      (⟨some 0, ((), none),
        SourceCSPNextRowBridge.callbackBank S row n r saved output count⟩ :
        TM2.Cfg (fun _ : SourceCSPAllRowLoop.Stack q => Bool)
          (Fin 2) (Unit × Option Bool)) =
      ⟨none, ((), none), SourceCSPNextRowBridge.callbackBank
        (Function.update S SourceCSPHeaderRowBridge.loopCount [])
        row n r saved output count⟩ := by
  have h := clear_loop_run q
    (SourceCSPNextRowBridge.callbackBank S row n r saved output count)
  change ((advance (clearLoopProgram q))^[(S SourceCSPHeaderRowBridge.loopCount).length + 2])
    _ = _ at h
  rw [clear_callback_bank] at h
  exact h

/-- For fixed `q` this is an explicit polynomial of raw source length and
the three supplied entry-prefix accumulator lengths. -/
noncomputable def entryEnvelope (q : Nat) (hq : 0 < q)
    (rawLength prefixLength : Nat) : Nat :=
  callbackEnvelope q hq (entryBase q rawLength prefixLength) +
    entryBase q rawLength prefixLength +
    q * rawLength + rawLength + 2 ^ q + 2

theorem entry_envelope_base (q L A : Nat) (hq : 0 < q) :
    let H := entryEnvelope q hq L A
    callbackEnvelope q hq (entryBase q L A) ≤ H ∧
      entryBase q L A ≤ H ∧ L ≤ H ∧ q * L ≤ H ∧
      1 + 2 ^ q ≤ H := by
  dsimp [entryEnvelope]
  have hp : 0 < 2 ^ q := pow_pos (by omega) _
  constructor
  · omega
  constructor
  · omega
  constructor
  · omega
  constructor
  · omega
  · omega

theorem entry_base_raw_bounds {n m q : Nat}
    (input suffix : List Bool)
    (rows : Fin m → SourceCSPCodec.Row n 2 q)
    (A : Nat)
    (hinput : input = SourceCSPHeaderParse.header n m 2 q ++ suffix)
    (hread : SourceCSPCodec.readFn (SourceCSPCodec.readRow n 2 q) m suffix =
      some (rows, []))
    (hsize : n ≤ q * m) :
    n ≤ entryBase q input.length A ∧
      m ≤ entryBase q input.length A ∧
      1 + 2 ^ q ≤ entryBase q input.length A := by
  have ⟨hn, hm, _⟩ := raw_source_parameters_le input suffix rows
    hinput hread hsize
  have hp : 0 < 2 ^ q := pow_pos (by omega) _
  have hmul : q * input.length ≤ (q + 1) * input.length :=
    Nat.mul_le_mul_right input.length (by omega)
  have hmul1 : input.length ≤ (q + 1) * input.length := by
    nlinarith
  dsimp [entryBase]
  omega

theorem entry_envelope_parameters {n m q : Nat}
    (hq : 0 < q) (input suffix : List Bool)
    (rows : Fin m → SourceCSPCodec.Row n 2 q)
    (saved output count : List Bool)
    (hinput : input = SourceCSPHeaderParse.header n m 2 q ++ suffix)
    (hread : SourceCSPCodec.readFn (SourceCSPCodec.readRow n 2 q) m suffix =
      some (rows, []))
    (hsize : n ≤ q * m) :
    let H := entryEnvelope q hq input.length
      (saved.length + output.length + count.length)
    n ≤ H ∧ m ≤ H ∧ n - 1 ≤ H ∧
      1 + 2 ^ q ≤ H ∧ suffix.length ≤ H ∧
      (∀ i : Fin m, ∀ j : Fin q,
        ((rows i).1 j).val.bits.length ≤ n) := by
  have ⟨hn, hm, hs⟩ := raw_source_parameters_le input suffix rows
    hinput hread hsize
  obtain ⟨_hC, _hB, hL, hqL, hpow⟩ := entry_envelope_base q input.length
    (saved.length + output.length + count.length) hq
  dsimp
  exact ⟨hn.trans hqL, hm.trans hL,
    (Nat.sub_le n 1).trans (hn.trans hqL),
    hpow, hs.trans hL, actual_rows_query_width rows⟩

/-- Starting from a callback-shaped bank with an arbitrary validator-private
counter, first clear that counter physically and then execute the existing
all-row controller. The output uses the original global bank outside the
counter cell, and is the exact canonical suffix-clause accumulator. -/
theorem all_remaining_after_first_with_clear {n m q H : Nat}
    (rows : Fin m → SourceCSPCodec.Row n 2 q) (hq : 0 < q)
    (L : Nat) (hn : 0 < n) (hm : 0 < m)
    (hword : ∀ i : Fin m, ∀ j : Fin q,
      ((rows i).1 j).val.bits.length ≤ L)
    (hcapL : n - 1 ≤ L)
    (hnH : n ≤ H) (hmH : m ≤ H)
    (ht : 1 + 2 ^ q ≤ H) (hL : L ≤ H)
    (S : SourceCSPGlobalDecisionProgram.Stack q → List Bool)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (saved output count : List Bool)
    (hS : ∀ x, (S x).length ≤ H)
    (hrow : ∀ x, (row x).length ≤ H)
    (hsaved : saved.length ≤ H)
    (houtput : output.length ≤ H)
    (hcountWords : count.length ≤ H)
    (hheader : S SourceCSPHeaderRowBridge.count =
      List.replicate m true)
    (hcap : S SourceCSPHeaderRowBridge.capSource =
      List.replicate (n - 1) true)
    (hsource : row (.inr 0) = SourceCSPCodec.fnFields
      SourceCSPCodec.rowFields
        (SourceCSPAllRowLoop.remainingRows rows 0 (m - 1)
          (by omega)))
    (hsourceLen : (row (.inr 0)).length ≤ H) :
    let S' := Function.update S SourceCSPHeaderRowBridge.loopCount []
    let clauses := SourceCSPAllRowLoop.suffixClauses rows hq 0
      (m - 1) (by omega)
    ∃ (tclear tloop : Nat)
      (lastRow : SourceCSPRowQueryFrame.Stack q → List Bool),
      tclear ≤ H + 2 ∧
      tloop ≤ SourceCSPAllRowLoopClock.loopCoefficient q * (H + 1) ^ 9 ∧
      ((advance (clearLoopProgram q))^[tclear])
        (⟨some 0, ((), none),
          SourceCSPNextRowBridge.callbackBank S row n 0
            saved output count⟩ :
          TM2.Cfg (fun _ : SourceCSPAllRowLoop.Stack q => Bool)
            (Fin 2) (Unit × Option Bool)) =
        ⟨none, ((), none),
          SourceCSPNextRowBridge.callbackBank S' row n 0
            saved output count⟩ ∧
      ((advance (SourceCSPAllRowLoop.program hq))^[tloop])
        (⟨some (.copy .scan), .copy none,
          SourceCSPNextRowBridge.callbackBank S' row n 0
            saved output count⟩ :
          TM2.Cfg (fun _ : SourceCSPAllRowLoop.Stack q => Bool)
            (SourceCSPAllRowLoop.Label hq)
            (SourceCSPAllRowLoop.Control hq)) =
        ⟨none, .done true,
          SourceCSPNextRowBridge.callbackBank
            (SourceCSPAllRowLoop.withRemaining S' 0)
            lastRow n (m - 1)
            ((EncodedCNF.clauseFields clauses).reverse ++ saved)
            output (List.replicate clauses.length true ++ count)⟩ ∧
      lastRow (.inr 0) = [] := by
  let S' := Function.update S SourceCSPHeaderRowBridge.loopCount []
  have hS' : ∀ x, (S' x).length ≤ H := by
    intro x
    by_cases hx : x = SourceCSPHeaderRowBridge.loopCount
    · subst x
      simp [S']
    · simpa [S', Function.update_of_ne hx] using hS x
  have hheader' : S' SourceCSPHeaderRowBridge.count =
      List.replicate m true := by
    simpa [S', SourceCSPHeaderRowBridge.count,
      SourceCSPHeaderRowBridge.loopCount] using hheader
  have hcap' : S' SourceCSPHeaderRowBridge.capSource =
      List.replicate (n - 1) true := by
    simpa [S', SourceCSPHeaderRowBridge.capSource,
      SourceCSPHeaderRowBridge.loopCount] using hcap
  have hzero : S' SourceCSPHeaderRowBridge.loopCount = [] := by
    simp [S']
  obtain ⟨tl, lastRow, htl, hrun, hlast⟩ :=
    SourceCSPAllRowLoopClock.all_remaining_after_first_polynomial
      rows hq L hn hm hword hcapL hnH hmH ht hL
      S' row saved output count hS' hrow hsaved houtput
      hcountWords hheader' hzero hcap' hsource hsourceLen
  refine ⟨(S SourceCSPHeaderRowBridge.loopCount).length + 2,
    tl, lastRow, ?_, htl, ?_, hrun, hlast⟩
  · have hc := hS SourceCSPHeaderRowBridge.loopCount
    omega
  · exact clear_callback_bank_run S row saved output count

/-- The first-row parser's physical unread word is literally the canonical
suffix of the same typed rows recovered from the raw validator. -/
theorem physical_first_rest {n m q : Nat}
    (hm : 0 < m) (suffix rest : List Bool)
    (rows : Fin m → SourceCSPCodec.Row n 2 q)
    (hread : SourceCSPCodec.readFn (SourceCSPCodec.readRow n 2 q) m suffix =
      some (rows, []))
    (hfirst : suffix =
      SourceCSPCodec.rowFields (rows ⟨0, hm⟩) ++ rest) :
    rest = SourceCSPCodec.fnFields SourceCSPCodec.rowFields
      (SourceCSPAllRowLoop.remainingRows rows 0 (m - 1)
        (by omega)) := by
  have hcanonical := RawCanonicalReadback.successful_rows_literal
    suffix rows hread
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
  subst m
  rw [SourceCSPCodec.fnFields_succ] at hcanonical
  rw [hfirst] at hcanonical
  have htail : rest = SourceCSPCodec.fnFields SourceCSPCodec.rowFields
      (fun j : Fin k => rows j.succ) :=
    List.append_cancel_left hcanonical
  convert htail using 1
  congr 1
  funext j
  apply congrArg rows
  apply Fin.ext
  change 0 + 1 + j.val = j.succ.val
  simp only [Fin.val_succ]
  omega

/-- An actual accepting raw validator run yields an actual physical first-row
halt. The retained row source is the literal suffix of the typed input. -/
theorem raw_accepted_first_row (q : Nat) (input : List Bool)
    (ta : Nat)
    (vr : SourceCSPRowLoopController.QueryControl ×
      SourceCSPRowLoopController.ResetControl)
    (Sa : SourceCSPGlobalDecisionProgram.Stack q → List Bool)
    (hacc : ((advance (SourceCSPGlobalDecisionProgram.program 2 q))^[ta])
      (SourceCSPGlobalDecisionProgram.initial 2 q input) =
        ⟨none, .row (vr, some true), Sa⟩) :
    ∃ (n m : Nat) (hm : 0 < m) (suffix rest : List Bool)
      (rows : Fin m → SourceCSPCodec.Row n 2 q)
      (t : Nat) (v : SourceCSPFirstRowController.Control 2 q)
      (U : SourceCSPFirstRowController.Stack q → List Bool),
      0 < n ∧ n ≤ q * m ∧
      input = SourceCSPHeaderParse.header n m 2 q ++ suffix ∧
      SourceCSPCodec.readFn (SourceCSPCodec.readRow n 2 q) m suffix =
        some (rows, []) ∧
      t ≤ SourceCSPFirstRowController.cubicCoefficient 2 q *
        (input.length + 1) ^ 3 ∧
      ((advance (SourceCSPFirstRowController.program 2 q))^[t])
        (SourceCSPFirstRowController.initial 2 q input) =
          ⟨none, v, U⟩ ∧
      (∀ g : SourceCSPGlobalDecisionProgram.Stack q,
        U (.inl g) = Sa g) ∧
      SourceCSPFirstSlotBridge.row U (.inr 0) =
        SourceCSPCodec.fnFields SourceCSPCodec.rowFields
          (SourceCSPAllRowLoop.remainingRows rows 0 (m - 1)
            (by omega)) ∧
      (∀ j : Fin q,
        SourceCSPFirstSlotBridge.row U (.inl (j, 1)) =
          List.replicate ((rows ⟨0, hm⟩).1 j).val true) ∧
      SourceCSPFirstSlotBridge.row U (.inr 2) =
        true :: List.ofFn (rows ⟨0, hm⟩).2 ∧
      SourceCSPFirstSlotBridge.writer U SourceClauseRowWriterOperands.vertex =
        List.replicate n true ∧
      SourceCSPFirstSlotBridge.writer U SourceClauseRowWriterOperands.rowIndex =
        [] ∧
      Sa SourceCSPHeaderRowBridge.count = List.replicate m true ∧
      Sa SourceCSPHeaderRowBridge.capSource =
        List.replicate (n - 1) true := by
  obtain ⟨n, m, suffix, rows, hn, hm, hsize, _hmL,
    hinput, hread, hsaved, hcap, hcount⟩ :=
    raw_accepted_source q input ta vr Sa hacc
  obtain ⟨tg, htg, hglobal⟩ :=
    bounded_accepted_global q input ta vr Sa hacc
  obtain ⟨t, U, rest, v, ht, hrun, hfirst,
    hquery, htruth, hsource, _hstatus, hleft, hvertex, hindex⟩ :=
    SourceCSPFirstSlotBridge.accepted_first_row_ready
      input suffix rows tg vr Sa hn hm hglobal hsaved hcap hread
  have ⟨hsuffixL, hmL⟩ :=
    RawCanonicalReadback.successful_rows_length_bounds
      input suffix rows hinput hread
  have ⟨hstage, hrow⟩ :=
    SourceCSPFirstRowController.bounds_le_uniform 2 q n m input.length
      suffix (by simp [hinput])
      hsize hmL
  have htC : t ≤ SourceCSPFirstRowController.controllerBound 2 q
      input.length := by
    unfold SourceCSPFirstRowController.controllerBound
    omega
  have ht3 := htC.trans
    (SourceCSPFirstRowController.controllerBound_le_cubic 2 q
      input.length)
  refine ⟨n, m, hm, suffix, rest, rows, t, v, U,
    hn, hsize, hinput, hread, ht3, hrun, hleft, ?_,
    hquery, htruth, hvertex, hindex, hcount, hcap⟩
  rw [hsource]
  exact physical_first_rest hm suffix rest rows hread hfirst

/-- The actual first-slot callback, started at the physically parsed first
row after the supplied prefix accumulator insertion, produces the precise
same-bank input required by the remaining-row controller. -/
theorem first_callback_exact {n m q : Nat}
    (hq : 0 < q) (hm : 0 < m)
    (rows : Fin m → SourceCSPCodec.Row n 2 q)
    (U : SourceCSPFirstRowController.Stack q → List Bool)
    (saved output count : List Bool)
    (htruth : SourceCSPFirstSlotBridge.row U (.inr 2) =
      true :: List.ofFn (rows ⟨0, hm⟩).2)
    (hquery : ∀ j : Fin q,
      SourceCSPFirstSlotBridge.row U (.inl (j, 1)) =
        List.replicate ((rows ⟨0, hm⟩).1 j).val true)
    (hn : SourceCSPFirstSlotBridge.writer U
      SourceClauseRowWriterOperands.vertex = List.replicate n true)
    (hr : SourceCSPFirstSlotBridge.writer U
      SourceClauseRowWriterOperands.rowIndex = []) :
    let Ub := prefixBank U saved output count
    let row := SourceCSPFirstSlotBridge.row Ub
    let clauses := SourceCSPAllRowLoop.rowClauses rows hq ⟨0, hm⟩
    ∃ t ≤ SourceCSPFirstSlotBridge.cleanupTime Ub +
      SourceClauseCallback.AllSlotsClock.allCost hq row n 0
        (rows ⟨0, hm⟩).2 saved output count + 1,
      ((advance (callbackProgram q hq))^[t])
        (callbackInitial q hq Ub) =
        ⟨none, (((), none),
          (SourceClauseCallback.AllSlots.allCircuit hq).initial),
          SourceCSPNextRowBridge.callbackBank
            (fun g => U (.inl g)) row n 0
            ((EncodedCNF.clauseFields clauses).reverse ++ saved)
            output (List.replicate clauses.length true ++ count)⟩ := by
  let Ub := prefixBank U saved output count
  let row := SourceCSPFirstSlotBridge.row Ub
  let clauses := SourceCSPAllRowLoop.rowClauses rows hq ⟨0, hm⟩
  have htruth' : SourceCSPFirstSlotBridge.row Ub (.inr 2) =
      true :: List.ofFn (rows ⟨0, hm⟩).2 := by
    rw [prefixBank_row]
    exact htruth
  have hquery' : ∀ j : Fin q,
      SourceCSPFirstSlotBridge.row Ub (.inl (j, 1)) =
        List.replicate ((rows ⟨0, hm⟩).1 j).val true := by
    intro j
    rw [prefixBank_row]
    exact hquery j
  have hn' : SourceCSPFirstSlotBridge.writer Ub
      SourceClauseRowWriterOperands.vertex = List.replicate n true := by
    rw [prefixBank_vertex]
    exact hn
  have hr' : SourceCSPFirstSlotBridge.writer Ub
      SourceClauseRowWriterOperands.rowIndex = [] := by
    rw [prefixBank_rowIndex]
    exact hr
  obtain ⟨t, ht, hrun⟩ :=
    SourceCSPFirstSlotBridge.typed_first_row_all_slots
      hq hm rows Ub htruth' hquery' hn' hr'
  refine ⟨t, ?_, ?_⟩
  · simpa only [Ub, row, prefixBank_saved, prefixBank_output,
      prefixBank_count] using ht
  · have hbank :
        Sum.elim (fun g => Ub (.inl g))
          (SourceClauseRowWriterTruthFrame.initial row n 0
            ((EncodedCNF.clauseFields clauses).reverse ++ saved)
            output (List.replicate clauses.length true ++ count)) =
        SourceCSPNextRowBridge.callbackBank
          (fun g => U (.inl g)) row n 0
          ((EncodedCNF.clauseFields clauses).reverse ++ saved)
          output (List.replicate clauses.length true ++ count) := by
      funext x
      cases x with
      | inl g =>
          exact prefixBank_global U saved output count g
      | inr k => rfl
    have hsave : SourceCSPFirstSlotBridge.writer Ub
        SourceClauseRowWriterCleanup.savedCell = saved :=
      prefixBank_saved U saved output count
    have hout : SourceCSPFirstSlotBridge.writer Ub
        SourceClauseRowWriterCleanup.outputCell = output :=
      prefixBank_output U saved output count
    have hcount : SourceCSPFirstSlotBridge.writer Ub
        SourceClauseRowWriterCleanup.countCell = count :=
      prefixBank_count U saved output count
    rw [hsave, hout, hcount] at hrun
    change ((advance (callbackProgram q hq))^[t])
        (callbackInitial q hq Ub) =
      ⟨none, (((), none),
        (SourceClauseCallback.AllSlots.allCircuit hq).initial),
        Sum.elim (fun g => Ub (.inl g))
          (SourceClauseRowWriterTruthFrame.initial row n 0
            ((EncodedCNF.clauseFields clauses).reverse ++ saved)
            output (List.replicate clauses.length true ++ count))⟩ at hrun
    rw [hbank] at hrun
    exact hrun

noncomputable def callbackClock (q B : Nat) : Nat :=
  SourceClauseClearExcept.workCount
      (SourceClauseRowWriterCleanup.keep q) * (B + 1) + 2 +
    SourceClauseCallbackAllSlotPolynomial.allCoefficient q * (B + 1) ^ 2 + 1

/-- The typed first callback's exact physical output satisfies the stack-growth
envelope. This does not assume a post-callback bank witness. -/
theorem first_callback_bounded {n m q B : Nat}
    (hq : 0 < q) (hm : 0 < m)
    (rows : Fin m → SourceCSPCodec.Row n 2 q)
    (U : SourceCSPFirstRowController.Stack q → List Bool)
    (saved output count : List Bool)
    (hUb : ∀ x, (prefixBank U saved output count x).length ≤ B)
    (hnB : n ≤ B)
    (htruth : SourceCSPFirstSlotBridge.row U (.inr 2) =
      true :: List.ofFn (rows ⟨0, hm⟩).2)
    (hquery : ∀ j : Fin q,
      SourceCSPFirstSlotBridge.row U (.inl (j, 1)) =
        List.replicate ((rows ⟨0, hm⟩).1 j).val true)
    (hn : SourceCSPFirstSlotBridge.writer U
      SourceClauseRowWriterOperands.vertex = List.replicate n true)
    (hr : SourceCSPFirstSlotBridge.writer U
      SourceClauseRowWriterOperands.rowIndex = []) :
    let Ub := prefixBank U saved output count
    let row := SourceCSPFirstSlotBridge.row Ub
    let clauses := SourceCSPAllRowLoop.rowClauses rows hq ⟨0, hm⟩
    let V := SourceCSPNextRowBridge.callbackBank
      (fun g => U (.inl g)) row n 0
      ((EncodedCNF.clauseFields clauses).reverse ++ saved)
      output (List.replicate clauses.length true ++ count)
    ∃ t ≤ callbackClock q B,
      ((advance (callbackProgram q hq))^[t])
        (callbackInitial q hq Ub) =
        ⟨none, (((), none),
          (SourceClauseCallback.AllSlots.allCircuit hq).initial), V⟩ ∧
      ∀ x, (V x).length ≤ callbackEnvelope q hq B := by
  let Ub := prefixBank U saved output count
  let row := SourceCSPFirstSlotBridge.row Ub
  let clauses := SourceCSPAllRowLoop.rowClauses rows hq ⟨0, hm⟩
  let V := SourceCSPNextRowBridge.callbackBank
    (fun g => U (.inl g)) row n 0
    ((EncodedCNF.clauseFields clauses).reverse ++ saved)
    output (List.replicate clauses.length true ++ count)
  obtain ⟨t, ht, hrun⟩ := first_callback_exact hq hm rows U
    saved output count htruth hquery hn hr
  have hqueryUnary : ∀ j : Fin q,
      row (.inl (j, 1)) = List.replicate
        (row (.inl (j, 1))).length true := by
    intro j
    rw [show row (.inl (j, 1)) =
      SourceCSPFirstSlotBridge.row U (.inl (j, 1)) from
      prefixBank_row U saved output count _]
    rw [hquery j]
    simp
  have ht' : t ≤ SourceCSPFirstSlotBridge.cleanupTime Ub +
      SourceClauseCallback.AllSlotsClock.allCost hq row n 0
        (rows ⟨0, hm⟩).2
        (SourceCSPFirstSlotBridge.writer Ub
          SourceClauseRowWriterCleanup.savedCell)
        (SourceCSPFirstSlotBridge.writer Ub
          SourceClauseRowWriterCleanup.outputCell)
        (SourceCSPFirstSlotBridge.writer Ub
          SourceClauseRowWriterCleanup.countCell) + 1 := by
    simpa only [Ub, row, prefixBank_saved, prefixBank_output,
      prefixBank_count] using ht
  have hV := callback_terminal_bank_le q hq Ub B n t
    (rows ⟨0, hm⟩).2 V hUb hnB hqueryUnary ht' hrun
  have hcleanup := cleanupTime_le Ub hUb
  have hcost := SourceClauseCallbackAllSlotPolynomial.allCost_le_quadratic
    hq row n 0 B (rows ⟨0, hm⟩).2
    (SourceCSPFirstSlotBridge.writer Ub SourceClauseRowWriterCleanup.savedCell)
    (SourceCSPFirstSlotBridge.writer Ub SourceClauseRowWriterCleanup.outputCell)
    (SourceCSPFirstSlotBridge.writer Ub SourceClauseRowWriterCleanup.countCell)
    hnB (Nat.zero_le B) (fun x => hUb _)
    (hUb _) (hUb _) (hUb _) hqueryUnary
  have htClock : t ≤ callbackClock q B := by
    dsimp [callbackClock]
    omega
  exact ⟨t, htClock, hrun, hV⟩

/-- The unchecked first-callback bank provides all five word-size premises
required by the post-first-row polynomial loop theorem. -/
theorem callback_words_for_loop {n q H : Nat}
    (S : SourceCSPGlobalDecisionProgram.Stack q → List Bool)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (saved output count : List Bool)
    (hV : ∀ x,
      (SourceCSPNextRowBridge.callbackBank S row n 0
        saved output count x).length ≤ H) :
    (∀ x, (S x).length ≤ H) ∧
      (∀ x, (row x).length ≤ H) ∧
      saved.length ≤ H ∧ output.length ≤ H ∧
      count.length ≤ H := by
  let V := SourceCSPNextRowBridge.callbackBank S row n 0
    saved output count
  have ⟨_, _, _, _, _, hsave, hout, hcount⟩ :=
    SourceCSPNextRowBridge.callback_bank_fields S row n 0
      saved output count
  have hS : ∀ x, (S x).length ≤ H := by
    intro x
    exact hV (.inl x)
  have hrow : ∀ x, (row x).length ≤ H := by
    intro x
    have h := hV (SourceCSPNextRowBridge.rowEmbedding x)
    rwa [SourceCSPNextRowBridge.callback_bank_row] at h
  have hsaved : saved.length ≤ H := by
    rw [← hsave]
    exact hV (SourceCSPFirstSlotBridge.writerEmbedding
      SourceClauseRowWriterCleanup.savedCell)
  have houtput : output.length ≤ H := by
    rw [← hout]
    exact hV (SourceCSPFirstSlotBridge.writerEmbedding
      SourceClauseRowWriterCleanup.outputCell)
  have hcountWords : count.length ≤ H := by
    rw [← hcount]
    exact hV (SourceCSPFirstSlotBridge.writerEmbedding
      SourceClauseRowWriterCleanup.countCell)
  exact ⟨hS, hrow, hsaved, houtput, hcountWords⟩

/-- Physical accepted-source continuation, with no assumed parsed rows,
post-callback payload, or completed loop. The only incoming words outside the
raw source are the supplied prefix accumulators. Each phase runs its fixed
machine; the aggregate budget separately charges three control transfers. -/
theorem raw_accepted_full_row_continuation (q : Nat) (hq : 0 < q)
    (input : List Bool) (ta : Nat)
    (vr : SourceCSPRowLoopController.QueryControl ×
      SourceCSPRowLoopController.ResetControl)
    (Sa : SourceCSPGlobalDecisionProgram.Stack q → List Bool)
    (hacc : ((advance (SourceCSPGlobalDecisionProgram.program 2 q))^[ta])
      (SourceCSPGlobalDecisionProgram.initial 2 q input) =
        ⟨none, .row (vr, some true), Sa⟩)
    (saved output count : List Bool) :
    let A := saved.length + output.length + count.length
    let B := entryBase q input.length A
    let H := entryEnvelope q hq input.length A
    ∃ (n m : Nat) (hm : 0 < m)
      (rows : Fin m → SourceCSPCodec.Row n 2 q)
      (tf : Nat) (v : SourceCSPFirstRowController.Control 2 q)
      (U : SourceCSPFirstRowController.Stack q → List Bool)
      (tc tclear tloop : Nat)
      (lastRow : SourceCSPRowQueryFrame.Stack q → List Bool),
      let Ub := prefixBank U saved output count
      let row := SourceCSPFirstSlotBridge.row Ub
      let first := SourceCSPAllRowLoop.rowClauses rows hq ⟨0, hm⟩
      let suffix := SourceCSPAllRowLoop.suffixClauses rows hq 0
        (m - 1) (by omega)
      let saved' := (EncodedCNF.clauseFields first).reverse ++ saved
      let count' := List.replicate first.length true ++ count
      let Sc := Function.update Sa SourceCSPHeaderRowBridge.loopCount []
      n ≤ H ∧ m ≤ H ∧
      tf ≤ SourceCSPFirstRowController.cubicCoefficient 2 q *
        (input.length + 1) ^ 3 ∧
      tc ≤ callbackClock q B ∧
      tclear ≤ H + 2 ∧
      tloop ≤ SourceCSPAllRowLoopClock.loopCoefficient q * (H + 1) ^ 9 ∧
      tf + 1 + tc + 1 + tclear + 1 + tloop ≤
        SourceCSPFirstRowController.cubicCoefficient 2 q *
          (input.length + 1) ^ 3 +
        callbackClock q B + (H + 2) +
        SourceCSPAllRowLoopClock.loopCoefficient q * (H + 1) ^ 9 + 3 ∧
      ((advance (SourceCSPFirstRowController.program 2 q))^[tf])
        (SourceCSPFirstRowController.initial 2 q input) =
          ⟨none, v, U⟩ ∧
      ((advance (callbackProgram q hq))^[tc])
        (callbackInitial q hq Ub) =
          ⟨none, (((), none),
            (SourceClauseCallback.AllSlots.allCircuit hq).initial),
            SourceCSPNextRowBridge.callbackBank Sa row n 0
              saved' output count'⟩ ∧
      ((advance (clearLoopProgram q))^[tclear])
        (⟨some 0, ((), none),
          SourceCSPNextRowBridge.callbackBank Sa row n 0
            saved' output count'⟩ :
          TM2.Cfg (fun _ : SourceCSPAllRowLoop.Stack q => Bool)
            (Fin 2) (Unit × Option Bool)) =
          ⟨none, ((), none),
            SourceCSPNextRowBridge.callbackBank Sc row n 0
              saved' output count'⟩ ∧
      ((advance (SourceCSPAllRowLoop.program hq))^[tloop])
        (⟨some (.copy .scan), .copy none,
          SourceCSPNextRowBridge.callbackBank Sc row n 0
            saved' output count'⟩ :
          TM2.Cfg (fun _ : SourceCSPAllRowLoop.Stack q => Bool)
            (SourceCSPAllRowLoop.Label hq)
            (SourceCSPAllRowLoop.Control hq)) =
          ⟨none, .done true,
            SourceCSPNextRowBridge.callbackBank
              (SourceCSPAllRowLoop.withRemaining Sc 0)
              lastRow n (m - 1)
              ((EncodedCNF.clauseFields suffix).reverse ++ saved')
              output (List.replicate suffix.length true ++ count')⟩ ∧
      lastRow (.inr 0) = [] := by
  let A := saved.length + output.length + count.length
  let B := entryBase q input.length A
  let H := entryEnvelope q hq input.length A
  obtain ⟨n, m, hm, source, rest, rows, tf, v, U,
    hn, hsize, hinput, hread, htfirst, hfirstRun, hleft,
    hsource, hquery, htruth, hvertex, hindex, hheader, hcap⟩ :=
    raw_accepted_first_row q input ta vr Sa hacc
  have hfirstWords := actual_first_bank_le q input tf v U
    htfirst hfirstRun
  have hUbB : ∀ x, (prefixBank U saved output count x).length ≤ B :=
    prefixBank_length_le q input U saved output count hfirstWords
  have ⟨hnB, _hmB, _hqB⟩ :=
    entry_base_raw_bounds input source rows A hinput hread hsize
  have ⟨hnH, hmH, hcapH, hqH, _hsourceH, hword⟩ :=
    entry_envelope_parameters hq input source rows saved output count
      hinput hread hsize
  let Ub := prefixBank U saved output count
  let row := SourceCSPFirstSlotBridge.row Ub
  let first := SourceCSPAllRowLoop.rowClauses rows hq ⟨0, hm⟩
  let saved' := (EncodedCNF.clauseFields first).reverse ++ saved
  let count' := List.replicate first.length true ++ count
  let V := SourceCSPNextRowBridge.callbackBank Sa row n 0
    saved' output count'
  have ⟨tc, htc, hcallbackRun, hVB⟩ :=
    first_callback_bounded hq hm rows U saved output count
      hUbB hnB htruth hquery hvertex hindex
  have hVeq : V = SourceCSPNextRowBridge.callbackBank
      (fun g => U (.inl g)) row n 0 saved' output count' := by
    funext x
    cases x with
    | inl g => exact (hleft g).symm
    | inr x => rfl
  have hCbH := (entry_envelope_base q input.length A hq).1
  have hVH : ∀ x, (V x).length ≤ H := by
    intro x
    rw [hVeq]
    exact (hVB x).trans hCbH
  obtain ⟨hS, hrow, hsave, hout, hcount⟩ :=
    callback_words_for_loop Sa row saved' output count' hVH
  have hsource' : row (.inr 0) =
      SourceCSPCodec.fnFields SourceCSPCodec.rowFields
        (SourceCSPAllRowLoop.remainingRows rows 0 (m - 1)
          (by omega)) := by
    change SourceCSPFirstSlotBridge.row
      (prefixBank U saved output count) (.inr 0) = _
    rw [prefixBank_row]
    exact hsource
  have hsourceLen := hrow (.inr 0)
  obtain ⟨tclear, tloop, lastRow, htclear, htloop,
    hclearRun, hloopRun, hlast⟩ :=
    all_remaining_after_first_with_clear rows hq n hn hm
      hword (Nat.sub_le n 1) hnH hmH hqH hnH
      Sa row saved' output count' hS hrow hsave hout hcount
      hheader hcap hsource' hsourceLen
  refine ⟨n, m, hm, rows, tf, v, U, tc, tclear, tloop,
    lastRow, hnH, hmH, htfirst, htc, htclear, htloop, ?_,
    hfirstRun, ?_, hclearRun, hloopRun, hlast⟩
  · change tf + 1 + tc + 1 + tclear + 1 + tloop ≤
      SourceCSPFirstRowController.cubicCoefficient 2 q *
        (input.length + 1) ^ 3 +
      callbackClock q B + (H + 2) +
      SourceCSPAllRowLoopClock.loopCoefficient q * (H + 1) ^ 9 + 3
    change tclear ≤ H + 2 at htclear
    change tloop ≤
      SourceCSPAllRowLoopClock.loopCoefficient q * (H + 1) ^ 9 at htloop
    omega
  · simpa only [Ub, row, first, saved', count', V, hVeq] using hcallbackRun

end EthInapproximability.CurrentPaper.SourceCSPEntryBound
