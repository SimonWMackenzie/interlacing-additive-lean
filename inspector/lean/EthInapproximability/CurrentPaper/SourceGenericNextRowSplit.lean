import EthInapproximability.CurrentPaper.SourceGenericNextParserGrowth
import EthInapproximability.CurrentPaper.SourceGenericNextRowFrameGrowth
import EthInapproximability.CurrentPaper.SourceCSPNextRowFrameGrowth

/-! Exact next-row program run with the same parser witness carrying the
noncircular all-word and cleanup-clock estimates. -/

namespace EthInapproximability.CurrentPaper.SourceGenericNextRowSplit

open Turing BitMachineEncoding BitMachineStackEmbedding
open SourceGenericNextParserGrowth SourceGenericNextRowFrameGrowth
open scoped Classical

theorem next_row_single_program_split {n a q H G : ℕ}
    (next : SourceCSPCodec.Row n a q)
    (B : SourceCSPNextRowBridge.Stack q → List Bool)
    (rest tail saved output count : List Bool)
    (r L : ℕ)
    (hn : 0 < n)
    (hrest : rest = SourceCSPCodec.rowFields next ++ tail)
    (hsource : B (SourceCSPNextRowBridge.rowEmbedding (.inr 0)) = rest)
    (hcap : B (.inl SourceCSPHeaderRowBridge.capSource) =
      List.replicate (n - 1) true)
    (hscratch : B (.inr (.inl SourceClauseRowWriterOperands.scratch)) = [])
    (hcursor : ∀ i : Fin 2, B (.inr (.inr i)) = [])
    (hvertex : SourceCSPNextRowBridge.writerProjection B
      SourceClauseRowWriterOperands.vertex = List.replicate n true)
    (hindex : SourceCSPNextRowBridge.writerProjection B
      SourceClauseRowWriterOperands.rowIndex = List.replicate r true)
    (hsaved : SourceCSPNextRowBridge.writerProjection B
      SourceClauseRowWriterCleanup.savedCell = saved)
    (houtput : SourceCSPNextRowBridge.writerProjection B
      SourceClauseRowWriterCleanup.outputCell = output)
    (hcount : SourceCSPNextRowBridge.writerProjection B
      SourceClauseRowWriterCleanup.countCell = count)
    (hword : ∀ j : Fin q, (next.1 j).val.bits.length ≤ L)
    (hcapL : n - 1 ≤ L)
    (hB : ∀ x, (B x).length ≤ G)
    (hrestLen : rest.length ≤ H) (hL : L ≤ H)
    (hHG : H ≤ G) :
    ∃ (t : ℕ) (V : SourceCSPRowQueryFrame.Stack q → List Bool),
      t ≤ SourceCSPNextRowBridge.resetCost B
            (List.replicate (n - 1) true) +
          parseBudget a q rest L + 2 +
          cleanupCoefficient a q * (G + 1) ^ 2 + 3 ∧
      ((advance (SourceCSPNextRowBridge.nextProgram q a))^[t])
        (⟨some (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel
              (BitMachineRawSequence.leftLabel 0))),
          (((((), none), none), SourceCSPNextRowBridge.parseControlStart),
            ((), ((), none))), B⟩ :
          TM2.Cfg (fun _ : SourceCSPNextRowBridge.Stack q => Bool) _ _) =
        ⟨none,
          (((((), none), none), SourceCSPNextRowBridge.parseControlStart),
            ((), ((), none))),
          Sum.elim (fun g => B (.inl g))
            (SourceClauseRowWriterTruthFrame.initial V n (r + 1)
              saved output count)⟩ ∧
      (∀ x, (V x).length ≤ parseWordCoefficient a q * (H + 1) ^ 2) ∧
      V (.inr 0) = tail ∧ V (.inr 4) = [true] ∧
      (∀ j : Fin q, V (.inl (j, 1)) =
        List.replicate (next.1 j).val true) ∧
      V (.inr 2) = true :: List.ofFn next.2 := by
  let cap := List.replicate (n - 1) true
  obtain ⟨tR, htR, hrunR⟩ :=
    SourceCSPNextRowBridge.reset_run q B rest cap hsource hcap hscratch
  obtain ⟨tP, v, V, htP, hrunP, hV, htail, hstatus, hquery, htruth⟩ :=
    parse_next_row_all_words next B rest tail L hn hrest hword hcapL
      hrestLen hL
  have hcapLen : cap.length ≤ H := by
    dsimp [cap]
    simp only [List.length_replicate]
    omega
  have hquad : (H + 1) ^ 2 ≤ (G + 1) ^ 2 :=
    Nat.pow_le_pow_left (by omega) 2
  have hV_G : ∀ x, (V x).length ≤
      parseWordCoefficient a q * (G + 1) ^ 2 := by
    intro x
    exact (hV x).trans (Nat.mul_le_mul_left _ hquad)
  have hclean := callbackCleanupTime_le_quadratic B rest cap V
    hB (hrestLen.trans hHG) (hcapLen.trans hHG) hV_G
  have hcursor' : ∀ i : Fin 2,
      SourceCSPNextRowBridge.steppedResult B rest cap V (.inr (.inr i)) = [] := by
    intro i
    rw [SourceCSPNextRowBridge.stepped_cursor]
    exact hcursor i
  have hvertex' : SourceCSPNextRowBridge.writerProjection
      (SourceCSPNextRowBridge.steppedResult B rest cap V)
      SourceClauseRowWriterOperands.vertex = List.replicate n true := by
    rw [SourceCSPNextRowBridge.writerProjection,
      SourceCSPNextRowBridge.stepped_writer_frame]
    · exact hvertex
    · intro x
      cases x <;> simp [SourceClauseRowWriterOperands.vertex,
        SourceClauseRowWriterCleanup.rowCell]
    · simp [SourceClauseRowWriterOperands.vertex,
        SourceClauseRowWriterOperands.rowIndex]
  have hindex' := SourceCSPNextRowBridge.stepped_index B rest cap V r hindex
  have hbank := SourceCSPNextRowBridge.callback_bank_after_step
    B rest cap saved output count V n r hsaved houtput hcount
  have hrunA := SourceCSPNextRowBridge.advance_run q
    (SourceCSPNextRowBridge.parsedResult B rest cap V)
  have hrunC := SourceCSPNextRowBridge.callback_cleanup_run
    (SourceCSPNextRowBridge.steppedResult B rest cap V)
    n (r + 1) hcursor' hvertex' hindex'
  obtain ⟨tRead, htRead, hrunRead⟩ :=
    BitMachineRawSequence.runs
      (SourceCSPNextRowBridge.resetProgram q)
      (SourceCSPNextRowBridge.parseProgram q a)
      (BitMachineRawSequence.leftLabel 0)
      (SourceCSPNextRowBridge.parseStart (q := q) (a := a))
      (((), none), none) (((), none), none)
      SourceCSPNextRowBridge.parseControlStart v B
      (SourceCSPNextRowBridge.resetResult B rest cap)
      (SourceCSPNextRowBridge.parsedResult B rest cap V)
      tR tP hrunR hrunP
  obtain ⟨tFinish, htFinish, hrunFinish⟩ :=
    BitMachineRawSequence.runs
      (SourceCSPNextRowBridge.advanceProgram q)
      (SourceCSPFirstSlotBridge.cleanupProgram (q := q))
      (.push) (.clear 0) () () ((), none) ((), none)
      (SourceCSPNextRowBridge.parsedResult B rest cap V)
      (SourceCSPNextRowBridge.steppedResult B rest cap V)
      (SourceCSPNextRowBridge.callbackResult
        (SourceCSPNextRowBridge.steppedResult B rest cap V) n (r + 1))
      2 (SourceCSPNextRowBridge.callbackCleanupTime
        (SourceCSPNextRowBridge.steppedResult B rest cap V))
      hrunA hrunC
  obtain ⟨t, ht, hrun⟩ :=
    BitMachineRawSequence.runs
      (SourceCSPNextRowBridge.readProgram q a)
      (SourceCSPNextRowBridge.finishProgram q)
      (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel 0))
      (BitMachineRawSequence.leftLabel .push)
      ((((), none), none), SourceCSPNextRowBridge.parseControlStart)
      ((((), none), none), v)
      ((), ((), none)) ((), ((), none))
      B (SourceCSPNextRowBridge.parsedResult B rest cap V)
      (SourceCSPNextRowBridge.callbackResult
        (SourceCSPNextRowBridge.steppedResult B rest cap V) n (r + 1))
      tRead tFinish hrunRead hrunFinish
  refine ⟨t, V, ?_, ?_, hV, htail, hstatus, hquery, htruth⟩
  · dsimp only [cap] at htR htFinish hclean ⊢
    omega
  · rw [hbank] at hrun
    simpa only [SourceCSPNextRowBridge.nextProgram,
      SourceCSPNextRowBridge.readProgram,
      SourceCSPNextRowBridge.finishProgram,
      SourceCSPNextRowBridge.parseStart] using hrun

theorem next_row_after_callback_split {n a q m H G : ℕ}
    (rows : Fin (m + 1) → SourceCSPCodec.Row n a q)
    (S : SourceCSPGlobalDecisionProgram.Stack q → List Bool)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (saved output count : List Bool) (r L : ℕ)
    (hn : 0 < n)
    (hsource : row (.inr 0) =
      SourceCSPCodec.fnFields SourceCSPCodec.rowFields rows)
    (hcap : S SourceCSPHeaderRowBridge.capSource =
      List.replicate (n - 1) true)
    (hword : ∀ j : Fin q, ((rows 0).1 j).val.bits.length ≤ L)
    (hcapL : n - 1 ≤ L)
    (hS : ∀ x, (S x).length ≤ G)
    (hrow : ∀ x, (row x).length ≤ G)
    (hnH : n ≤ G) (hrH : r ≤ G)
    (hsaved : saved.length ≤ G)
    (houtput : output.length ≤ G)
    (hcount : count.length ≤ G)
    (hrestLen : (SourceCSPCodec.fnFields SourceCSPCodec.rowFields rows).length ≤ H)
    (hL : L ≤ H) (hHG : H ≤ G) :
    let rest := SourceCSPCodec.fnFields SourceCSPCodec.rowFields rows
    let tail := SourceCSPCodec.fnFields SourceCSPCodec.rowFields
      (fun j : Fin m => rows j.succ)
    let B := SourceCSPNextRowBridge.callbackBank S row n r saved output count
    ∃ (t : ℕ) (V : SourceCSPRowQueryFrame.Stack q → List Bool),
      t ≤ SourceCSPNextRowBridge.resetCost B
            (List.replicate (n - 1) true) +
          parseBudget a q rest L + 2 +
          cleanupCoefficient a q * (G + 1) ^ 2 + 3 ∧
      ((advance (SourceCSPNextRowBridge.nextProgram q a))^[t])
        (⟨some (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel
              (BitMachineRawSequence.leftLabel 0))),
          (((((), none), none), SourceCSPNextRowBridge.parseControlStart),
            ((), ((), none))), B⟩ :
          TM2.Cfg (fun _ : SourceCSPNextRowBridge.Stack q => Bool) _ _) =
        ⟨none,
          (((((), none), none), SourceCSPNextRowBridge.parseControlStart),
            ((), ((), none))),
          SourceCSPNextRowBridge.callbackBank S V n (r + 1)
            saved output count⟩ ∧
      (∀ x, (V x).length ≤ parseWordCoefficient a q * (H + 1) ^ 2) ∧
      V (.inr 0) = tail ∧ V (.inr 4) = [true] ∧
      (∀ j : Fin q, V (.inl (j, 1)) =
        List.replicate ((rows 0).1 j).val true) ∧
      V (.inr 2) = true :: List.ofFn (rows 0).2 := by
  let rest := SourceCSPCodec.fnFields SourceCSPCodec.rowFields rows
  let tail := SourceCSPCodec.fnFields SourceCSPCodec.rowFields
    (fun j : Fin m => rows j.succ)
  let B := SourceCSPNextRowBridge.callbackBank S row n r
    saved output count
  obtain ⟨hcapB, hscratch, hcursor, hvertex, hindex,
    hsavedB, houtputB, hcountB⟩ :=
    SourceCSPNextRowBridge.callback_bank_fields S row n r
      saved output count
  have hsourceB : B (SourceCSPNextRowBridge.rowEmbedding (.inr 0)) = rest := by
    change SourceCSPNextRowBridge.callbackBank S row n r saved output count
      (SourceCSPNextRowBridge.rowEmbedding (.inr 0)) = rest
    rw [SourceCSPNextRowBridge.callback_bank_row]
    exact hsource
  have hrest : rest = SourceCSPCodec.rowFields (rows 0) ++ tail :=
    SourceCSPNextRowBridge.remaining_rows_succ rows
  have hB := callbackBank_words_le S row n r saved output count
    hS hrow hnH hrH hsaved houtput hcount
  obtain ⟨t, V, ht, hrun, hV, htail, hstatus, hquery, htruth⟩ :=
    next_row_single_program_split (rows 0) B rest tail
      saved output count r L hn hrest hsourceB
      (hcapB.trans hcap) hscratch hcursor hvertex hindex
      hsavedB houtputB hcountB hword hcapL hB hrestLen hL hHG
  refine ⟨t, V, ht, ?_, hV, htail, hstatus, hquery, htruth⟩
  simpa only [B, SourceCSPNextRowBridge.callbackBank] using hrun

end EthInapproximability.CurrentPaper.SourceGenericNextRowSplit
