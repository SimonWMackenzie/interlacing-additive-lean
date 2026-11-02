import EthInapproximability.CurrentPaper.SourceGenericRowClearSuffix

namespace EthInapproximability.CurrentPaper.SourceGenericFirstRowSuffix

open Turing BitMachineEncoding
open scoped Classical

noncomputable def callbackClearProgram {a q : Nat} (hq : 0 < q) :=
  let C := SourceClauseGenericAllSlots.allCircuit (a := a) hq
  BitMachineRawSequence.program
    (SourceGenericFirstRowJoin.callbackProgram (a := a) hq)
    (SourceCSPEntryBound.clearLoopProgram q)
    0 (((), none), C.initial) ((), none)

noncomputable def callbackClearSuffixProgram {a q : Nat} (hq : 0 < q) :=
  let C := SourceClauseGenericAllSlots.allCircuit (a := a) hq
  BitMachineRawSequence.program
    (callbackClearProgram (a := a) hq)
    (SourceGenericAllRowLoop.program (a := a) hq)
    (.copy .scan)
    ((((), none), C.initial), ((), none))
    (.copy none)

/-- A single fixed-`a,q` controller starts on the physically staged first
row, executes its actual tuple clauses, clears private validator fuel, and
then consumes all unread rows to EOF. The accumulated prefix words are read
from `U`; they are never supplied to the controller as expected output. -/
theorem first_then_remaining {n m a q H : Nat}
    (rows : Fin m → SourceCSPCodec.Row n a q)
    (hq : 0 < q) (hn : 0 < n) (hm : 0 < m)
    (U : SourceCSPFirstRowController.Stack q → List Bool)
    (htruth : SourceCSPFirstSlotBridge.row U (.inr 2) =
      true :: List.ofFn (rows ⟨0, hm⟩).2)
    (hquery : ∀ j : Fin q,
      SourceCSPFirstSlotBridge.row U (.inl (j, 1)) =
        List.replicate ((rows ⟨0, hm⟩).1 j).val true)
    (hvertex : SourceCSPFirstSlotBridge.writer U
      SourceClauseRowWriterOperands.vertex = List.replicate n true)
    (hindex : SourceCSPFirstSlotBridge.writer U
      SourceClauseRowWriterOperands.rowIndex = [])
    (L : Nat)
    (hword : ∀ i : Fin m, ∀ j : Fin q,
      ((rows i).1 j).val.bits.length ≤ L)
    (hcapL : n - 1 ≤ L)
    (hnH : n ≤ H) (hmH : m ≤ H)
    (ht : 1 + a ^ q ≤ H) (hL : L ≤ H)
    (hS : ∀ x, (U (.inl x)).length ≤ H)
    (hrow : ∀ x, (SourceCSPFirstSlotBridge.row U x).length ≤ H)
    (hsaved :
      (((EncodedCNF.clauseFields
        (SourceGenericAllRowLoop.rowClauses rows hq ⟨0, hm⟩)).reverse ++
          SourceCSPFirstSlotBridge.writer U
            SourceClauseRowWriterCleanup.savedCell)).length ≤ H)
    (houtput : (SourceCSPFirstSlotBridge.writer U
      SourceClauseRowWriterCleanup.outputCell).length ≤ H)
    (hcount :
      ((List.replicate
        (SourceGenericAllRowLoop.rowClauses rows hq ⟨0, hm⟩).length true ++
          SourceCSPFirstSlotBridge.writer U
            SourceClauseRowWriterCleanup.countCell)).length ≤ H)
    (hheader : U (.inl SourceCSPHeaderRowBridge.count) =
      List.replicate m true)
    (hcap : U (.inl SourceCSPHeaderRowBridge.capSource) =
      List.replicate (n - 1) true)
    (hsource : SourceCSPFirstSlotBridge.row U (.inr 0) =
      SourceCSPCodec.fnFields SourceCSPCodec.rowFields
        (SourceGenericAllRowLoop.remainingRows rows 0 (m - 1)
          (by omega))) :
    let C := SourceClauseGenericAllSlots.allCircuit (a := a) hq
    let S := fun g => U (.inl g)
    let row := SourceCSPFirstSlotBridge.row U
    let saved := SourceCSPFirstSlotBridge.writer U
      SourceClauseRowWriterCleanup.savedCell
    let output := SourceCSPFirstSlotBridge.writer U
      SourceClauseRowWriterCleanup.outputCell
    let count := SourceCSPFirstSlotBridge.writer U
      SourceClauseRowWriterCleanup.countCell
    let first := SourceGenericAllRowLoop.rowClauses rows hq ⟨0, hm⟩
    let rest := SourceGenericAllRowLoop.suffixClauses rows hq 0
      (m - 1) (by omega)
    ∃ (t : Nat) (lastRow : SourceCSPRowQueryFrame.Stack q → List Bool),
      t ≤ SourceCSPFirstSlotBridge.cleanupTime U +
        SourceClauseGenericAllSlotPolynomial.allCoefficient a q *
          (SourceClauseGenericRow.inputBits row n 0 saved output count + 1)^2 +
        H + 3 + SourceGenericAllRowLoopClock.loopCoefficient a q * (H + 1)^9 + 2 ∧
      ((advance (callbackClearSuffixProgram (a := a) hq))^[t])
        (⟨some (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel (.clear 0)))),
          (((((), none), C.initial), ((), none)), .copy none),
          SourceCSPFirstSlotBridge.extended U⟩ :
          TM2.Cfg (fun _ : SourceGenericAllRowLoop.Stack q => Bool) _ _) =
        ⟨none, (((((), none), C.initial), ((), none)), .done true),
          SourceCSPNextRowBridge.callbackBank
            (SourceGenericAllRowLoop.withRemaining
              (Function.update S SourceCSPHeaderRowBridge.loopCount []) 0)
            lastRow n (m - 1)
            ((EncodedCNF.clauseFields rest).reverse ++
              (EncodedCNF.clauseFields first).reverse ++ saved)
            output
            (List.replicate rest.length true ++
              List.replicate first.length true ++ count)⟩ ∧
      lastRow (.inr 0) = [] := by
  let C := SourceClauseGenericAllSlots.allCircuit (a := a) hq
  let S := fun g => U (.inl g)
  let row := SourceCSPFirstSlotBridge.row U
  let saved := SourceCSPFirstSlotBridge.writer U
    SourceClauseRowWriterCleanup.savedCell
  let output := SourceCSPFirstSlotBridge.writer U
    SourceClauseRowWriterCleanup.outputCell
  let count := SourceCSPFirstSlotBridge.writer U
    SourceClauseRowWriterCleanup.countCell
  let first := SourceGenericAllRowLoop.rowClauses rows hq ⟨0, hm⟩
  let rest := SourceGenericAllRowLoop.suffixClauses rows hq 0
    (m - 1) (by omega)
  let saved1 := (EncodedCNF.clauseFields first).reverse ++ saved
  let count1 := List.replicate first.length true ++ count
  let S' := Function.update S SourceCSPHeaderRowBridge.loopCount []
  let B1 := SourceCSPNextRowBridge.callbackBank S row n 0
    saved1 output count1
  let B2 := SourceCSPNextRowBridge.callbackBank S' row n 0
    saved1 output count1
  let B3 := SourceCSPNextRowBridge.callbackBank
    (SourceGenericAllRowLoop.withRemaining S' 0)
    (fun _ => []) n (m - 1)
    ((EncodedCNF.clauseFields rest).reverse ++ saved1)
    output (List.replicate rest.length true ++ count1)
  obtain ⟨tc, htc, hcb⟩ :=
    SourceGenericFirstRowJoin.first_callback_exact
      hq hm rows U htruth hquery hvertex hindex
  have hcb' :
      ((advance (SourceGenericFirstRowJoin.callbackProgram (a := a) hq))^[tc])
        (⟨some (BitMachineRawSequence.leftLabel (.clear 0)),
          (((), none), C.initial), SourceCSPFirstSlotBridge.extended U⟩) =
        ⟨none, (((), none), C.initial), B1⟩ := by
    simpa only [C, S, row, saved, output, count, first, saved1,
      count1, B1] using hcb
  have hsourceLen : (row (.inr 0)).length ≤ H := hrow _
  obtain ⟨tz, tl, lastRow, htz, htl, hclear, hloop, hlast⟩ :=
    SourceGenericRowClearSuffix.remaining_after_first_with_clear
      rows hq L hn hm hword hcapL hnH hmH ht hL
      S row saved1 output count1 hS hrow hsaved houtput hcount
      hheader hcap hsource hsourceLen
  have hclear' :
      ((advance (SourceCSPEntryBound.clearLoopProgram q))^[tz])
        (⟨some 0, ((), none), B1⟩) =
        ⟨none, ((), none), B2⟩ := by
    simpa only [B1, B2, S', saved1, count1] using hclear
  have hloop' :
      ((advance (SourceGenericAllRowLoop.program (a := a) hq))^[tl])
        (⟨some (.copy .scan), .copy none, B2⟩) =
        ⟨none, .done true,
          SourceCSPNextRowBridge.callbackBank
            (SourceGenericAllRowLoop.withRemaining S' 0)
            lastRow n (m - 1)
            ((EncodedCNF.clauseFields rest).reverse ++ saved1)
            output (List.replicate rest.length true ++ count1)⟩ := by
    simpa only [B2, S', rest, saved1, count1] using hloop
  obtain ⟨t1, ht1, hphase1⟩ := BitMachineRawSequence.runs
    (SourceGenericFirstRowJoin.callbackProgram (a := a) hq)
    (SourceCSPEntryBound.clearLoopProgram q)
    (BitMachineRawSequence.leftLabel (.clear 0)) 0
    (((), none), C.initial) (((), none), C.initial)
    ((), none) ((), none)
    (SourceCSPFirstSlotBridge.extended U) B1 B2
    tc tz hcb' hclear'
  obtain ⟨t, htt, hrun⟩ := BitMachineRawSequence.runs
    (callbackClearProgram (a := a) hq)
    (SourceGenericAllRowLoop.program (a := a) hq)
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel (.clear 0)))
    (.copy .scan)
    ((((), none), C.initial), ((), none))
    ((((), none), C.initial), ((), none))
    (.copy none) (.done true)
    (SourceCSPFirstSlotBridge.extended U) B2
    (SourceCSPNextRowBridge.callbackBank
      (SourceGenericAllRowLoop.withRemaining S' 0)
      lastRow n (m - 1)
      ((EncodedCNF.clauseFields rest).reverse ++ saved1)
      output (List.replicate rest.length true ++ count1))
    t1 tl (by simpa only [callbackClearProgram, C] using hphase1) hloop'
  refine ⟨t, lastRow, ?_, ?_, hlast⟩
  · have htcall : tc ≤ SourceCSPFirstSlotBridge.cleanupTime U +
        SourceClauseGenericAllSlotPolynomial.allCoefficient a q *
          (SourceClauseGenericRow.inputBits row n 0 saved output count + 1)^2 + 1 := by
      simpa only [row, saved, output, count] using htc
    omega
  · simpa only [callbackClearSuffixProgram, C, S, row, saved, output,
      count, first, rest, saved1, count1, S', List.append_assoc] using hrun

#print axioms first_then_remaining

end EthInapproximability.CurrentPaper.SourceGenericFirstRowSuffix
