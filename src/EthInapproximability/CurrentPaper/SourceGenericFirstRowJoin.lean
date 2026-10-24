import EthInapproximability.CurrentPaper.SourceGenericAllRowClock

namespace EthInapproximability.CurrentPaper.SourceGenericFirstRowJoin

open Turing BitMachineEncoding BitMachineStackEmbedding
open scoped Classical

noncomputable def callbackProgram {a q : Nat} (hq : 0 < q) :=
  let C := SourceClauseGenericAllSlots.allCircuit (a := a) hq
  BitMachineRawSequence.program
    (SourceCSPFirstSlotBridge.cleanupProgram (q := q))
    (SourceGenericRowBridge.slotProgram (a := a) hq)
    C.start ((), none) C.initial

/-- The actual staged first-row bank, with whatever prefix words the prior
physical producer placed in its writer cells, runs cleanup and the generic
all-tuple callback. No prefix bytes or row result are supplied to the code. -/
theorem first_callback_exact {n m a q : Nat}
    (hq : 0 < q) (hm : 0 < m)
    (rows : Fin m → SourceCSPCodec.Row n a q)
    (U : SourceCSPFirstRowController.Stack q → List Bool)
    (htruth : SourceCSPFirstSlotBridge.row U (.inr 2) =
      true :: List.ofFn (rows ⟨0, hm⟩).2)
    (hquery : ∀ j : Fin q,
      SourceCSPFirstSlotBridge.row U (.inl (j, 1)) =
        List.replicate ((rows ⟨0, hm⟩).1 j).val true)
    (hn : SourceCSPFirstSlotBridge.writer U
      SourceClauseRowWriterOperands.vertex = List.replicate n true)
    (hr : SourceCSPFirstSlotBridge.writer U
      SourceClauseRowWriterOperands.rowIndex = []) :
    let row := SourceCSPFirstSlotBridge.row U
    let saved := SourceCSPFirstSlotBridge.writer U
      SourceClauseRowWriterCleanup.savedCell
    let output := SourceCSPFirstSlotBridge.writer U
      SourceClauseRowWriterCleanup.outputCell
    let count := SourceCSPFirstSlotBridge.writer U
      SourceClauseRowWriterCleanup.countCell
    let clauses := SourceGenericAllRowLoop.rowClauses rows hq ⟨0, hm⟩
    let C := SourceClauseGenericAllSlots.allCircuit (a := a) hq
    ∃ t ≤ SourceCSPFirstSlotBridge.cleanupTime U +
      SourceClauseGenericAllSlotPolynomial.allCoefficient a q *
        (SourceClauseGenericRow.inputBits row n 0 saved output count + 1)^2 + 1,
      ((advance (callbackProgram (a := a) hq))^[t])
        (⟨some (BitMachineRawSequence.leftLabel (.clear 0)),
          (((), none), C.initial), SourceCSPFirstSlotBridge.extended U⟩ :
          TM2.Cfg (fun _ : SourceCSPFirstSlotBridge.Stack q => Bool) _ _) =
        ⟨none, (((), none), C.initial),
          SourceCSPNextRowBridge.callbackBank
            (fun g => U (.inl g)) row n 0
            ((EncodedCNF.clauseFields clauses).reverse ++ saved)
            output (List.replicate clauses.length true ++ count)⟩ := by
  let row := SourceCSPFirstSlotBridge.row U
  let saved := SourceCSPFirstSlotBridge.writer U
    SourceClauseRowWriterCleanup.savedCell
  let output := SourceCSPFirstSlotBridge.writer U
    SourceClauseRowWriterCleanup.outputCell
  let count := SourceCSPFirstSlotBridge.writer U
    SourceClauseRowWriterCleanup.countCell
  let clauses := SourceGenericAllRowLoop.rowClauses rows hq ⟨0, hm⟩
  let C := SourceClauseGenericAllSlots.allCircuit (a := a) hq
  let S := fun g => U (.inl g)
  let B := SourceCSPNextRowBridge.callbackBank S row n 0 saved output count
  let T := SourceCSPNextRowBridge.callbackBank S row n 0
    ((EncodedCNF.clauseFields clauses).reverse ++ saved)
    output (List.replicate clauses.length true ++ count)
  have hfirst :
      ((advance (SourceCSPFirstSlotBridge.cleanupProgram (q := q)))^[
        SourceCSPFirstSlotBridge.cleanupTime U])
        (⟨some (.clear 0), ((), none), SourceCSPFirstSlotBridge.extended U⟩) =
      ⟨none, ((), none), B⟩ := by
    simpa only [B, S, row, saved, output, count,
      SourceCSPNextRowBridge.callbackBank] using
      SourceCSPFirstSlotBridge.cleanup_to_callback_initial U n 0
        saved output count rfl rfl rfl hn (by simpa using hr)
  obtain ⟨ts, hts, hslot⟩ :=
    SourceGenericRowBridge.all_slots_from_typed_row
      rows ⟨0, hm⟩ hq S row hquery htruth saved output count
  have hslot' :
      ((advance (SourceGenericRowBridge.slotProgram (a := a) hq))^[ts])
        (⟨some C.start, C.initial, B⟩) =
      ⟨none, C.initial, T⟩ := by
    simpa only [B, T, C, S, row, clauses] using hslot
  obtain ⟨t, ht, hrun⟩ := BitMachineRawSequence.runs
    (SourceCSPFirstSlotBridge.cleanupProgram (q := q))
    (SourceGenericRowBridge.slotProgram (a := a) hq)
    (.clear 0) C.start ((), none) ((), none)
    C.initial C.initial (SourceCSPFirstSlotBridge.extended U)
    B T (SourceCSPFirstSlotBridge.cleanupTime U) ts hfirst hslot'
  refine ⟨t, ?_, ?_⟩
  · change t ≤ SourceCSPFirstSlotBridge.cleanupTime U +
        SourceClauseGenericAllSlotPolynomial.allCoefficient a q *
          (SourceClauseGenericRow.inputBits row n 0
            saved output count + 1)^2 + 1
    have hts' : ts ≤
        SourceClauseGenericAllSlotPolynomial.allCoefficient a q *
          (SourceClauseGenericRow.inputBits row n 0
            saved output count + 1)^2 := by
      simpa only [Fin.val_zero] using hts
    omega
  · simpa only [callbackProgram, C, T, B, S, row, saved, output,
      count, clauses] using hrun

#print axioms first_callback_exact

end EthInapproximability.CurrentPaper.SourceGenericFirstRowJoin
