import EthInapproximability.CurrentPaper.SourceClauseGenericRowExact
import EthInapproximability.CurrentPaper.SourceCSPNextRowBridge

namespace EthInapproximability.CurrentPaper.SourceGenericRowBridge

open Turing BitMachineEncoding BitMachineStackEmbedding
open SourceBooleanEncoding SourceClauseRowSchedule SourceClauseCallback
open scoped Classical

abbrev Stack (q : Nat) := SourceCSPNextRowBridge.Stack q

noncomputable def slotProgram {a q : Nat} (hq : 0 < q) :=
  fun l => stackStmt (SourceCSPFirstSlotBridge.truthEmbedding (q := q))
    ((SourceClauseGenericAllSlots.allCircuit (a := a) hq).program l)

/-- The generic physical all-slot circuit runs on the actual parsed row bank
embedded in the global-plus-writer stack, preserving the header/parser bank. -/
theorem all_slots_from_typed_row {n m a q : Nat}
    (rows : Fin m → SourceCSPCodec.Row n a q) (r : Fin m)
    (hq : 0 < q)
    (S : SourceCSPGlobalDecisionProgram.Stack q → List Bool)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (hquery : ∀ j : Fin q,
      row (.inl (j, 1)) = List.replicate ((rows r).1 j).val true)
    (htruth : row (.inr 2) = true :: List.ofFn (rows r).2)
    (saved output count : List Bool) :
    let P := (SourceCSPCodec.fromRows n m a q rows).system
    let C := SourceClauseGenericAllSlots.allCircuit (a := a) hq
    let clauses := (List.ofFn fun k : Fin (a ^ q) =>
      SourceGenericOrder.rowChain P hq r k).flatten
    ∃ t ≤ SourceClauseGenericAllSlotPolynomial.allCoefficient a q *
        (SourceClauseGenericRow.inputBits row n r.val saved output count + 1)^2,
      ((advance (slotProgram (a := a) hq))^[t])
        (⟨some C.start, C.initial,
          SourceCSPNextRowBridge.callbackBank S row n r.val
            saved output count⟩ :
          TM2.Cfg (fun _ : Stack q => Bool) C.Label C.Control) =
        ⟨none, C.initial,
          SourceCSPNextRowBridge.callbackBank S row n r.val
            ((EncodedCNF.clauseFields clauses).reverse ++ saved)
            output (List.replicate clauses.length true ++ count)⟩ := by
  let P := (SourceCSPCodec.fromRows n m a q rows).system
  let C := SourceClauseGenericAllSlots.allCircuit (a := a) hq
  let clauses := (List.ofFn fun k : Fin (a ^ q) =>
    SourceGenericOrder.rowChain P hq r k).flatten
  have hu : ∀ j : Fin q, row (.inl (j, 1)) =
      List.replicate (row (.inl (j, 1))).length true := by
    intro j
    rw [hquery j]
    simp
  have hqP : ∀ j : Fin q, rowQuery row j = (P.query r j).val := by
    intro j
    simp [SourceClauseCallback.rowQuery, P,
      SourceCSPCodec.fromRows, hquery j]
  have haP : ∀ k : Fin (a ^ q),
      (rows r).2 k = P.accept r (tuple a q k) := by
    intro k
    simp [P, SourceCSPCodec.fromRows, tuple]
  obtain ⟨t, ht, hrun⟩ :=
    SourceClauseGenericRowExact.row_bounded_exact P hq r row
      (rows r).2 htruth hu hqP haP saved output count
  let B := SourceCSPNextRowBridge.callbackBank S row n r.val
    saved output count
  let T := SourceClauseRowWriterTruthFrame.initial row n r.val
    ((EncodedCNF.clauseFields clauses).reverse ++ saved)
    output (List.replicate clauses.length true ++ count)
  have hbank : bank SourceCSPFirstSlotBridge.truthEmbedding B
      (SourceClauseRowWriterTruthFrame.initial row n r.val
        saved output count) = B := by
    apply bank_eq_self
    intro x
    rfl
  have he := BitMachineStackRun.run
    (SourceCSPFirstSlotBridge.truthEmbedding (q := q)) B C.program
    (⟨some C.start, C.initial,
      SourceClauseRowWriterTruthFrame.initial row n r.val
        saved output count⟩) t
  change ((advance C.program)^[t])
      (⟨some C.start, C.initial,
        SourceClauseRowWriterTruthFrame.initial row n r.val
          saved output count⟩) =
      ⟨none, C.initial, T⟩ at hrun
  rw [hrun] at he
  have hterminal : bank SourceCSPFirstSlotBridge.truthEmbedding B T =
      SourceCSPNextRowBridge.callbackBank S row n r.val
        ((EncodedCNF.clauseFields clauses).reverse ++ saved)
        output (List.replicate clauses.length true ++ count) := by
    funext x
    cases x with
    | inl g =>
        rw [bank_outside]
        · rfl
        · rintro ⟨y, hy⟩
          cases hy
    | inr y =>
        change bank SourceCSPFirstSlotBridge.truthEmbedding B T
          (SourceCSPFirstSlotBridge.truthEmbedding y) = _
        rw [bank_at]
        rfl
  refine ⟨t, ht, ?_⟩
  simpa only [slotProgram, stackCfg, hbank, hterminal,
    B, C, clauses, T] using he

#print axioms all_slots_from_typed_row

noncomputable def rowPairProgram {a q : Nat} (hq : 0 < q) :=
  let C := SourceClauseGenericAllSlots.allCircuit (a := a) hq
  BitMachineRawSequence.program (SourceCSPNextRowBridge.nextProgram q a)
    (slotProgram (a := a) hq) C.start
    (((((), none), none), SourceCSPNextRowBridge.parseControlStart),
      ((), ((), none))) C.initial

/-- One actual next-row parser/reset followed by the complete generic tuple
callback; its source row is read from the retained unread suffix. -/
theorem row_pair_run {n M a q k : Nat}
    (rows : Fin M → SourceCSPCodec.Row n a q)
    (remaining : Fin (k + 1) → SourceCSPCodec.Row n a q)
    (rNext : Fin M) (rCurrent L : Nat)
    (S : SourceCSPGlobalDecisionProgram.Stack q → List Bool)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (saved output count : List Bool)
    (hq : 0 < q) (hn : 0 < n)
    (hindex : rNext.val = rCurrent + 1)
    (hhead : rows rNext = remaining 0)
    (hsource : row (.inr 0) =
      SourceCSPCodec.fnFields SourceCSPCodec.rowFields remaining)
    (hcap : S SourceCSPHeaderRowBridge.capSource =
      List.replicate (n - 1) true)
    (hword : ∀ j : Fin q, ((remaining 0).1 j).val.bits.length ≤ L)
    (hcapL : n - 1 ≤ L) :
    let rest := SourceCSPCodec.fnFields SourceCSPCodec.rowFields remaining
    let tail := SourceCSPCodec.fnFields SourceCSPCodec.rowFields
      (fun j : Fin k => remaining j.succ)
    let B := SourceCSPNextRowBridge.callbackBank S row n rCurrent
      saved output count
    let P := (SourceCSPCodec.fromRows n M a q rows).system
    let clauses := (List.ofFn fun z : Fin (a ^ q) =>
      SourceGenericOrder.rowChain P hq rNext z).flatten
    let C := SourceClauseGenericAllSlots.allCircuit (a := a) hq
    ∃ (t : Nat) (V : SourceCSPRowQueryFrame.Stack q → List Bool),
      t ≤ SourceCSPNextRowBridge.resetCost B
          (List.replicate (n - 1) true) +
        (q * (2 * (SourceCSPCodec.rowFields (remaining 0) ++ tail).length + 4) +
          2 * a ^ q + 3 + q * (100 * (L + 1) ^ 2) + 2) +
        2 + SourceCSPNextRowBridge.callbackCleanupTime
          (SourceCSPNextRowBridge.steppedResult B rest
            (List.replicate (n - 1) true) V) + 3 +
        SourceClauseGenericAllSlotPolynomial.allCoefficient a q *
          (SourceClauseGenericRow.inputBits V n rNext.val saved output count + 1)^2 + 1 ∧
      ((advance (rowPairProgram (a := a) hq))^[t])
        (⟨some (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel
              (BitMachineRawSequence.leftLabel
                (BitMachineRawSequence.leftLabel 0)))),
          ((((((), none), none),
              SourceCSPNextRowBridge.parseControlStart),
              ((), ((), none))), C.initial), B⟩ :
          TM2.Cfg (fun _ : Stack q => Bool) _ _) =
        ⟨none, ((((((), none), none),
            SourceCSPNextRowBridge.parseControlStart),
            ((), ((), none))), C.initial),
          SourceCSPNextRowBridge.callbackBank S V n rNext.val
            ((EncodedCNF.clauseFields clauses).reverse ++ saved)
            output (List.replicate clauses.length true ++ count)⟩ ∧
      V (.inr 0) = tail := by
  let rest := SourceCSPCodec.fnFields SourceCSPCodec.rowFields remaining
  let tail := SourceCSPCodec.fnFields SourceCSPCodec.rowFields
    (fun j : Fin k => remaining j.succ)
  let B := SourceCSPNextRowBridge.callbackBank S row n rCurrent
    saved output count
  let P := (SourceCSPCodec.fromRows n M a q rows).system
  let clauses := (List.ofFn fun z : Fin (a ^ q) =>
    SourceGenericOrder.rowChain P hq rNext z).flatten
  let C := SourceClauseGenericAllSlots.allCircuit (a := a) hq
  obtain ⟨tn, V, htn, hnext, htail, _, hquery, htruth⟩ :=
    SourceCSPNextRowBridge.next_row_after_callback
      remaining S row saved output count rCurrent L hn hsource hcap
      hword hcapL
  have hquery' : ∀ j : Fin q,
      V (.inl (j, 1)) = List.replicate ((rows rNext).1 j).val true := by
    intro j
    rw [hhead]
    exact hquery j
  have htruth' : V (.inr 2) = true :: List.ofFn (rows rNext).2 := by
    rw [hhead]
    exact htruth
  obtain ⟨ts, hts, hslot⟩ := all_slots_from_typed_row
    rows rNext hq S V hquery' htruth' saved output count
  have hnext' : ((advance (SourceCSPNextRowBridge.nextProgram q a))^[tn])
      (⟨some (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel 0))),
        (((((), none), none), SourceCSPNextRowBridge.parseControlStart),
          ((), ((), none))), B⟩) =
      ⟨none,
        (((((), none), none), SourceCSPNextRowBridge.parseControlStart),
          ((), ((), none))),
        SourceCSPNextRowBridge.callbackBank S V n rNext.val
          saved output count⟩ := by
    simpa only [hindex] using hnext
  obtain ⟨t, ht, hrun⟩ := BitMachineRawSequence.runs
    (SourceCSPNextRowBridge.nextProgram q a)
    (slotProgram (a := a) hq)
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel 0)))
    C.start
    (((((), none), none), SourceCSPNextRowBridge.parseControlStart),
      ((), ((), none)))
    (((((), none), none), SourceCSPNextRowBridge.parseControlStart),
      ((), ((), none)))
    C.initial C.initial B
    (SourceCSPNextRowBridge.callbackBank S V n rNext.val
      saved output count)
    (SourceCSPNextRowBridge.callbackBank S V n rNext.val
      ((EncodedCNF.clauseFields clauses).reverse ++ saved)
      output (List.replicate clauses.length true ++ count))
    tn ts hnext' hslot
  refine ⟨t, V, ?_, ?_, htail⟩
  · omega
  · simpa only [rowPairProgram, C, P, clauses] using hrun

#print axioms row_pair_run

end EthInapproximability.CurrentPaper.SourceGenericRowBridge
