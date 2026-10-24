import EthInapproximability.CurrentPaper.SourceGenericRowBridge
import EthInapproximability.CurrentPaper.SourceGenericNextRowSplit

/-! Same-witness clocked next-row plus all-slot pair on the frozen loop program. -/

namespace EthInapproximability.CurrentPaper.SourceGenericRowPairSplit

open Turing BitMachineEncoding BitMachineStackEmbedding
open SourceGenericRowBridge
open SourceGenericNextParserGrowth SourceGenericNextRowFrameGrowth
open SourceGenericNextRowSplit
open scoped Classical

theorem row_pair_run_split {n M a q k H G : ℕ}
    (rows : Fin M → SourceCSPCodec.Row n a q)
    (remaining : Fin (k + 1) → SourceCSPCodec.Row n a q)
    (rNext : Fin M) (rCurrent L : ℕ)
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
    (hcapL : n - 1 ≤ L)
    (hS : ∀ x, (S x).length ≤ G)
    (hrow : ∀ x, (row x).length ≤ G)
    (hnH : n ≤ G) (hrH : rCurrent ≤ G)
    (hsaved : saved.length ≤ G)
    (houtput : output.length ≤ G)
    (hcount : count.length ≤ G)
    (hrestLen :
      (SourceCSPCodec.fnFields SourceCSPCodec.rowFields remaining).length ≤ H)
    (hL : L ≤ H) (hHG : H ≤ G) :
    let rest := SourceCSPCodec.fnFields SourceCSPCodec.rowFields remaining
    let tail := SourceCSPCodec.fnFields SourceCSPCodec.rowFields
      (fun j : Fin k => remaining j.succ)
    let B := SourceCSPNextRowBridge.callbackBank S row n rCurrent
      saved output count
    let P := (SourceCSPCodec.fromRows n M a q rows).system
    let clauses := (List.ofFn fun z : Fin (a ^ q) => SourceGenericOrder.rowChain P hq rNext z).flatten
    let C := SourceClauseGenericAllSlots.allCircuit (a := a) hq
    ∃ (t : ℕ) (V : SourceCSPRowQueryFrame.Stack q → List Bool),
      t ≤ SourceCSPNextRowBridge.resetCost B
          (List.replicate (n - 1) true) +
        parseBudget a q rest L + 2 +
        cleanupCoefficient a q * (G + 1) ^ 2 + 3 +
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
      (∀ x, (V x).length ≤ parseWordCoefficient a q * (H + 1) ^ 2) ∧
      V (.inr 0) = tail ∧
      (∀ j : Fin q, V (.inl (j, 1)) =
        List.replicate ((rows rNext).1 j).val true) ∧
      V (.inr 2) = true :: List.ofFn (rows rNext).2 := by
  let rest := SourceCSPCodec.fnFields SourceCSPCodec.rowFields remaining
  let tail := SourceCSPCodec.fnFields SourceCSPCodec.rowFields
    (fun j : Fin k => remaining j.succ)
  let B := SourceCSPNextRowBridge.callbackBank S row n rCurrent
    saved output count
  let P := (SourceCSPCodec.fromRows n M a q rows).system
  let clauses := (List.ofFn fun z : Fin (a ^ q) => SourceGenericOrder.rowChain P hq rNext z).flatten
  let C := SourceClauseGenericAllSlots.allCircuit (a := a) hq
  obtain ⟨tn, V, htn, hnext, hV, htail, _, hquery,
    htruth⟩ := SourceGenericNextRowSplit.next_row_after_callback_split
      remaining S row saved output count rCurrent L hn hsource hcap
      hword hcapL hS hrow hnH hrH hsaved houtput hcount hrestLen hL hHG
  have hquery' : ∀ j : Fin q,
      V (.inl (j, 1)) = List.replicate ((rows rNext).1 j).val true := by
    intro j
    rw [hhead]
    exact hquery j
  have htruth' : V (.inr 2) = true :: List.ofFn (rows rNext).2 := by
    rw [hhead]
    exact htruth
  obtain ⟨ts, hts, hslot⟩ := SourceGenericRowBridge.all_slots_from_typed_row
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
    (SourceCSPNextRowBridge.nextProgram q a) (slotProgram (a := a) hq)
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
  refine ⟨t, V, ?_, ?_, hV, htail, hquery', htruth'⟩
  · omega
  · simpa only [rowPairProgram, C, P, clauses] using hrun

end EthInapproximability.CurrentPaper.SourceGenericRowPairSplit
