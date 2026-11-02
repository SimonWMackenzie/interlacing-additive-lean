import EthInapproximability.CurrentPaper.SourceCSPAllRowLoop
import EthInapproximability.CurrentPaper.SourceCSPNextRowSplitEnvelope

/-! Same-witness clocked next-row plus all-slot pair on the frozen loop program. -/

namespace EthInapproximability.CurrentPaper.SourceCSPRowPairSplitProduction

open Turing BitMachineEncoding BitMachineStackEmbedding
open SourceCSPAllRowLoop
open SourceCSPNextParserGrowth SourceCSPNextRowFrameGrowth
open SourceCSPNextRowSplitProduction
open scoped Classical

theorem row_pair_run_split {n M q k H G : ℕ}
    (rows : Fin M → SourceCSPCodec.Row n 2 q)
    (remaining : Fin (k + 1) → SourceCSPCodec.Row n 2 q)
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
    let P := (SourceCSPCodec.fromRows n M 2 q rows).system
    let clauses := SourceClauseCallback.AllSlots.actualListClauses P hq rNext
      (List.ofFn (fun z : Fin (2 ^ q) => z))
    let C := SourceClauseCallback.AllSlots.allCircuit hq
    ∃ (t : ℕ) (V : SourceCSPRowQueryFrame.Stack q → List Bool),
      t ≤ SourceCSPNextRowBridge.resetCost B
          (List.replicate (n - 1) true) +
        parseBudget q rest L + 2 +
        cleanupCoefficient q * (G + 1) ^ 2 + 3 +
        SourceClauseCallback.AllSlotsClock.allCost hq V n rNext.val
          (rows rNext).2 saved output count + 1 ∧
      ((advance (rowPairProgram hq))^[t])
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
      (∀ x, (V x).length ≤ parseWordCoefficient q * (H + 1) ^ 2) ∧
      V (.inr 0) = tail ∧
      (∀ j : Fin q, V (.inl (j, 1)) =
        List.replicate ((rows rNext).1 j).val true) ∧
      V (.inr 2) = true :: List.ofFn (rows rNext).2 := by
  let rest := SourceCSPCodec.fnFields SourceCSPCodec.rowFields remaining
  let tail := SourceCSPCodec.fnFields SourceCSPCodec.rowFields
    (fun j : Fin k => remaining j.succ)
  let B := SourceCSPNextRowBridge.callbackBank S row n rCurrent
    saved output count
  let P := (SourceCSPCodec.fromRows n M 2 q rows).system
  let clauses := SourceClauseCallback.AllSlots.actualListClauses P hq rNext
    (List.ofFn (fun z : Fin (2 ^ q) => z))
  let C := SourceClauseCallback.AllSlots.allCircuit hq
  obtain ⟨tn, V, htn, hnext, hV, htail, _, hquery,
    htruth⟩ := next_row_after_callback_split
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
  obtain ⟨ts, hts, hslot⟩ := all_slots_from_typed_row
    rows rNext hq S V hquery' htruth' saved output count
  have hnext' : ((advance (SourceCSPNextRowBridge.nextProgram q 2))^[tn])
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
    (SourceCSPNextRowBridge.nextProgram q 2) (slotProgram hq)
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

end EthInapproximability.CurrentPaper.SourceCSPRowPairSplitProduction
