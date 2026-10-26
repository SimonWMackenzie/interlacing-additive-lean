import EthInapproximability.CurrentPaper.SourceGenericRowPairCost
import EthInapproximability.CurrentPaper.SourceGenericAllRowLoop

/-! A uniform quartic clock on the actual physical next-row/all-slot pair. -/

namespace EthInapproximability.CurrentPaper.SourceGenericRowPairQuartic

open Turing BitMachineEncoding BitMachineStackEmbedding
open SourceGenericAllRowLoop
open SourceGenericRowBridge (rowPairProgram)
open SourceGenericNextParserGrowth SourceGenericNextRowFrameGrowth
open SourceGenericRowPairSplit SourceGenericRowPairCost
open scoped Classical

theorem row_pair_run_quartic {n M a q k H G : ℕ}
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
    let tail := SourceCSPCodec.fnFields SourceCSPCodec.rowFields
      (fun j : Fin k => remaining j.succ)
    let B := SourceCSPNextRowBridge.callbackBank S row n rCurrent
      saved output count
    let P := (SourceCSPCodec.fromRows n M a q rows).system
    let clauses := (List.ofFn fun z : Fin (a ^ q) => SourceGenericOrder.rowChain P hq rNext z).flatten
    let C := SourceClauseGenericAllSlots.allCircuit (a := a) hq
    ∃ (t : ℕ) (V : SourceCSPRowQueryFrame.Stack q → List Bool),
      t ≤ pairCoefficient a q * (G + 1) ^ 4 ∧
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
  let B := SourceCSPNextRowBridge.callbackBank S row n rCurrent
    saved output count
  obtain ⟨t, V, ht, hrun, hV, htail, hquery, htruth⟩ :=
    SourceGenericRowPairSplit.row_pair_run_split rows remaining rNext rCurrent L S row
      saved output count hq hn hindex hhead hsource hcap hword hcapL
      hS hrow hnH hrH hsaved houtput hcount hrestLen hL hHG
  have hB : ∀ x, (B x).length ≤ G :=
    callbackBank_words_le S row n rCurrent saved output count
      hS hrow hnH hrH hsaved houtput hcount
  have hrNext : rNext.val ≤ G + 1 := by omega
  have hcost := pair_cost_le_quartic rows rNext B rest L V
    saved output count hB hnH hrNext hrestLen hL hHG
    hV hsaved houtput hcount
  refine ⟨t, V, ht.trans hcost, hrun, hV, htail, hquery, htruth⟩

end EthInapproximability.CurrentPaper.SourceGenericRowPairQuartic
