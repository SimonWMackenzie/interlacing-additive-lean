import EthInapproximability.CurrentPaper.SourceClauseLabelBridge

/-! Connect the physical selected-slot terminal bank to the exact indexed
block of the existing ordered Boolean-CSP-to-3CNF translation. -/

namespace EthInapproximability.CurrentPaper.SourceClauseCallback.SourceLabelBridge

open SourceBooleanEncoding SourceClauseEncoding SourceClauseRowSchedule
open SourceClauseCallback.DualDispatch

theorem finalBank_actual {n m q : ℕ}
    (P : CSP n m 2 q) (hq : 0 < q)
    (r : Fin m) (k : Fin (2 ^ q))
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (table : Fin (2 ^ q) → Bool)
    (saved output count remaining : List Bool)
    (hquery : ∀ j : Fin q,
      SourceClauseCallback.rowQuery row j = (P.query r j).val)
    (haccept : table k = P.accept r (tuple 2 q k)) :
    finalBank hq row n r.val k saved output count remaining (table k) =
      BitMachineStackEmbedding.bank SourceClauseRowWriterTruthFrame.writerEmbedding
        (SourceClauseRowWriterTruthFlagFrame.afterFlag row n r.val
          saved output count (table k) remaining)
        (SourceClauseRowWriterBlank.bank row n r.val
          ((EncodedCNF.clauseFields
            (actualTranslateBlock P hq r k)).reverse ++ saved)
          output
          (List.replicate (clauseCount q (table k)) true ++ count)) := by
  simp only [finalBank]
  rw [selected_payload_actual_block P hq r k row table saved hquery haccept]

end EthInapproximability.CurrentPaper.SourceClauseCallback.SourceLabelBridge
