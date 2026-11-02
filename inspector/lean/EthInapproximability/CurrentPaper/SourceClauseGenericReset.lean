import EthInapproximability.CurrentPaper.SourceClauseGenericDual
import EthInapproximability.CurrentPaper.SourceClauseTruthReset

namespace EthInapproximability.CurrentPaper.SourceClauseGenericReset

open SourceClauseCallback.TruthReset
open SourceClauseCallback
open Turing BitMachineEncoding
open scoped Classical

theorem cleared_finalBank {a q : ℕ} (hq : 0 < q)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r : ℕ) (k : Fin (a ^ q))
    (saved output count remaining : List Bool) (b : Bool) :
    cleared (SourceClauseGenericDual.finalBank hq row n r k
      saved output count remaining b) =
      SourceClauseRowWriterTruthFrame.initial row n r
        ((EncodedCNF.clauseFields
          (SourceClauseEncoding.chain (SourceClauseGenericCallback.base n r k)
            (SourceClauseRowSchedule.tupleClause hq k
              (SourceClauseCallback.rowQuery row) b))).reverse ++ saved)
        output
        (List.replicate (SourceClauseGenericDual.clauseCount q b)
          true ++ count) := by
  funext x
  cases x with
  | inl x =>
      simp [cleared, BitMachineClearBank.cleared,
        SourceClauseGenericDual.finalBank,
        SourceClauseRowWriterTruthFrame.initial]
      change BitMachineStackEmbedding.bank
        SourceClauseRowWriterTruthFrame.writerEmbedding
        (SourceClauseRowWriterTruthFlagFrame.afterFlag row n r
          saved output count b remaining)
        (SourceClauseRowWriterBlank.bank row n r
          ((EncodedCNF.clauseFields
            (SourceClauseEncoding.chain (SourceClauseGenericCallback.base n r k)
              (SourceClauseRowSchedule.tupleClause hq k
                (SourceClauseCallback.rowQuery row) b))).reverse ++ saved)
          output
          (List.replicate (SourceClauseGenericDual.clauseCount q b)
            true ++ count))
        (SourceClauseRowWriterTruthFrame.writerEmbedding x) = _
      rw [BitMachineStackEmbedding.bank_at]
  | inr x =>
      fin_cases x <;>
        simp [cleared, BitMachineClearBank.cleared,
          SourceClauseRowWriterTruthFrame.initial]


end EthInapproximability.CurrentPaper.SourceClauseGenericReset
