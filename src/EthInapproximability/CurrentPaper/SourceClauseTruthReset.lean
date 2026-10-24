import EthInapproximability.CurrentPaper.SourceClauseActualCallback
import EthInapproximability.CurrentPaper.BitMachineClearBank

/-! A physical two-stack reset for the copied truth cursor and selected-bit
flag. It leaves every writer and checked-row stack untouched. -/

namespace EthInapproximability.CurrentPaper.SourceClauseCallback.TruthReset

open Turing Turing.TM2.Stmt BitMachineEncoding
open scoped Classical

abbrev Stack (q : ℕ) := SourceClauseRowWriterTruthFrame.Stack q
abbrev Control := Unit × Option Bool

noncomputable def program {q : ℕ} : Fin 4 →
    TM2.Stmt (fun _ : Stack q => Bool) (Fin 4) Control
  | 0 => BitMachineClearBank.clearStep (.inr 0) 0 1
  | 1 => BitMachineClearBank.clearStep (.inr 1) 1 2
  | 2 => BitMachineClearBank.finishStep id 3
  | 3 => halt

noncomputable def cleared {q : ℕ} (S : Stack q → List Bool) : Stack q → List Bool :=
  BitMachineClearBank.cleared (fun i : Fin 2 => (Sum.inr i : Stack q)) S

theorem run {q : ℕ} (S : Stack q → List Bool) :
    ((advance (program (q := q)))^[(S (.inr 0)).length +
      (S (.inr 1)).length + 4])
      ⟨some (0 : Fin 4), ((), none), S⟩ =
      ⟨none, ((), none), cleared S⟩ := by
  have h := BitMachineClearBank.clear_bank_run
    (program (q := q)) id (3 : Fin 4) 2
    (fun i : Fin 2 => (Sum.inr i : Stack q))
    (by intro i j hij; exact Sum.inr.inj hij)
    (fun i : Fin 3 => i.castSucc)
    (by intro i; fin_cases i <;> rfl)
    (by rfl) () S
  simp only [Fin.sum_univ_two] at h
  have h' :
      ((advance (program (q := q)))^[(S (.inr 0)).length +
        (S (.inr 1)).length + 3])
        ⟨some (0 : Fin 4), ((), none), S⟩ =
        ⟨some (3 : Fin 4), ((), none), cleared S⟩ := by
    simpa only [Fin.castSucc_zero, id_eq, cleared] using h
  rw [show (S (.inr 0)).length + (S (.inr 1)).length + 4 =
    ((S (.inr 0)).length + (S (.inr 1)).length + 2 + 1) + 1 by omega,
    Function.iterate_succ_apply', h']
  rfl

theorem cleared_finalBank {q : ℕ} (hq : 0 < q)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r : ℕ) (k : Fin (2 ^ q))
    (saved output count remaining : List Bool) (b : Bool) :
    cleared (SourceClauseCallback.DualDispatch.finalBank hq row n r k
      saved output count remaining b) =
      SourceClauseRowWriterTruthFrame.initial row n r
        ((EncodedCNF.clauseFields
          (SourceClauseEncoding.chain (SourceClauseCallback.base n r k)
            (SourceClauseRowSchedule.tupleClause hq k
              (SourceClauseCallback.rowQuery row) b))).reverse ++ saved)
        output
        (List.replicate (SourceClauseCallback.DualDispatch.clauseCount q b)
          true ++ count) := by
  funext x
  cases x with
  | inl x =>
      simp [cleared, BitMachineClearBank.cleared,
        SourceClauseCallback.DualDispatch.finalBank,
        SourceClauseRowWriterTruthFrame.initial]
      change BitMachineStackEmbedding.bank
        SourceClauseRowWriterTruthFrame.writerEmbedding
        (SourceClauseRowWriterTruthFlagFrame.afterFlag row n r
          saved output count b remaining)
        (SourceClauseRowWriterBlank.bank row n r
          ((EncodedCNF.clauseFields
            (SourceClauseEncoding.chain (SourceClauseCallback.base n r k)
              (SourceClauseRowSchedule.tupleClause hq k
                (SourceClauseCallback.rowQuery row) b))).reverse ++ saved)
          output
          (List.replicate (SourceClauseCallback.DualDispatch.clauseCount q b)
            true ++ count))
        (SourceClauseRowWriterTruthFrame.writerEmbedding x) = _
      rw [BitMachineStackEmbedding.bank_at]
  | inr x =>
      fin_cases x <;>
        simp [cleared, BitMachineClearBank.cleared,
          SourceClauseRowWriterTruthFrame.initial]

end EthInapproximability.CurrentPaper.SourceClauseCallback.TruthReset
