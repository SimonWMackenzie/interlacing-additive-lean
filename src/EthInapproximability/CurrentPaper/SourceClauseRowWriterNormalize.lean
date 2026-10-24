import EthInapproximability.CurrentPaper.SourceClauseRowWriterGateClean

/-! The actual whole-bank normal form after a charged writer cleanup. -/

namespace EthInapproximability.CurrentPaper.SourceClauseRowWriterNormalize

open scoped Classical

theorem cleanup_blank {q : ℕ}
    (S : SourceClauseRowWriterOperands.Stack q → List Bool)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r : ℕ) (saved output count : List Bool)
    (hrow : ∀ x, S (SourceClauseRowWriterCleanup.rowCell x) = row x)
    (hsaved : S SourceClauseRowWriterCleanup.savedCell = saved)
    (houtput : S SourceClauseRowWriterCleanup.outputCell = output)
    (hcount : S SourceClauseRowWriterCleanup.countCell = count)
    (hn : S SourceClauseRowWriterOperands.vertex = List.replicate n true)
    (hr : S SourceClauseRowWriterOperands.rowIndex = List.replicate r true) :
    SourceClauseRowWriterCleanup.clean S =
      SourceClauseRowWriterBlank.bank row n r saved output count := by
  funext x
  cases x with
  | inl y =>
      cases y with
      | inl z =>
          cases z with
          | inl z =>
              rw [show (Sum.inl (Sum.inl (Sum.inl z)) :
                SourceClauseRowWriterOperands.Stack q) =
                SourceClauseRowWriterCleanup.rowCell z by rfl]
              rw [SourceClauseRowWriterCleanup.retained _ _
                (SourceClauseRowWriterCleanup.row_mem z), hrow]
              rfl
          | inr i =>
              fin_cases i <;>
                simp [SourceClauseRowWriterCleanup.clean,
                  SourceClauseRowWriterCleanup.keep,
                  SourceClauseRowWriterCleanup.savedCell,
                  SourceClauseRowWriterCleanup.outputCell,
                  SourceClauseRowWriterCleanup.countCell,
                  SourceClauseRowWriterCleanup.rowCell,
                  SourceClauseRowWriterBlank.bank,
                  SourceClauseRowWriterBlank.master,
                  SourceClauseRowWriterBlank.core,
                  SourceClauseClearExcept.result,
                  hsaved, houtput, hcount]
              all_goals first
                | simpa [SourceClauseRowWriterCleanup.savedCell] using hsaved
                | simpa [SourceClauseRowWriterCleanup.outputCell] using houtput
                | simpa [SourceClauseRowWriterCleanup.countCell] using hcount
      | inr z =>
          simp [SourceClauseRowWriterCleanup.clean,
            SourceClauseRowWriterCleanup.keep,
            SourceClauseRowWriterCleanup.rowCell,
            SourceClauseRowWriterCleanup.savedCell,
            SourceClauseRowWriterCleanup.outputCell,
            SourceClauseRowWriterCleanup.countCell,
            SourceClauseRowWriterOperands.vertex,
            SourceClauseRowWriterOperands.rowIndex,
            SourceClauseRowWriterBlank.bank,
            SourceClauseRowWriterBlank.master,
            SourceClauseClearExcept.result]
  | inr i =>
      fin_cases i <;>
        simp [SourceClauseRowWriterCleanup.clean,
          SourceClauseRowWriterCleanup.keep,
          SourceClauseRowWriterCleanup.rowCell,
          SourceClauseRowWriterCleanup.savedCell,
          SourceClauseRowWriterCleanup.outputCell,
          SourceClauseRowWriterCleanup.countCell,
          SourceClauseRowWriterOperands.vertex,
          SourceClauseRowWriterOperands.rowIndex,
          SourceClauseRowWriterOperands.scratch,
          SourceClauseRowWriterBlank.bank,
          SourceClauseClearExcept.result, hn, hr]
      all_goals first
        | simpa [SourceClauseRowWriterOperands.vertex] using hn
        | simpa [SourceClauseRowWriterOperands.rowIndex] using hr

def gateSaved {q : ℕ} (j : Fin q)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r a k s t w : ℕ) (sign : Bool) (saved : List Bool) : List Bool :=
  let p := SourceClauseRowSlotAddress.slot n r a q k * w + (n * a + t)
  (EncodedCNF.encodeClause
    (SourceClauseGatePrepare.thirdClause p
      ⟨(row (.inl (j, 1))).length * a + s, sign⟩)).reverse ++
  (EncodedCNF.encodeClause (SourceClauseGatePrepare.secondClause p)).reverse ++
  (EncodedCNF.encodeClause
    (SourceClauseGatePrepare.firstClause p
      ⟨(row (.inl (j, 1))).length * a + s, sign⟩)).reverse ++ saved

theorem gate_blank {q : ℕ} (j : Fin q)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r a k s t w : ℕ) (sign : Bool)
    (saved output count : List Bool)
    (h : row (.inl (j, 1)) =
      List.replicate (row (.inl (j, 1))).length true) :
    SourceClauseRowWriterGateClean.result j row n r a k s t w sign
      saved output count =
      SourceClauseRowWriterBlank.bank row n r
        (gateSaved j row n r a k s t w sign saved)
        output (true :: true :: true :: count) := by
  unfold SourceClauseRowWriterGateClean.result
  apply cleanup_blank
  · intro x
    have he := SourceClauseRowWriterGateClean.final_row
      j row n r a k s t w sign saved output count h x
    rw [SourceClauseRowWriterGateClean.result,
      SourceClauseRowWriterCleanup.retained _ _
        (SourceClauseRowWriterCleanup.row_mem x)] at he
    exact he
  · have he := SourceClauseRowWriterGateClean.final_saved
      j row n r a k s t w sign saved output count
    rw [SourceClauseRowWriterGateClean.result,
      SourceClauseRowWriterCleanup.retained _ _
        SourceClauseRowWriterCleanup.saved_mem] at he
    exact he
  · have he := SourceClauseRowWriterGateClean.final_output
      j row n r a k s t w sign saved output count
    rw [SourceClauseRowWriterGateClean.result,
      SourceClauseRowWriterCleanup.retained _ _
        SourceClauseRowWriterCleanup.output_mem] at he
    exact he
  · have he := SourceClauseRowWriterGateClean.final_count
      j row n r a k s t w sign saved output count
    rw [SourceClauseRowWriterGateClean.result,
      SourceClauseRowWriterCleanup.retained _ _
        SourceClauseRowWriterCleanup.count_mem] at he
    exact he
  · have he := SourceClauseRowWriterGateClean.final_vertex
      j row n r a k s t w sign saved output count
    rw [SourceClauseRowWriterGateClean.result,
      SourceClauseRowWriterCleanup.retained _ _
        SourceClauseRowWriterCleanup.vertex_mem] at he
    exact he
  · have he := SourceClauseRowWriterGateClean.final_row_index
      j row n r a k s t w sign saved output count
    rw [SourceClauseRowWriterGateClean.result,
      SourceClauseRowWriterCleanup.retained _ _
        SourceClauseRowWriterCleanup.row_index_mem] at he
    exact he

end EthInapproximability.CurrentPaper.SourceClauseRowWriterNormalize
