import EthInapproximability.CurrentPaper.SourceCSPNextRowBridge

/-! Linear bounds for the two physical row-loop clearing clocks, conditional
on explicit whole-bank word-length bounds. -/

namespace EthInapproximability.CurrentPaper.SourceCSPRowCleanupPolynomial

open scoped BigOperators Classical

theorem fin_sum_le {N H : ℕ} (f : Fin N → ℕ)
    (hf : ∀ i, f i ≤ H) : (∑ i : Fin N, f i) ≤ N * H := by
  calc
    (∑ i : Fin N, f i) ≤ ∑ _ : Fin N, H :=
      Finset.sum_le_sum (by intro i hi; exact hf i)
    _ = N * H := by simp

theorem resetCost_le {q H : ℕ}
    (B : SourceCSPNextRowBridge.Stack q → List Bool)
    (cap : List Bool)
    (hbank : ∀ x, (B x).length ≤ H)
    (hcap : cap.length ≤ H) :
    SourceCSPNextRowBridge.resetCost B cap ≤ (q * 5 + 9) * (H + 1) := by
  have hs := fin_sum_le
    (fun i : Fin (q * 5 + 4) =>
      (SourceCSPNextRowBridge.resetProjection B
        (SourceCSPRowLoopClear.scratch q i)).length)
    (by intro i; exact hbank _)
  dsimp [SourceCSPNextRowBridge.resetCost]
  nlinarith

theorem callbackCleanupTime_le {q H : ℕ}
    (B : SourceCSPNextRowBridge.Stack q → List Bool)
    (hbank : ∀ x, (B x).length ≤ H) :
    SourceCSPNextRowBridge.callbackCleanupTime B ≤
      (SourceClauseClearExcept.workCount
        (SourceClauseRowWriterCleanup.keep q) + 2) * (H + 1) := by
  have hs := fin_sum_le
    (fun i : Fin (SourceClauseClearExcept.workCount
      (SourceClauseRowWriterCleanup.keep q)) =>
      (SourceCSPNextRowBridge.writerProjection B
        (SourceClauseClearExcept.workBank
          (SourceClauseRowWriterCleanup.keep q) i)).length)
    (by intro i; exact hbank _)
  dsimp [SourceCSPNextRowBridge.callbackCleanupTime]
  nlinarith

end EthInapproximability.CurrentPaper.SourceCSPRowCleanupPolynomial
