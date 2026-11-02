import EthInapproximability.CurrentPaper.SourceCSPNextParserGrowth
import EthInapproximability.CurrentPaper.SourceCSPRowCleanupPolynomial
import EthInapproximability.CurrentPaper.SourceClauseCallbackPolynomial

/-! Bounds for the actual framed row-loop bank and its post-parser cleanup. -/

namespace EthInapproximability.CurrentPaper.SourceCSPNextRowFrameGrowth

open SourceCSPNextParserGrowth
open scoped Classical

theorem callbackBank_words_le {q H : ℕ}
    (S : SourceCSPGlobalDecisionProgram.Stack q → List Bool)
    (row : SourceCSPRowQueryFrame.Stack q → List Bool)
    (n r : ℕ) (saved output count : List Bool)
    (hS : ∀ x, (S x).length ≤ H)
    (hrow : ∀ x, (row x).length ≤ H)
    (hn : n ≤ H) (hr : r ≤ H)
    (hsaved : saved.length ≤ H)
    (houtput : output.length ≤ H)
    (hcount : count.length ≤ H) :
    ∀ x, (SourceCSPNextRowBridge.callbackBank S row n r
      saved output count x).length ≤ H := by
  have hw := SourceClauseCallbackPolynomial.blank_words_le
    row n r H saved output count hn hr hrow hsaved houtput hcount
  intro x
  cases x with
  | inl g => exact hS g
  | inr x =>
      cases x with
      | inl k => exact hw k
      | inr i =>
          fin_cases i <;>
            simp [SourceCSPNextRowBridge.callbackBank,
              SourceClauseRowWriterTruthFrame.initial]

noncomputable def cleanupCoefficient (q : ℕ) : ℕ :=
  (SourceClauseClearExcept.workCount
    (SourceClauseRowWriterCleanup.keep q) + 2) *
      (steppedWordCoefficient q + 1)

theorem callbackCleanupTime_le_quadratic {q H : ℕ}
    (B : SourceCSPNextRowBridge.Stack q → List Bool)
    (rest cap : List Bool)
    (V : SourceCSPRowQueryFrame.Stack q → List Bool)
    (hB : ∀ x, (B x).length ≤ H)
    (hrest : rest.length ≤ H) (hcap : cap.length ≤ H)
    (hV : ∀ x, (V x).length ≤ parseWordCoefficient q * (H + 1) ^ 2) :
    SourceCSPNextRowBridge.callbackCleanupTime
      (SourceCSPNextRowBridge.steppedResult B rest cap V) ≤
        cleanupCoefficient q * (H + 1) ^ 2 := by
  have hstep := steppedResult_words_le B rest cap V
    hB hrest hcap hV
  have hc := SourceCSPRowCleanupPolynomial.callbackCleanupTime_le
    (SourceCSPNextRowBridge.steppedResult B rest cap V)
    (H := steppedWordCoefficient q * (H + 1) ^ 2) hstep
  have hM : 1 ≤ (H + 1) ^ 2 := by nlinarith
  have hmul := Nat.mul_le_mul_left
    (SourceClauseClearExcept.workCount
      (SourceClauseRowWriterCleanup.keep q) + 2) hM
  dsimp [cleanupCoefficient]
  nlinarith

end EthInapproximability.CurrentPaper.SourceCSPNextRowFrameGrowth
