import Paper2.MMain
import Paper2.ParameterizedCanonicalSource

/-! Unit 3, segment (2), second part: the outputs of `MProducer.mProg` on unary
`b = sourceBudget L r q k`, `k`, `L` are the literal scheduled sample dimensions
`mY = SourceRecursiveNoSampling.sourceCols L r q k` and `mX = SourceRecursiveNoSampling.sourceRows L r q k`
(definitions read literally: `sourceRank = 2 ^ (sourceBudget - 1)`, `sourceCost`, `compressionEntropy`,
`compressionColumnDraws Z = 2 (Z + 12)`, `compressionRowDraws Z L = (Z + 12) ⌈/⌉ L`). -/

set_option maxRecDepth 16384

namespace Paper2.MProducer

open SourceRecursiveNoSampling

theorem cost_eq (L r q k : ℕ) : sourceCost L r q k = sourceBudget L r q k + k := by
  unfold sourceCost sourceBudget
  ring

theorem entropy_eq (L r q k : ℕ) :
    compressionEntropy (sourceRank L r q k) (sourceCost L r q k) + 12 =
      12 + (2 + 2 ^ (sourceBudget L r q k - 1) * (2 ^ (sourceBudget L r q k - 1) + 1)) *
        2 ^ (k + sourceBudget L r q k - 1) := by
  rw [cost_eq]
  unfold compressionEntropy sourceRank
  rw [Nat.add_comm k (sourceBudget L r q k)]
  ring

theorem cols_eq (L r q k : ℕ) :
    sourceCols L r q k =
      (12 + (2 + 2 ^ (sourceBudget L r q k - 1) * (2 ^ (sourceBudget L r q k - 1) + 1)) *
        2 ^ (k + sourceBudget L r q k - 1)) +
      (12 + (2 + 2 ^ (sourceBudget L r q k - 1) * (2 ^ (sourceBudget L r q k - 1) + 1)) *
        2 ^ (k + sourceBudget L r q k - 1)) := by
  unfold sourceCols compressionColumnDraws
  rw [entropy_eq]
  ring

theorem rows_eq (L r q k : ℕ) :
    sourceRows L r q k =
      (L + (12 + (2 + 2 ^ (sourceBudget L r q k - 1) * (2 ^ (sourceBudget L r q k - 1) + 1)) *
        2 ^ (k + sourceBudget L r q k - 1)) - 1) / L := by
  unfold sourceRows compressionRowDraws
  rw [Nat.ceilDiv_eq_add_pred_div, entropy_eq]
  congr 1
  omega

/-- Segment (2), second part: ONE fixed program `mProg` from unary `sourceBudget L r q k`, `k`, `L`
produces unary `sourceCols L r q k` (cell 10) and unary `sourceRows L r q k` (cell 13). -/
theorem m_run_sched (L r q k : ℕ) :
    ∃ t ≤ mBd (sourceBudget L r q k) k L, ∃ vc, ∃ F : MK → List Bool,
      ((EthInapproximability.CurrentPaper.BitMachineEncoding.advance mProg)^[t])
          (⟨some mStart, mCtl, M0 (sourceBudget L r q k) k L⟩ :
            Turing.TM2.Cfg (fun _ : MK => Bool) _ _) = ⟨none, vc, F⟩ ∧
      F 0 = u (sourceBudget L r q k) ∧ F 1 = u k ∧ F 2 = u L ∧
      F 10 = u (sourceCols L r q k) ∧ F 13 = u (sourceRows L r q k) := by
  obtain ⟨t, ht, vc, F, hr, h0, h1, h2, -, -, -, -, -, -, -, h10, -, -, h13, -⟩ :=
    m_run (sourceBudget L r q k) k L
  refine ⟨t, ht, vc, F, hr, h0, h1, h2, ?_, ?_⟩
  · rw [h10, cols_eq]
  · rw [h13, rows_eq]

#print axioms cost_eq
#print axioms entropy_eq
#print axioms cols_eq
#print axioms rows_eq
#print axioms m_run_sched

end Paper2.MProducer
