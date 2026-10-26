import Paper2.YaoEntryRuns
import Paper2.YaoMaterializationBounds

/-! Unit 5 segment Y9, writer phase only (lane a-yao-owner-2).

From the writer start configuration (static bank `yaoBank`, unary `r, c`), the ONE
fixed program prints exactly `(materialize t lambda edges bits).bits` within the
admitted cubic writer clock `20 * (r + c + T + 1) ^ 3` (admitted
`MatrixTableWriter.writerBound_polynomial`), and the printed list has the admitted
length bound (`YaoMaterializationBounds.materialize_length_le`).  The YES/NO clauses
of T30 are the admitted `materialize_yes_bound` / `materialize_no_success` about the
SAME object `materialize t lambda edges bits` (no restatement, no transfer).

NOT claimed: the preparation of the writer start configuration from the encoded
source and the tape (Y2 ; Y6 ; placement into `yaoBank`), the output framing (Y8),
and any polynomial bound on `yaoT` in terms of the input length. -/

noncomputable section

namespace Paper2.YaoEntryRuns

open Turing
open EthInapproximability.CurrentPaper
open Paper2.YaoLowerBound
open Paper2.YaoLookup
open Paper2.YaoMaterialization
open Paper2.YaoOneEntry
open Paper2.YaoLowerBound.Materialization

theorem yao_writer_phase {v e : ℕ} (t lambda : ℕ) (ht : 1 ≤ t)
    (edges : Fin e → Fin (2 ^ t * 2 ^ t) ↪ Fin v)
    (bits : SerializedTape t (paddedEdgeBits e) lambda) (output : List Bool) :
    (∃ n ≤ 20 * (rowCount v t (paddedEdgeBits e) lambda +
        columnCount t (paddedEdgeBits e) lambda + yaoT t lambda edges + 1) ^ 3, ∃ w,
      MatrixTableWriter.run (entryProgram (writerPlace t lambda))
        (BitMachineRawSequence.leftLabel Paper2.YaoIndexDecoder.startLabel)
        (entryControl t lambda) n
        (MatrixTableWriter.cfg (some (.inr (.copy .rows))) (entryControl t lambda, none)
          (MatrixTableWriter.ready (yaoBank t lambda edges bits)
            (rowCount v t (paddedEdgeBits e) lambda) (columnCount t (paddedEdgeBits e) lambda)
            0 0 0 0 [] output)) =
      MatrixTableWriter.cfg none w
        (MatrixTableWriter.ready (yaoBank t lambda edges bits)
          (rowCount v t (paddedEdgeBits e) lambda) (columnCount t (paddedEdgeBits e) lambda)
          0 0 0 0 [] ((materialize t lambda edges bits).bits ++ output))) ∧
    (materialize t lambda edges bits).bits.length ≤
      v * (16 * Paper2.YaoResources.entryCoefficient t lambda) * (max 1 e) ^ 4 := by
  obtain ⟨n, hn, w, hr⟩ := yao_write_rowMajor t lambda edges bits output
  exact ⟨⟨n, hn.trans (MatrixTableWriter.writerBound_polynomial _ _ _), w, hr⟩,
    Paper2.YaoMaterialization.materialize_length_le t lambda ht edges bits⟩

#print axioms yao_writer_phase

end Paper2.YaoEntryRuns

end
