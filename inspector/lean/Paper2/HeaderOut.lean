import Paper2.HeaderA
import Paper2.EncodedSelectedOutput

/-! Unit 3, segment (5), G2: the header stage `HeaderA.prog` delivers EXACTLY the
consumer word `EncodedSelectedOutput.outputBits hn edge Δ γ k t` (the encoded
`selectedInstance`, same object as `TotalFiniteConstructor.select`) on its output
cell, from unary rows, cols, threshold of that instance and its table word.
Branch-independent (success or fallback: `selectedInstance` is defined for every
tape by `instanceOf ((select …).table t) (select …).budget`). The four entry cells
are SUPPLIED here; their producers on the two branch banks are not bound. -/

set_option maxHeartbeats 8000000
set_option maxRecDepth 16384

namespace Paper2.HeaderOut

noncomputable section

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.EncodedCommunication

theorem header_outputBits {n m : ℕ} (hn : 0 < n) (edge : Fin m → Bool → Fin n) (Δ : ℕ)
    (γ : ℚ) (k : ℕ) (t : (TotalFiniteConstructorScratch.select hn edge Δ γ k).Tape)
    (suffix : List Bool) :
    let i := EncodedSelectedOutput.selectedInstance hn edge Δ γ k t
    ∃ T ≤ UnaryBinaryEncoding.coefficient * (i.rows + 1) ^ 2 +
        UnaryBinaryEncoding.coefficient * (i.cols + 1) ^ 2 +
        UnaryBinaryEncoding.coefficient * (i.threshold + 1) ^ 2 +
        (2 * (natField i.rows ++ natField i.cols ++ natField i.threshold).length + 2) + 3,
      ∃ v F,
        ((advance HeaderA.prog)^[T]) (⟨some HeaderA.progStart, HeaderA.progCtl,
          HeaderA.Hin i.rows i.cols i.threshold i.table suffix⟩ :
          TM2.Cfg (fun _ : HeaderA.HB => Bool) _ _) = ⟨none, v, F⟩ ∧
        F HeaderA.outH = EncodedSelectedOutput.outputBits hn edge Δ γ k t ++ suffix := by
  intro i
  exact HeaderA.header_instance i suffix

end

end Paper2.HeaderOut

#print axioms Paper2.HeaderOut.header_outputBits
