import EthInapproximability.CurrentPaper.MatrixStage4AlignmentStream
import EthInapproximability.CurrentPaper.MatrixStage4AlignmentDigits

/-!
# Source meaning of the charged variable-bin alignment stream

The stream here is a semantic encoding of every selector digit. Its physical
production from the raw-column evaluator remains a separate obligation.
-/

namespace EthInapproximability.CurrentPaper.MatrixStage4AlignmentCorrect

open MatrixStage4Codes MatrixStage4AlignmentDigits
open MatrixStage4AlignmentStream
open Construction

def selectorWords {a s q cy : ℕ} (code : Fin (cols a s q cy)) :
    List ℕ := List.ofFn (fun p : Fin s => selectorDigit code p)

theorem selectorWords_all_iff {a s q cy : ℕ} (hs : 0 < s)
    (code : Fin (cols a s q cy)) :
    (selectorWords code).all
      (fun x => decide (x = selectorDigit code (firstBin s hs))) = true ↔
      aligned hs ((rawColumnCode a s q cy).symm code) := by
  rw [List.all_eq_true,aligned_iff_digits hs code]
  constructor
  · intro h p
    exact of_decide_eq_true (h _ (List.mem_ofFn.mpr ⟨p,rfl⟩))
  · intro h x hx
    obtain ⟨p,rfl⟩ := List.mem_ofFn.mp hx
    exact decide_eq_true (h p)

theorem selectorWords_halt {a s q cy : ℕ} (hs : 0 < s)
    (code : Fin (cols a s q cy)) :
    ∃ t ≤ MatrixStage4AlignmentStream.budget (selectorWords code)
        (selectorDigit code (firstBin s hs)) + 1,
      MatrixStage4AlignmentStream.run t
      (MatrixStage4AlignmentStream.cfg (some .start)
        MatrixStage4AlignmentStream.initial
        (MatrixStage4AlignmentStream.words (selectorWords code))
        (List.replicate (selectorDigit code (firstBin s hs)) true) []) =
      MatrixStage4AlignmentStream.cfg none
        ((selectorWords code).all
          (fun x => decide (x = selectorDigit code (firstBin s hs))),none,none)
        [] (List.replicate (selectorDigit code (firstBin s hs)) true) [] :=
  MatrixStage4AlignmentStream.words_halt (selectorWords code)
    (selectorDigit code (firstBin s hs))

end EthInapproximability.CurrentPaper.MatrixStage4AlignmentCorrect
