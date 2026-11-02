import EthInapproximability.CurrentPaper.MatrixStage4ActiveRankMachine
import EthInapproximability.CurrentPaper.MatrixStage4ColumnMachine

/-!
# Arithmetic target for variable-bin selector alignment

This file identifies the exact mixed-radix selector ordinals the eventual
physical alignment loop must compare. It is a semantic target, not an
implementation of that loop.
-/

namespace EthInapproximability.CurrentPaper.MatrixStage4AlignmentDigits

open Construction MatrixStage4Codes MatrixStage4Digits

def selectorDigit {a s q cy : ℕ}
    (code : Fin (cols a s q cy)) (p : Fin s) : ℕ :=
  binDigit code.val a s q cy p / wordBase a s cy

theorem selector_value {a s q cy : ℕ}
    (code : Fin (cols a s q cy)) (p : Fin s) :
    (((rawColumnCode a s q cy).symm code).2 p).1.val =
      selectorDigit code p := by
  rw [selectorDigit, second_row_alpha,
    column_bin_code]

theorem aligned_iff_digits {a s q cy : ℕ} (hs : 0 < s)
    (code : Fin (cols a s q cy)) :
    aligned hs ((rawColumnCode a s q cy).symm code) ↔
      ∀ p, selectorDigit code p =
        selectorDigit code (firstBin s hs) := by
  constructor
  · intro h p
    have hp := congrArg Fin.val (h p)
    simpa only [selector_value] using hp
  · intro h p
    apply Fin.ext
    simpa only [selector_value] using h p

end EthInapproximability.CurrentPaper.MatrixStage4AlignmentDigits
