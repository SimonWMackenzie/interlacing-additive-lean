import EthInapproximability.CurrentPaper.ColumnScalarWordBase

/-! Charged physical product of the ordinal count and first-column radix. -/

namespace EthInapproximability.CurrentPaper.ColumnScalarBinBase

open Turing BitMachineEncoding MatrixStage4ScalarPreparationOps
open ColumnScalarPrefix ColumnScalarWordBase

def productSlots : Fin 6 ↪ Stack := ⟨![2,8,37,38,39,9], by decide⟩
def productProgram := multiplyProgram productSlots

def sourceBank (a s q L rx cy : ℕ) : Stack → List Bool :=
  ColumnScalarWordBase.outputBank
    (ColumnScalarWordBase.sourceBank a s q L rx cy) a s cy

def outputBank (S : Stack → List Bool) (a s q cy : ℕ) : Stack → List Bool :=
  Function.update S 9
    (List.replicate (MatrixStage4Digits.binBase a s q cy) true)

theorem binBase_run (a s q L rx cy : ℕ) :
    ((advance productProgram)^[MatrixAddressMachine.exactTime q
        (MatrixStage4Digits.wordBase a s cy) 0])
      (⟨some .outer, false, sourceBank a s q L rx cy⟩ :
        TM2.Cfg (fun _ : Stack => Bool) MatrixAddressMachine.Label Bool) =
      ⟨none, false, outputBank (sourceBank a s q L rx cy) a s q cy⟩ := by
  let S := sourceBank a s q L rx cy
  have hr := multiply_run productSlots S q
    (MatrixStage4Digits.wordBase a s cy)
    (by simp [S, productSlots, sourceBank,
      ColumnScalarWordBase.outputBank, ColumnScalarWordBase.sourceBank,
      ColumnScalarPrefix.lengthBank, ColumnScalarPrefix.qoneBank,
      ColumnScalarPrefix.inputBank])
    (by simp [S, productSlots, sourceBank,
      ColumnScalarWordBase.outputBank])
    (by simp [S, productSlots, sourceBank,
      ColumnScalarWordBase.outputBank, ColumnScalarWordBase.sourceBank,
      ColumnScalarPrefix.lengthBank, ColumnScalarPrefix.qoneBank,
      ColumnScalarPrefix.inputBank])
    (by simp [S, productSlots, sourceBank,
      ColumnScalarWordBase.outputBank, ColumnScalarWordBase.sourceBank,
      ColumnScalarPrefix.lengthBank, ColumnScalarPrefix.qoneBank,
      ColumnScalarPrefix.inputBank])
    (by simp [S, productSlots, sourceBank,
      ColumnScalarWordBase.outputBank, ColumnScalarWordBase.sourceBank,
      ColumnScalarPrefix.lengthBank, ColumnScalarPrefix.qoneBank,
      ColumnScalarPrefix.inputBank])
  have hbank : Function.update S (productSlots 5)
      (List.replicate (q * MatrixStage4Digits.wordBase a s cy) true ++
        S (productSlots 5)) =
      outputBank S a s q cy := by
    funext j
    by_cases hj : j = 9
    · subst j
      simp [S, productSlots, sourceBank, outputBank,
        MatrixStage4Digits.binBase, ColumnScalarWordBase.outputBank,
        ColumnScalarWordBase.sourceBank, ColumnScalarPrefix.lengthBank,
        ColumnScalarPrefix.qoneBank, ColumnScalarPrefix.inputBank]
    · simp [productSlots, outputBank, Function.update_of_ne hj]
  simpa only [productProgram, hbank] using hr

#print axioms binBase_run

end EthInapproximability.CurrentPaper.ColumnScalarBinBase
