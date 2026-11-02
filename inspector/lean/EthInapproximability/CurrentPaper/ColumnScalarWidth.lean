import EthInapproximability.CurrentPaper.ColumnScalarBinPower

/-! Final physical product for the exact Stage--4 raw column width. -/

namespace EthInapproximability.CurrentPaper.ColumnScalarWidth

open Turing BitMachineEncoding MatrixStage4ScalarPreparationOps
open ColumnScalarPrefix

def sourceBank (a s q L rx cy : ℕ) : Stack → List Bool :=
  ColumnScalarBinPower.outputBank
    (ColumnScalarBinPower.sourceBank a s q L rx cy) a s q cy

def productSlots : Fin 6 ↪ Stack := ⟨![10,11,37,38,39,12], by decide⟩
def productProgram := multiplyProgram productSlots

def outputBank (S : Stack → List Bool) (a s q cy : ℕ) : Stack → List Bool :=
  Function.update S 12
    (List.replicate (MatrixStage4Codes.cols a s q cy) true)

theorem width_run (a s q L rx cy : ℕ) :
    ((advance productProgram)^[MatrixAddressMachine.exactTime
        (cy^(s+1)) ((MatrixStage4Digits.binBase a s q cy)^s) 0])
      (⟨some .outer, false, sourceBank a s q L rx cy⟩ :
        TM2.Cfg (fun _ : Stack => Bool) MatrixAddressMachine.Label Bool) =
      ⟨none, false, outputBank (sourceBank a s q L rx cy) a s q cy⟩ := by
  let S := sourceBank a s q L rx cy
  have hr := multiply_run productSlots S (cy^(s+1))
    ((MatrixStage4Digits.binBase a s q cy)^s)
    (by simp [S, productSlots, sourceBank,
      ColumnScalarBinPower.outputBank, ColumnScalarBinPower.sourceBank,
      ColumnScalarTailPower.outputBank])
    (by simp [S, productSlots, sourceBank,
      ColumnScalarBinPower.outputBank])
    (by simp [S, productSlots, sourceBank,
      ColumnScalarBinPower.outputBank, ColumnScalarBinPower.sourceBank,
      ColumnScalarTailPower.outputBank, ColumnScalarTailPower.sourceBank,
      ColumnScalarBinBase.outputBank, ColumnScalarBinBase.sourceBank,
      ColumnScalarWordBase.outputBank, ColumnScalarWordBase.sourceBank,
      ColumnScalarPrefix.lengthBank, ColumnScalarPrefix.qoneBank,
      ColumnScalarPrefix.inputBank])
    (by simp [S, productSlots, sourceBank,
      ColumnScalarBinPower.outputBank, ColumnScalarBinPower.sourceBank,
      ColumnScalarTailPower.outputBank, ColumnScalarTailPower.sourceBank,
      ColumnScalarBinBase.outputBank, ColumnScalarBinBase.sourceBank,
      ColumnScalarWordBase.outputBank, ColumnScalarWordBase.sourceBank,
      ColumnScalarPrefix.lengthBank, ColumnScalarPrefix.qoneBank,
      ColumnScalarPrefix.inputBank])
    (by simp [S, productSlots, sourceBank,
      ColumnScalarBinPower.outputBank, ColumnScalarBinPower.sourceBank,
      ColumnScalarTailPower.outputBank, ColumnScalarTailPower.sourceBank,
      ColumnScalarBinBase.outputBank, ColumnScalarBinBase.sourceBank,
      ColumnScalarWordBase.outputBank, ColumnScalarWordBase.sourceBank,
      ColumnScalarPrefix.lengthBank, ColumnScalarPrefix.qoneBank,
      ColumnScalarPrefix.inputBank])
  have hbank : Function.update S (productSlots 5)
      (List.replicate ((cy^(s+1)) *
        ((MatrixStage4Digits.binBase a s q cy)^s)) true ++
        S (productSlots 5)) = outputBank S a s q cy := by
    funext j
    by_cases hj : j = 12
    · subst j
      have h12 : S 12 = [] := by
        simp [S, sourceBank, ColumnScalarBinPower.outputBank,
          ColumnScalarBinPower.sourceBank, ColumnScalarTailPower.outputBank,
          ColumnScalarTailPower.sourceBank, ColumnScalarBinBase.outputBank,
          ColumnScalarBinBase.sourceBank, ColumnScalarWordBase.outputBank,
          ColumnScalarWordBase.sourceBank, ColumnScalarPrefix.lengthBank,
          ColumnScalarPrefix.qoneBank, ColumnScalarPrefix.inputBank]
      change List.replicate (cy^(s+1) *
        (MatrixStage4Digits.binBase a s q cy)^s) true ++ S 12 =
        List.replicate (MatrixStage4Codes.cols a s q cy) true
      rw [h12, List.append_nil]
      rfl
    · simp [productSlots, outputBank, Function.update_of_ne hj]
  simpa only [productProgram, hbank] using hr

#print axioms width_run

end EthInapproximability.CurrentPaper.ColumnScalarWidth
