import EthInapproximability.CurrentPaper.WeightedMJoin
import EthInapproximability.CurrentPaper.MatrixStage4ScalarPreparationOps
import Mathlib.Data.Fin.VecNotation

/-! Source-preserving physical copy from already-computed weighted-writer
q₂ cell56 to the threshold arithmetic's input cell0. -/

namespace EthInapproximability.CurrentPaper.WeightedQCopy

open Turing BitMachineEncoding
noncomputable section

abbrev Stack := WeightedMWidth.Stack

def slots : Fin 3 ↪ Stack :=
  ⟨![WeightedMWidth.writer 56,WeightedMWidth.scalar 0,
      WeightedMWidth.scalar 10], by decide⟩

def program := MatrixStage4ScalarPreparationOps.copyProgram slots

theorem run (S : Stack → List Bool) (q : ℕ)
    (hq : S (WeightedMWidth.writer 56) = List.replicate q true)
    (h0 : S (WeightedMWidth.scalar 0) = [])
    (h10 : S (WeightedMWidth.scalar 10) = []) :
    ((advance program)^[2*q+2])
      (⟨some .scan,none,S⟩ : TM2.Cfg (fun _ : Stack => Bool)
        BitMachineCopy.Label (Option Bool)) =
      ⟨none,none,Function.update S (WeightedMWidth.scalar 0)
        (List.replicate q true)⟩ := by
  have hr := MatrixStage4ScalarPreparationOps.copy_run slots S h10
  simpa [program,slots,hq,h0] using hr

#print axioms run

end
end EthInapproximability.CurrentPaper.WeightedQCopy
