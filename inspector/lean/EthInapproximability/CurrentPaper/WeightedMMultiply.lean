import EthInapproximability.CurrentPaper.WeightedMWidth
import EthInapproximability.CurrentPaper.BitMachineClearBank

/-! Multiply the physically produced `qOne a` by the live row count at
writer17, write the threshold input at scalar2, then clear the width work
cell with a charged pop loop. -/

namespace EthInapproximability.CurrentPaper.WeightedMMultiply

open Turing BitMachineEncoding
noncomputable section

abbrev Stack := WeightedMWidth.Stack

def slots : Fin 6 ↪ Stack :=
  ⟨![WeightedMWidth.width,WeightedMWidth.writer 17,
      WeightedMWidth.scalar 4,WeightedMWidth.scalar 5,
      WeightedMWidth.scalar 6,WeightedMWidth.scalar 2], by decide⟩

def multiplyProgram := MatrixStage4ScalarPreparationOps.multiplyProgram slots

theorem multiply_run (S : Stack → List Bool) (a rx : ℕ)
    (hw : S WeightedMWidth.width =
      List.replicate (Construction.qOne a) true)
    (hrx : S (WeightedMWidth.writer 17) = List.replicate rx true)
    (h4 : S (WeightedMWidth.scalar 4) = [])
    (h5 : S (WeightedMWidth.scalar 5) = [])
    (h6 : S (WeightedMWidth.scalar 6) = [])
    (hm : S (WeightedMWidth.scalar 2) = []) :
    ((advance multiplyProgram)^[MatrixAddressMachine.exactTime
      (Construction.qOne a) rx 0])
      (⟨some .outer,false,S⟩ : TM2.Cfg (fun _ : Stack => Bool)
        MatrixAddressMachine.Label Bool) =
      ⟨none,false,Function.update S (WeightedMWidth.scalar 2)
        (List.replicate (Construction.qOne a * rx) true)⟩ := by
  have h := MatrixStage4ScalarPreparationOps.multiply_run slots S
    (Construction.qOne a) rx hw hrx h4 h5 h6
  simpa [multiplyProgram,slots,hm] using h

inductive ClearLabel where
  | loop | done
  deriving DecidableEq, Fintype

def clearProgram : ClearLabel →
    TM2.Stmt (fun _ : Stack => Bool) ClearLabel (Unit × Option Bool)
  | .loop => BitMachineClearBank.clearStep WeightedMWidth.width .loop .done
  | .done => .halt

def clearCost (S : Stack → List Bool) : ℕ :=
  (S WeightedMWidth.width).length + 2

theorem clear_run (S : Stack → List Bool) :
    ((advance clearProgram)^[clearCost S])
      (⟨some .loop,((),none),S⟩ :
        TM2.Cfg (fun _ : Stack => Bool) ClearLabel (Unit × Option Bool)) =
      ⟨none,((),none),Function.update S WeightedMWidth.width []⟩ := by
  have hr := BitMachineClearBank.clear_one_run clearProgram
    WeightedMWidth.width .loop .done rfl () S
  have hfinish : advance clearProgram
      (⟨some .done,((),none),Function.update S WeightedMWidth.width []⟩ :
        TM2.Cfg (fun _ : Stack => Bool) ClearLabel (Unit × Option Bool)) =
      ⟨none,((),none),Function.update S WeightedMWidth.width []⟩ := rfl
  dsimp only [clearCost]
  rw [show (S WeightedMWidth.width).length + 2 =
    ((S WeightedMWidth.width).length + 1) + 1 by omega,
    Function.iterate_succ_apply',hr,hfinish]

#print axioms multiply_run
#print axioms clear_run

end
end EthInapproximability.CurrentPaper.WeightedMMultiply
