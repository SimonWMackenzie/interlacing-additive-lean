import EthInapproximability.CurrentPaper.MatrixStage4ScalarPreparationOps

set_option maxHeartbeats 1000000

namespace Paper2.AffineMultiplyAdd

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineStackEmbedding

variable {K : Type*} [DecidableEq K]

/-- Physical unary multiplication with a nonzero offset field. The three
inputs survive, both work cells return empty, and the result is prepended
to an arbitrary output suffix. -/
theorem multiply_add_run (ι : Fin 6 ↪ K) (S : K → List Bool)
    (row width column : Nat)
    (hrow : S (ι 0) = List.replicate row true)
    (hwidth : S (ι 1) = List.replicate width true)
    (hcolumn : S (ι 2) = List.replicate column true)
    (h3 : S (ι 3) = []) (h4 : S (ι 4) = []) :
    ((advance (MatrixStage4ScalarPreparationOps.multiplyProgram ι))^[
      MatrixAddressMachine.exactTime row width column])
      (⟨some .outer, false, S⟩ :
        TM2.Cfg (fun _ : K => Bool) MatrixAddressMachine.Label Bool) =
      ⟨none, false, Function.update S (ι 5)
        (List.replicate (row * width + column) true ++ S (ι 5))⟩ := by
  let c := MatrixAddressMachine.cfg (some .outer) false
    (List.replicate row true) (List.replicate width true)
    (List.replicate column true) [] [] (S (ι 5))
  have hstart : stackCfg ι S c =
      (⟨some .outer, false, S⟩ :
        TM2.Cfg (fun _ : K => Bool) MatrixAddressMachine.Label Bool) := by
    dsimp [stackCfg, c, MatrixAddressMachine.cfg]
    congr 1
    apply bank_eq_self
    intro k
    fin_cases k <;> simp [hrow, hwidth, hcolumn, h3, h4]
  have hr := BitMachineStackRun.run ι S MatrixAddressMachine.program c
    (MatrixAddressMachine.exactTime row width column)
  rw [hstart] at hr
  change _ = stackCfg ι S
    (MatrixAddressMachine.run (MatrixAddressMachine.exactTime row width column) c) at hr
  rw [show c = MatrixAddressMachine.cfg (some .outer) false
      (List.replicate row true) (List.replicate width true)
      (List.replicate column true) [] [] (S (ι 5)) from rfl,
    MatrixAddressMachine.address_run] at hr
  have hfinish : stackCfg ι S
      (MatrixAddressMachine.cfg none false
        (List.replicate row true) (List.replicate width true)
        (List.replicate column true) [] []
        (List.replicate (row * width + column) true ++ S (ι 5))) =
      (⟨none, false, Function.update S (ι 5)
        (List.replicate (row * width + column) true ++ S (ι 5))⟩ :
        TM2.Cfg (fun _ : K => Bool) MatrixAddressMachine.Label Bool) := by
    dsimp [stackCfg, MatrixAddressMachine.cfg]
    congr 1
    have hlocal : (![List.replicate row true, List.replicate width true,
        List.replicate column true, ([] : List Bool), [],
        List.replicate (row * width + column) true ++ S (ι 5)] : Fin 6 → List Bool) =
        Function.update (fun k : Fin 6 => S (ι k)) 5
          (List.replicate (row * width + column) true ++ S (ι 5)) := by
      funext k
      fin_cases k <;> simp [hrow, hwidth, hcolumn, h3, h4]
    rw [hlocal, bank_update, bank_restrict]
  exact hr.trans hfinish

#print axioms multiply_add_run

end Paper2.AffineMultiplyAdd
