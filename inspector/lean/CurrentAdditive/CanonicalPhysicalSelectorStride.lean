import CurrentAdditive.CanonicalPackedFieldOrder
import EthInapproximability.CurrentPaper.MatrixStage4ScalarPreparationOps

namespace CurrentAdditive.FiniteFieldConstructor.CanonicalTable

open Turing EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding

/-- The accumulator occupies the divisor cell of `physical_selector_digit`;
the base stays in its base cell, and the query index is disposable fuel. -/
def selectorStrideCells : MatrixWeightedPower.Stack ↪ Fin 12 :=
  ⟨Sum.elim (![1, 6, 7, 8, 9, 10] : Fin 6 → Fin 12)
    (![11] : Fin 1 → Fin 12), by decide⟩

/-- Physical preparation of the unary selector stride `H^g` in cell 1.
The row selector in cell 0 and the unary base in cell 6 are preserved. -/
theorem physical_selector_stride (H g : ℕ) (S : Fin 12 → List Bool)
    (hacc : S 1 = [true])
    (hbase : S 6 = List.replicate H true)
    (h7 : S 7 = []) (h8 : S 8 = []) (h9 : S 9 = [])
    (h10 : S 10 = [])
    (hfuel : S 11 = List.replicate g true) :
    ∃ steps ≤ MatrixWeightedPower.powerBound H g,
      ((advance (MatrixStage4ScalarPreparationOps.weightedPowerProgram
        selectorStrideCells))^[steps])
        (⟨some (.inr .test), (false, false), S⟩ :
          TM2.Cfg (fun _ : Fin 12 => Bool)
            MatrixWeightedPower.Label MatrixWeightedPower.Control) =
        ⟨none, (false, false),
          Function.update (Function.update S 1
            (List.replicate (H ^ g) true)) 11 []⟩ := by
  simpa only [selectorStrideCells] using
    MatrixStage4ScalarPreparationOps.weighted_power_run
      selectorStrideCells S H g
      (by simpa [selectorStrideCells] using hacc)
      (by simpa [selectorStrideCells] using hbase)
      (by simpa [selectorStrideCells] using h7)
      (by simpa [selectorStrideCells] using h8)
      (by simpa [selectorStrideCells] using h9)
      (by simpa [selectorStrideCells] using h10)
      (by simpa [selectorStrideCells] using hfuel)

#print axioms physical_selector_stride

end CurrentAdditive.FiniteFieldConstructor.CanonicalTable
