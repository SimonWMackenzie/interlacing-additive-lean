import CurrentAdditive.CanonicalPhysicalSelectorStride

namespace CurrentAdditive.FiniteFieldConstructor.CanonicalTable

open Turing EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding

def selectorStridePush : Unit → TM2.Stmt (fun _ : Fin 12 => Bool) Unit (Option Bool)
  | () => .push 1 (fun _ => true) .halt

noncomputable def selectorStrideProgram :=
  BitMachineRawSequence.program selectorStridePush
    (MatrixStage4ScalarPreparationOps.weightedPowerProgram selectorStrideCells)
    (Sum.inr MatrixWeightedPower.Admin.test) none (false, false)

/-- From a blank stride cell and prepared unary `H`, `g`, this one fixed
program writes unary `H^g` into the divisor cell and consumes query fuel. -/
theorem physical_selector_stride_from_blank (H g : ℕ) (S : Fin 12 → List Bool)
    (hacc : S 1 = [])
    (hbase : S 6 = List.replicate H true)
    (h7 : S 7 = []) (h8 : S 8 = []) (h9 : S 9 = [])
    (h10 : S 10 = [])
    (hfuel : S 11 = List.replicate g true) :
    ∃ steps ≤ MatrixWeightedPower.powerBound H g + 2,
      ((advance selectorStrideProgram)^[steps])
        (⟨some (BitMachineRawSequence.leftLabel ()),
          (none, (false, false)), S⟩ : TM2.Cfg (fun _ : Fin 12 => Bool) _ _) =
        ⟨none, (none, (false, false)),
          Function.update (Function.update S 1
            (List.replicate (H ^ g) true)) 11 []⟩ := by
  let S1 := Function.update S 1 [true]
  have hpush : ((advance selectorStridePush)^[1])
      (⟨some (), none, S⟩ : TM2.Cfg (fun _ : Fin 12 => Bool) _ _) =
      ⟨none, none, S1⟩ := by
    simp only [Function.iterate_one, advance, TM2.step, TM2.stepAux,
      selectorStridePush, hacc, Option.getD_some, S1]
  obtain ⟨t, ht, hr⟩ := physical_selector_stride H g S1
    (by simp [S1])
    (by simpa [S1] using hbase)
    (by simpa [S1] using h7)
    (by simpa [S1] using h8)
    (by simpa [S1] using h9)
    (by simpa [S1] using h10)
    (by simpa [S1] using hfuel)
  obtain ⟨steps, hsteps, hrun⟩ := BitMachineRawSequence.runs
    selectorStridePush
    (MatrixStage4ScalarPreparationOps.weightedPowerProgram selectorStrideCells)
    () (Sum.inr MatrixWeightedPower.Admin.test)
    none none (false, false) (false, false)
    S S1 (Function.update (Function.update S1 1
      (List.replicate (H ^ g) true)) 11 []) 1 t hpush hr
  refine ⟨steps, by omega, ?_⟩
  simpa only [selectorStrideProgram, S1, Function.update_idem] using hrun

#print axioms physical_selector_stride_from_blank

end CurrentAdditive.FiniteFieldConstructor.CanonicalTable
