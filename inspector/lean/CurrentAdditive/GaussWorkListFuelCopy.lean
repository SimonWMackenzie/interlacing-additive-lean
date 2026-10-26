import CurrentAdditive.GaussWorkListFuel
import EthInapproximability.CurrentPaper.ExactParameterBranchInstall

/-! Copy the retained source width into the disposable unary loop fuel.
The source width remains available for the final counted-list header. -/

namespace CurrentAdditive.GaussWorkListFuelCopy

open Turing Turing.TM2 EthInapproximability.CurrentPaper BitMachineEncoding

abbrev Bank := GaussWorkListFuel.Bank

noncomputable def slots : Fin 3 ↪ Bank :=
  ⟨![⟨3, by omega⟩, ⟨5, by omega⟩, ⟨12, by omega⟩], by
    intro a b h
    fin_cases a <;> fin_cases b <;> simp_all⟩

noncomputable def program := ExactParameterBranchInstall.copyProgram slots

theorem physical_fuel (S : Bank → List Bool) (k : Nat)
    (hwidth : S ⟨3, by omega⟩ = List.replicate k true)
    (h5 : S ⟨5, by omega⟩ = [])
    (h12 : S ⟨12, by omega⟩ = []) :
    ∃ t ≤ 2 * k + 2,
      ((advance program)^[t])
        (⟨some BitMachineCopy.Label.scan, none, S⟩ :
          TM2.Cfg (fun _ : Bank => Bool) _ _) =
      ⟨none, none, Function.update S ⟨5, by omega⟩
        (List.replicate k true)⟩ := by
  simpa only [program, slots, List.length_replicate] using
    ExactParameterBranchInstall.copy_run slots S (List.replicate k true)
      hwidth h5 h12

#print axioms physical_fuel

end CurrentAdditive.GaussWorkListFuelCopy
