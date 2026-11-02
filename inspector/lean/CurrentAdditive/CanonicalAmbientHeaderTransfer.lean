import CurrentAdditive.CanonicalAmbientThresholdRun

/-! A literal ambient copy stage for each encoded header input. -/

noncomputable section

namespace CurrentAdditive.FiniteFieldConstructor.CanonicalAmbient

open Turing EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding

def headerTransferPlace (t N : ℕ)
    (source : Cell t N) (target : Paper2.HeaderA.HB)
    (hsourceTarget : source ≠ .header target)
    (hsourceScratch : source ≠ .copyScratch 0) : Fin 3 ↪ Cell t N :=
  ⟨![source, .header target, .copyScratch 0], by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all⟩

theorem physical_header_transfer (t N : ℕ)
    (source : Cell t N) (target : Paper2.HeaderA.HB)
    (hsourceTarget : source ≠ .header target)
    (hsourceScratch : source ≠ .copyScratch 0)
    (S : Cell t N → List Bool) (word : List Bool)
    (hsource : S source = word)
    (htarget : S (.header target) = [])
    (hscratch : S (.copyScratch 0) = []) :
    ((advance (MatrixStage4ScalarPreparationOps.copyProgram
        (headerTransferPlace t N source target hsourceTarget hsourceScratch)))^[2*word.length+2])
      (⟨some BitMachineCopy.Label.scan, none, S⟩ :
        TM2.Cfg (fun _ : Cell t N => Bool) _ _) =
      ⟨none, none, Function.update S (.header target) word⟩ := by
  have hrun := MatrixStage4ScalarPreparationOps.copy_run
    (headerTransferPlace t N source target hsourceTarget hsourceScratch)
    S (by simpa [headerTransferPlace] using hscratch)
  simpa [headerTransferPlace, hsource, htarget] using hrun

#print axioms physical_header_transfer

end CurrentAdditive.FiniteFieldConstructor.CanonicalAmbient
