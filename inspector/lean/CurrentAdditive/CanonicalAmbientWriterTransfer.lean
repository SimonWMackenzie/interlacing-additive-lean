import CurrentAdditive.CanonicalAmbientFieldInputs

/-! A literal ambient three-stack copy stage for each writer input cell. The
source word and every foreign stack are preserved, and the copy clock charges
the entire transferred word. -/

noncomputable section

namespace CurrentAdditive.FiniteFieldConstructor.CanonicalAmbient

open Turing EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding

def writerTransferPlace (t N : ℕ)
    (source : Cell t N) (target : MatrixTableWriter.Stack 60)
    (hsourceTarget : source ≠ .writer target)
    (hsourceScratch : source ≠ .copyScratch 0) : Fin 3 ↪ Cell t N :=
  ⟨![source, .writer target, .copyScratch 0], by
    intro i j h
    fin_cases i <;> fin_cases j <;>
      simp_all [hsourceTarget, hsourceScratch]⟩

theorem physical_writer_transfer (t N : ℕ)
    (source : Cell t N) (target : MatrixTableWriter.Stack 60)
    (hsourceTarget : source ≠ .writer target)
    (hsourceScratch : source ≠ .copyScratch 0)
    (S : Cell t N → List Bool) (word : List Bool)
    (hsource : S source = word)
    (htarget : S (.writer target) = [])
    (hscratch : S (.copyScratch 0) = []) :
    ((advance (MatrixStage4ScalarPreparationOps.copyProgram
        (writerTransferPlace t N source target hsourceTarget hsourceScratch)))^[2*word.length+2])
      (⟨some BitMachineCopy.Label.scan, none, S⟩ :
        TM2.Cfg (fun _ : Cell t N => Bool) _ _) =
      ⟨none, none, Function.update S (.writer target) word⟩ := by
  have hrun := MatrixStage4ScalarPreparationOps.copy_run
    (writerTransferPlace t N source target hsourceTarget hsourceScratch)
    S (by simpa [writerTransferPlace] using hscratch)
  simpa [writerTransferPlace, hsource, htarget] using hrun

#print axioms physical_writer_transfer

end CurrentAdditive.FiniteFieldConstructor.CanonicalAmbient
