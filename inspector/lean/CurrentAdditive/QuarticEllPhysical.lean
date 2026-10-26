import CurrentAdditive.QuarticCountValue
import Paper2.LMain
import Paper2.LQFront

/-! The old public graph-count machine already computes the unary logarithm
`ell` needed by the new quartic width machine. -/

namespace Paper2.CurrentAdditive.QuarticNumericFront

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding

theorem l_program_writes_ell (n : ℕ) :
    ∃ T ≤ LProducer.lBd n, ∃ vc, ∃ F : LProducer.LK → List Bool,
      ((advance LProducer.lProg)^[T])
        (⟨some LProducer.lStart, LProducer.lCtl, LProducer.L0 n⟩ :
          TM2.Cfg (fun _ : LProducer.LK => Bool) _ _) =
        ⟨none, vc, F⟩ ∧
      F (LProducer.outR 1) = List.replicate
        (RestorationWidthScheduleScratch.ell (Nat.clog 2 n)) true ∧
      CountFront.LFacts n F := by
  obtain ⟨T, hT, vc, F, hr, facts⟩ := LProducer.l_run n
  have hFacts : CountFront.LFacts n F := facts
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, g0, g1,
    hreg0, hreg1, hout0, hout1⟩ := facts
  refine ⟨T, hT, vc, F, hr, ?_, hFacts⟩
  have h := hreg1 (ETHParameterScaleMachineLogCopy.logStack
    ETHParameterScaleMachineLogCopy.logMachine.output)
  rw [hout1] at h
  simpa only [LProducer.outR, LProducer.u, RestorationWidthScheduleScratch.ell] using h

end Paper2.CurrentAdditive.QuarticNumericFront

#print axioms Paper2.CurrentAdditive.QuarticNumericFront.l_program_writes_ell
