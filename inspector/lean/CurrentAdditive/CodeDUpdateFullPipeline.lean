import CurrentAdditive.CodeDUpdateFinalPairList
import CurrentAdditive.CodeDUpdatedCompactPipeline
import EthInapproximability.CurrentPaper.BitMachineComposition

/-! Physical arithmetic update, entry rewrite, and zero deletion from an ordered request list. -/

namespace CurrentAdditive.CodeDUpdateFullPipeline

open EthInapproximability.CurrentPaper
open CodeDUpdateRequestABI CodeDSourceCodecV2 CodeDCanonicalSourceV2

noncomputable def machine : BitMachine.Machine :=
  BitMachineComposition.composition
    CodeDUpdateFinalPairList.machine CodeDUpdatedCompactPipeline.machine

noncomputable def clock {q : Nat}
    (source : Array ((Fin q → Nat) × ℚ)) (coeff : Array ℚ)
    (lambda : ℚ) : Nat :=
  let requests := requestItems source coeff lambda
  let updated := CodeDUpdatedArithmeticABI.candidateWeights source coeff lambda
  CodeDUpdateFinalPairList.clock requests +
    2*(CodeDCodecV2.encodeItems
      (CodeDUpdatedEntryList.pairItems source updated)).length+2 +
    CodeDUpdatedCompactPipeline.clock source updated

theorem outputs {q : Nat}
    (source : Array ((Fin q → Nat) × ℚ)) (coeff : Array ℚ)
    (lambda : ℚ)
    (hnonneg : (CodeDUpdatedArithmeticABI.candidateWeights source coeff lambda).all
      (fun w => decide (0 ≤ w)) = true) :
    machine.OutputsWithin
      (requestPacketList source coeff lambda)
      (encodedSource
        (CodeDCompactSequentialBridge.retainedSource source
          (CodeDUpdatedArithmeticABI.candidateWeights source coeff lambda)))
      (clock source coeff lambda) := by
  let updated := CodeDUpdatedArithmeticABI.candidateWeights source coeff lambda
  have h₁ := CodeDUpdateFinalPairList.writes_pairItems source coeff lambda
  have h₂ := CodeDUpdatedCompactPipeline.outputs source updated hnonneg
  have h := BitMachineComposition.composition_outputsWithin
    CodeDUpdateFinalPairList.machine CodeDUpdatedCompactPipeline.machine
    h₁ h₂
  simpa only [machine, clock, updated] using h

#print axioms outputs

end CurrentAdditive.CodeDUpdateFullPipeline
