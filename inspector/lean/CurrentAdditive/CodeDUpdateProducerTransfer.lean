import CurrentAdditive.CodeDUpdateUnivariateClock
import CurrentAdditive.CodeDUpdateMaterializedBridge

/-! Composition boundary for any physical writer of the exact ordered
request packet. The concrete writer may be supplied later without changing
the arithmetic, updated-entry writer, or zero-filter machines. -/

namespace CurrentAdditive.CodeDUpdateProducerTransfer

open EthInapproximability.CurrentPaper
open CurrentAdditive.CodeDCanonicalSourceV2

theorem compose_exact {q : Nat}
    (producer : BitMachine.Machine) (input : List Bool)
    (source : Array ((Fin q → Nat) × ℚ)) (coeff : Array ℚ)
    (lambda : ℚ) (t : Nat)
    (hproducer : producer.OutputsWithin input
      (CodeDUpdateRequestABI.requestPacketList source coeff lambda) t)
    (hnonneg : (CodeDUpdatedArithmeticABI.candidateWeights source coeff lambda).all
      (fun w => decide (0 ≤ w)) = true) :
    (BitMachineComposition.composition producer
      CodeDUpdateFullPipeline.machine).OutputsWithin input
      (encodedSource
        (CodeDCompactSequentialBridge.retainedSource source
          (CodeDUpdatedArithmeticABI.candidateWeights source coeff lambda)))
      (t + 2*(CodeDUpdateRequestABI.requestPacketList source coeff lambda).length+2+
        CodeDUpdateFullPipeline.clock source coeff lambda) := by
  exact BitMachineComposition.composition_outputsWithin
    producer CodeDUpdateFullPipeline.machine hproducer
    (CodeDUpdateFullPipeline.outputs source coeff lambda hnonneg)

theorem composed_clock_le_input_envelope {q : Nat}
    (producer : BitMachine.Machine) (input : List Bool)
    (source : Array ((Fin q → Nat) × ℚ)) (coeff : Array ℚ)
    (lambda : ℚ) (t : Nat)
    (hproducer : producer.OutputsWithin input
      (CodeDUpdateRequestABI.requestPacketList source coeff lambda) t) :
    t + 2*(CodeDUpdateRequestABI.requestPacketList source coeff lambda).length+2+
        CodeDUpdateFullPipeline.clock source coeff lambda ≤
      t + 2*(input.length+t*producer.pushBound)+2+
        CodeDUpdateArithmeticClock.fullPipelineBound
          (input.length+t*producer.pushBound)
          (input.length+t*producer.pushBound) := by
  let m := (CodeDUpdateRequestABI.requestPacketList source coeff lambda).length
  let B := input.length+t*producer.pushBound
  have hsize : m ≤ B := BitMachine.output_length_bound producer hproducer
  have hc := CodeDUpdateUnivariateClock.valid_packet_clock_le
    source coeff lambda
  have hm := CodeDUpdateUnivariateClock.fullPipelineBound_mono m m B
    hsize hsize
  change CodeDUpdateFullPipeline.clock source coeff lambda ≤
    CodeDUpdateArithmeticClock.fullPipelineBound m m at hc
  have htwice : 2*m ≤ 2*B := Nat.mul_le_mul_left 2 hsize
  change t+2*m+2+CodeDUpdateFullPipeline.clock source coeff lambda ≤
    t+2*B+2+CodeDUpdateArithmeticClock.fullPipelineBound B B
  omega

#print axioms compose_exact
#print axioms composed_clock_le_input_envelope

end CurrentAdditive.CodeDUpdateProducerTransfer
