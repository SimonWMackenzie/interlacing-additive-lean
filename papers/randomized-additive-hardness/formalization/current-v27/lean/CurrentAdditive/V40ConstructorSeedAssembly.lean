import CurrentAdditive.V40ConstructorComposition
import CurrentAdditive.V40ConstructorRoundPacket
import CurrentAdditive.D22StepContextAssembly
import CurrentAdditive.V40WeightedSeedClock

namespace CurrentAdditive.V40ConstructorSeedAssembly
noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 65536
open EthInapproximability.CurrentPaper V39GeneratedConstruction

def seedCoefficient := Classical.choose V40WeightedSeed.outputs_polynomial
def seedDegree := Classical.choose (Classical.choose_spec V40WeightedSeed.outputs_polynomial)
theorem seed_outputs (context : List Bool) (L : Nat) (hL : 2≤L) :
    V40WeightedSeed.machine.OutputsWithin (V40WeightedSeed.packet context (List.replicate L true))
      (V40WeightedSeed.packet context (StoredWeightedState.encode (storedLookupSeed L)))
      (seedCoefficient*(context.length+2^L+1)^seedDegree) :=
  Classical.choose_spec (Classical.choose_spec V40WeightedSeed.outputs_polynomial) context L hL

def machine := BitMachineComposition.composition D22StepContextAssembly.seedInputMachine
  V40WeightedSeed.machine
def coefficient := V40ConstructorComposition.coefficient
  D22StepContextAssembly.seedExpr.timeCoefficient D22StepContextAssembly.seedExpr.timeDegree
  seedCoefficient seedDegree D22StepContextAssembly.seedInputMachine.pushBound 1
def degree := V40ConstructorComposition.degree D22StepContextAssembly.seedExpr.timeDegree seedDegree

/-- The actual source packet is routed to the actual weighted seed printer.
All seed cells, counts and canonical uniform laws are computed physically. -/
theorem outputs (graph : List Bool) (n m L K : Nat) (law activity : List Bool) (hL : 2≤L) :
    machine.OutputsWithin (D22PostSearchPacket.withSource graph n m L K law activity)
      (V40StoredEnvelope.input L K (D22PostSearchPacket.stepContext L law activity) (storedLookupSeed L))
      (coefficient*(2^L+(D22PostSearchPacket.withSource graph n m L K law activity).length+1)^degree) := by
  have ha := D22StepContextAssembly.seed_input_outputs graph n m L K law activity
  have hs := seed_outputs (D22PostSearchPacket.envelope L K law activity) L hL
  simp only [V40WeightedSeed.packet_eq] at hs
  change V40WeightedSeed.machine.OutputsWithin (D22StepContextAssembly.seedInput L K law activity)
    (V40StoredEnvelope.input L K (D22PostSearchPacket.stepContext L law activity) (storedLookupSeed L))
    (seedCoefficient*((D22PostSearchPacket.envelope L K law activity).length+2^L+1)^seedDegree) at hs
  have hctx : (D22PostSearchPacket.envelope L K law activity).length≤
      (D22StepContextAssembly.seedInput L K law activity).length := by
    simp [D22StepContextAssembly.seedInput,BitMachineBankCodec.encode_length,Fin.sum_univ_succ] <;> omega
  have hs' := BitMachine.outputsWithin_mono V40WeightedSeed.machine hs
    (Nat.mul_le_mul_left seedCoefficient (Nat.pow_le_pow_left
      (show (D22PostSearchPacket.envelope L K law activity).length+2^L+1≤
        2^L+(D22StepContextAssembly.seedInput L K law activity).length+1 by omega) seedDegree))
  have h := BitMachineComposition.composition_outputsWithin D22StepContextAssembly.seedInputMachine
    V40WeightedSeed.machine ha hs'
  have hm := BitMachine.output_length_bound D22StepContextAssembly.seedInputMachine ha
  apply BitMachine.outputsWithin_mono _ h
  exact V40ConstructorComposition.time_bound
    (2^L+(D22PostSearchPacket.withSource graph n m L K law activity).length)
    D22StepContextAssembly.seedExpr.timeCoefficient D22StepContextAssembly.seedExpr.timeDegree
    seedCoefficient seedDegree D22StepContextAssembly.seedInputMachine.pushBound 1 (2^L)
    (D22StepContextAssembly.seedInput L K law activity).length
    (by omega) (hm.trans (Nat.add_le_add_right (Nat.le_add_left _ _) _))

def roundMachine := BitMachineComposition.composition machine V40ConstructorRoundPacket.packet.machine
def roundCoefficient := V40ConstructorComposition.coefficient coefficient degree
  V40ConstructorRoundPacket.packet.coefficient V40ConstructorRoundPacket.packet.degree machine.pushBound 0
def roundDegree := V40ConstructorComposition.degree degree V40ConstructorRoundPacket.packet.degree

theorem round_outputs (graph : List Bool) (n m L K : Nat) (law activity : List Bool) (hL : 2≤L) :
    roundMachine.OutputsWithin (D22PostSearchPacket.withSource graph n m L K law activity)
      (WeightedIterationDriver.input
        (V40StoredEnvelope.input L K (D22PostSearchPacket.stepContext L law activity) (storedLookupSeed L)) K)
      (roundCoefficient*(2^L+(D22PostSearchPacket.withSource graph n m L K law activity).length+1)^roundDegree) := by
  have hs := outputs graph n m L K law activity hL
  have hp := V40ConstructorRoundPacket.outputs L K (D22PostSearchPacket.stepContext L law activity)
    (storedLookupSeed L)
  have h := BitMachineComposition.composition_outputsWithin machine
    V40ConstructorRoundPacket.packet.machine hs hp
  have hm := BitMachine.output_length_bound machine hs
  apply BitMachine.outputsWithin_mono _ h
  simpa only [Nat.zero_add] using V40ConstructorComposition.time_bound
    (2^L+(D22PostSearchPacket.withSource graph n m L K law activity).length)
    coefficient degree V40ConstructorRoundPacket.packet.coefficient V40ConstructorRoundPacket.packet.degree
    machine.pushBound 0 0
    (V40StoredEnvelope.input L K (D22PostSearchPacket.stepContext L law activity) (storedLookupSeed L)).length
    (by omega) (hm.trans (Nat.add_le_add_right (Nat.le_add_left _ _) _))

#print axioms outputs
#print axioms round_outputs
end
end CurrentAdditive.V40ConstructorSeedAssembly
