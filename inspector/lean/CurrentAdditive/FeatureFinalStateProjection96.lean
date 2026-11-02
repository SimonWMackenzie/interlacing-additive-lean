import CurrentAdditive.FeatureGeneratedIteration96
import CurrentAdditive.CylinderRawInputProjection

/-! Actual projections from the final packed state. They recover the feature
packet and the retained original source word through physical bank parsers. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxSize 65536
set_option maxRecDepth 4096
namespace CurrentAdditive.FeatureFinalStateProjection96
open EthInapproximability.CurrentPaper

def featureMachine : BitMachine.Machine := BankFieldProjection.machine (8 : Fin 96)
def rawMachine : BitMachine.Machine := BankFieldProjection.machine (29 : Fin 96)
def qMachine : BitMachine.Machine :=
  BitMachineComposition.composition rawMachine CylinderRawInputProjection.qMachine
def tupleMachine : BitMachine.Machine :=
  BitMachineComposition.composition rawMachine CylinderRawInputProjection.tupleMachine

theorem feature_bank (j : Nat) (ys : List Nat) (cs : List (List (Nat × Nat)))
    (qfuel jUnary carry : List Bool) :
    FeatureCoordinateStage96.initialBank j ys cs qfuel jUnary carry 8=
      SourceListEncoding.encode (FeatureOldDescriptorFrame96.words cs) :=
  FeatureCoordinateBank96.frame_low _ _ _ _ _ _ 8

theorem raw_bank (j : Nat) (ys : List Nat) (cs : List (List (Nat × Nat)))
    (qfuel jUnary carry : List Bool) :
    FeatureCoordinateStage96.initialBank j ys cs qfuel jUnary carry 29=carry := by
  have h := FeatureCoordinateBank96.frame_high
    (SourceListEncoding.encode (FeatureOldDescriptorFrame96.words cs))
    (SourceListEncoding.fields (FeatureOldDescriptorFrame96.words cs))
    (List.replicate cs.length true) 0 cs.length
    (FeatureOldDescriptorFrame96.extra j ys qfuel jUnary carry) 29 (by decide)
  simpa [FeatureCoordinateStage96.initialBank,FeatureOldDescriptorFrame96.extra] using h

theorem feature_word (q : Nat) (alphabet : Array Nat) :
    SourceListEncoding.encode (FeatureOldDescriptorFrame96.words
      (FeatureGeneratedIteration96.featuresAt q alphabet.toList))=
    CylinderFeatureCodec.generatedFeatureBits q 8192 alphabet := by
  exact CylinderOrderedSpec.featurePacket_exact q 8192 alphabet

theorem features_output (q : Nat) (alphabet : Array Nat) (carry : List Bool) :
    featureMachine.OutputsWithin (FeatureGeneratedIteration96.states alphabet.toList carry q)
      (CylinderFeatureCodec.generatedFeatureBits q 8192 alphabet)
      (196*((FeatureGeneratedIteration96.states alphabet.toList carry q).length+1)) := by
  have h := BankFieldProjection.outputs (8 : Fin 96)
    (FeatureGeneratedIteration96.states alphabet.toList carry q)
  simpa only [featureMachine,FeatureGeneratedIteration96.states,
    FeatureCoordinateTransition96.stateWord,BankFieldProjection.result_encode,
    feature_bank,feature_word] using h

theorem raw_output (q : Nat) (ys : List Nat) (carry : List Bool) :
    rawMachine.OutputsWithin (FeatureGeneratedIteration96.states ys carry q) carry
      (196*((FeatureGeneratedIteration96.states ys carry q).length+1)) := by
  have h := BankFieldProjection.outputs (29 : Fin 96)
    (FeatureGeneratedIteration96.states ys carry q)
  simpa only [rawMachine,FeatureGeneratedIteration96.states,
    FeatureCoordinateTransition96.stateWord,BankFieldProjection.result_encode,raw_bank] using h

theorem q_output {q : Nat} (alphabet : Array (Nat × ℚ))
    (source : Array ((Fin q → Nat) × ℚ)) :
    let raw := CylinderRawInputProjection.input alphabet source
    let state := FeatureGeneratedIteration96.states (alphabet.map Prod.fst).toList raw q
    qMachine.OutputsWithin state (List.replicate q true)
      (196*(state.length+1)+2*raw.length+2+10*(raw.length+1)) := by
  dsimp only
  exact BitMachineComposition.composition_outputsWithin _ _
    (raw_output q (alphabet.map Prod.fst).toList (CylinderRawInputProjection.input alphabet source))
    (CylinderRawInputProjection.q_output alphabet source)

theorem tuples_output {q : Nat} (alphabet : Array (Nat × ℚ))
    (source : Array ((Fin q → Nat) × ℚ)) :
    let raw := CylinderRawInputProjection.input alphabet source
    let state := FeatureGeneratedIteration96.states (alphabet.map Prod.fst).toList raw q
    tupleMachine.OutputsWithin state
      (SourceListEncoding.encode (CylinderProductionProjection.tupleWords source))
      (196*(state.length+1)+2*raw.length+2+
        CylinderRawInputProjection.coefficient*(raw.length+1)^3) := by
  dsimp only
  exact BitMachineComposition.composition_outputsWithin _ _
    (raw_output q (alphabet.map Prod.fst).toList (CylinderRawInputProjection.input alphabet source))
    (CylinderRawInputProjection.tuple_output_polynomial alphabet source)

#print axioms features_output
#print axioms tuples_output
end CurrentAdditive.FeatureFinalStateProjection96
