import CurrentAdditive.FeatureFinalStateProjection96

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

namespace CurrentAdditive.GenericFeatureFinalStateProjection
open EthInapproximability.CurrentPaper

/-- Exact pure serializer used by the dimension-indexed physical iteration. -/
def featuresAt (D j : Nat) (ys : List Nat) := CylinderOrderedSpec.generatedList j D ys
def states (D : Nat) (ys : List Nat) (carry : List Bool) (j : Nat) :=
  FeatureCoordinateTransition96.stateWord j ys (featuresAt D j ys) [] [] carry

/-- These physical parsers depend only on the fixed Fin96 layout. The
descriptor dimension changes the field contents, not their locations. -/
abbrev featureMachine := FeatureFinalStateProjection96.featureMachine
abbrev rawMachine := FeatureFinalStateProjection96.rawMachine
abbrev qMachine := FeatureFinalStateProjection96.qMachine
abbrev tupleMachine := FeatureFinalStateProjection96.tupleMachine

theorem feature_word (D q : Nat) (alphabet : Array Nat) :
    SourceListEncoding.encode (FeatureOldDescriptorFrame96.words
      (featuresAt D q alphabet.toList)) =
      CylinderFeatureCodec.generatedFeatureBits q D alphabet := by
  exact CylinderOrderedSpec.featurePacket_exact q D alphabet

theorem features_output (D q : Nat) (alphabet : Array Nat) (carry : List Bool) :
    featureMachine.OutputsWithin (states D alphabet.toList carry q)
      (CylinderFeatureCodec.generatedFeatureBits q D alphabet)
      (196 * ((states D alphabet.toList carry q).length + 1)) := by
  have h := BankFieldProjection.outputs (8 : Fin 96)
    (states D alphabet.toList carry q)
  simpa only [featureMachine, FeatureFinalStateProjection96.featureMachine,
    states, FeatureCoordinateTransition96.stateWord,
    BankFieldProjection.result_encode, FeatureFinalStateProjection96.feature_bank,
    feature_word] using h

theorem raw_output (D q : Nat) (ys : List Nat) (carry : List Bool) :
    rawMachine.OutputsWithin (states D ys carry q) carry
      (196 * ((states D ys carry q).length + 1)) := by
  have h := BankFieldProjection.outputs (29 : Fin 96)
    (states D ys carry q)
  simpa only [rawMachine, FeatureFinalStateProjection96.rawMachine,
    states, FeatureCoordinateTransition96.stateWord,
    BankFieldProjection.result_encode, FeatureFinalStateProjection96.raw_bank] using h

theorem q_output (D : Nat) {q : Nat} (alphabet : Array (Nat × ℚ))
    (source : Array ((Fin q → Nat) × ℚ)) :
    let raw := CylinderRawInputProjection.input alphabet source
    let state := states D (alphabet.map Prod.fst).toList raw q
    qMachine.OutputsWithin state (List.replicate q true)
      (196 * (state.length + 1) + 2 * raw.length + 2 + 10 * (raw.length + 1)) := by
  dsimp only
  exact BitMachineComposition.composition_outputsWithin _ _
    (raw_output D q (alphabet.map Prod.fst).toList (CylinderRawInputProjection.input alphabet source))
    (CylinderRawInputProjection.q_output alphabet source)

theorem tuples_output (D : Nat) {q : Nat} (alphabet : Array (Nat × ℚ))
    (source : Array ((Fin q → Nat) × ℚ)) :
    let raw := CylinderRawInputProjection.input alphabet source
    let state := states D (alphabet.map Prod.fst).toList raw q
    tupleMachine.OutputsWithin state
      (SourceListEncoding.encode (CylinderProductionProjection.tupleWords source))
      (196 * (state.length + 1) + 2 * raw.length + 2 +
        CylinderRawInputProjection.coefficient * (raw.length + 1) ^ 3) := by
  dsimp only
  exact BitMachineComposition.composition_outputsWithin _ _
    (raw_output D q (alphabet.map Prod.fst).toList (CylinderRawInputProjection.input alphabet source))
    (CylinderRawInputProjection.tuple_output_polynomial alphabet source)

end CurrentAdditive.GenericFeatureFinalStateProjection
