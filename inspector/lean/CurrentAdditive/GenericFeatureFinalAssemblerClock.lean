import CurrentAdditive.GenericFeatureFinalAssembler
import CurrentAdditive.FeatureFinalAssemblerClock96

namespace CurrentAdditive.GenericFeatureFinalAssemblerClock
noncomputable section
open EthInapproximability.CurrentPaper
open CurrentAdditive.MinimumRatioContext GaussCellPolynomialClock GenericFeatureFinalAssembler
set_option maxRecDepth 16384
set_option maxHeartbeats 1000000
attribute [local irreducible] PolynomialBound CylinderRawInputProjection.coefficient
  CylinderRawInputProjection.tupleMachine FeatureFinalStateProjection96.qMachine
  FeatureFinalStateProjection96.featureMachine FeatureFinalStateProjection96.tupleMachine

abbrev tupleCap := FeatureFinalAssemblerClock96.tupleCap
abbrev packetCap := FeatureFinalAssemblerClock96.packetCap
abbrev clockCap := FeatureFinalAssemblerClock96.clockCap

theorem raw_length (D : Nat) (q : Nat) (ys : List Nat) (raw : List Bool) :
    raw.length ≤ (GenericFeatureFinalStateProjection.states D ys raw q).length := by
  have h := BitMachineBankCodec.word_length_le_encode
    (FeatureCoordinateStage96.initialBank q ys (GenericFeatureFinalStateProjection.featuresAt D q ys) [] [] raw) 29
  simpa only [GenericFeatureFinalStateProjection.states,FeatureCoordinateTransition96.stateWord,
    FeatureFinalStateProjection96.raw_bank] using h

theorem feature_length (D : Nat) (q : Nat) (alphabet : Array Nat) (raw : List Bool) :
    (CylinderFeatureCodec.generatedFeatureBits q D alphabet).length ≤
      (GenericFeatureFinalStateProjection.states D alphabet.toList raw q).length := by
  have h := BitMachineBankCodec.word_length_le_encode
    (FeatureCoordinateStage96.initialBank q alphabet.toList
      (GenericFeatureFinalStateProjection.featuresAt D q alphabet.toList) [] [] raw) 8
  simpa only [GenericFeatureFinalStateProjection.states,FeatureCoordinateTransition96.stateWord,
    FeatureFinalStateProjection96.feature_bank,GenericFeatureFinalStateProjection.feature_word] using h

theorem tuple_length (D : Nat) {q : Nat} (alphabet : Array (Nat × ℚ))
    (source : Array ((Fin q → Nat) × ℚ)) :
    let raw := CylinderRawInputProjection.input alphabet source
    let state := GenericFeatureFinalStateProjection.states D (alphabet.map Prod.fst).toList raw q
    (SourceListEncoding.encode (CylinderProductionProjection.tupleWords source)).length ≤ tupleCap state.length := by
  let raw := CylinderRawInputProjection.input alphabet source
  let state := GenericFeatureFinalStateProjection.states D (alphabet.map Prod.fst).toList raw q
  have hr : raw.length ≤ state.length := raw_length D q _ raw
  have h := BitMachine.output_length_bound CylinderRawInputProjection.tupleMachine
    (CylinderRawInputProjection.tuple_output_polynomial alphabet source)
  apply h.trans
  change raw.length+CylinderRawInputProjection.coefficient*(raw.length+1)^3*
    CylinderRawInputProjection.tupleMachine.pushBound ≤ tupleCap state.length
  unfold tupleCap FeatureFinalAssemblerClock96.tupleCap
  gcongr

theorem packet_length (D : Nat) {q : Nat} (alphabet : Array (Nat × ℚ))
    (source : Array ((Fin q → Nat) × ℚ)) :
    let raw := CylinderRawInputProjection.input alphabet source
    let state := GenericFeatureFinalStateProjection.states D (alphabet.map Prod.fst).toList raw q
    (packet q (CylinderFeatureCodec.generatedFeatureBits q D (alphabet.map Prod.fst))
      (SourceListEncoding.encode (CylinderProductionProjection.tupleWords source))).length ≤ packetCap state.length := by
  let raw := CylinderRawInputProjection.input alphabet source
  let state := GenericFeatureFinalStateProjection.states D (alphabet.map Prod.fst).toList raw q
  have hr : raw.length ≤ state.length := raw_length D q _ raw
  have hq : q ≤ state.length := by
    have h : q ≤ raw.length := by
      simpa only [Matrix.cons_val_zero,List.length_replicate] using
        CylinderRawInputProjection.field_length_le alphabet source 0
    exact h.trans hr
  have hf := feature_length D q (alphabet.map Prod.fst) raw
  change (CylinderFeatureCodec.generatedFeatureBits q D (alphabet.map Prod.fst)).length ≤ state.length at hf
  have ht := tuple_length D alphabet source
  change _ ≤ packetCap state.length
  rw [packet,FeatureFinalAssembler96.packet,BitMachineBankCodec.encode_length]
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,Matrix.cons_val_zero,Matrix.cons_val_succ,
    List.length_replicate,Nat.add_zero]
  unfold packetCap FeatureFinalAssemblerClock96.packetCap
  change (SourceListEncoding.encode (CylinderProductionProjection.tupleWords source)).length ≤ tupleCap state.length at ht
  dsimp only [tupleCap] at ht
  omega

theorem clock_le (D : Nat) {q : Nat} (alphabet : Array (Nat × ℚ))
    (source : Array ((Fin q → Nat) × ℚ)) :
    let raw := CylinderRawInputProjection.input alphabet source
    let state := GenericFeatureFinalStateProjection.states D (alphabet.map Prod.fst).toList raw q
    clock D state raw q (CylinderFeatureCodec.generatedFeatureBits q D (alphabet.map Prod.fst))
      (SourceListEncoding.encode (CylinderProductionProjection.tupleWords source)) ≤ clockCap state.length := by
  let raw := CylinderRawInputProjection.input alphabet source
  let state := GenericFeatureFinalStateProjection.states D (alphabet.map Prod.fst).toList raw q
  have hr : raw.length ≤ state.length := raw_length D q _ raw
  have hq : qClock state.length raw.length ≤ qClock state.length state.length := by unfold qClock FeatureFinalAssembler96.qClock; omega
  have ht : tClock state.length raw.length ≤ tClock state.length state.length := by unfold tClock FeatureFinalAssembler96.tClock; gcongr
  have hmQ := FeatureSeedClock96.invocation_mono Q state (List.replicate state.length true)
    _ _ (by simp only [List.length_replicate]; exact le_rfl) hq
  have hmT := FeatureSeedClock96.invocation_mono T state (List.replicate state.length true)
    _ _ (by simp only [List.length_replicate]; exact le_rfl) ht
  have hp := packet_length D alphabet source
  change clock D state raw q _ _ ≤ clockCap state.length
  change (packet q _ _).length ≤ packetCap state.length at hp
  unfold clock FeatureFinalAssembler96.clock clockCap FeatureFinalAssemblerClock96.clockCap
  dsimp only [GenericFeatureFinalAssembler.Q,GenericFeatureFinalAssembler.F,
    GenericFeatureFinalAssembler.T,GenericFeatureFinalAssembler.packet,
    GenericFeatureFinalAssembler.qClock,GenericFeatureFinalAssembler.fClock,
    GenericFeatureFinalAssembler.tClock] at hmQ hmT hp ⊢
  dsimp only [packetCap] at hp
  simp only [MachineInvokeFull.uniformBound,List.length_replicate] at hmQ hmT ⊢
  omega

theorem clock_polynomial : PolynomialBound (fun _ n => clockCap n) :=
  FeatureFinalAssemblerClock96.clock_polynomial

def coefficient (_D : Nat) := FeatureFinalAssemblerClock96.coefficient
def exponent (_D : Nat) := FeatureFinalAssemblerClock96.exponent

theorem cap_polynomial (D n : Nat) : clockCap n ≤ coefficient D*(n+1)^exponent D :=
  FeatureFinalAssemblerClock96.cap_polynomial n

/-- Fixed control and one polynomial in the actual complete input stateword.
No projected field, prepared state, run, or output-size bound is supplied. -/
theorem outputs_polynomial (D : Nat) {q : Nat} (alphabet : Array (Nat × ℚ))
    (source : Array ((Fin q → Nat) × ℚ)) :
    let raw := CylinderRawInputProjection.input alphabet source
    let state := GenericFeatureFinalStateProjection.states D (alphabet.map Prod.fst).toList raw q
    (machine D).OutputsWithin state
      (packet q (CylinderFeatureCodec.generatedFeatureBits q D (alphabet.map Prod.fst))
        (SourceListEncoding.encode (CylinderProductionProjection.tupleWords source)))
      (coefficient D*(state.length+1)^exponent D) :=
  BitMachine.outputsWithin_mono _ (outputs D alphabet source)
    ((clock_le D alphabet source).trans (cap_polynomial D _))

#print axioms raw_length
#print axioms packet_length
#print axioms clock_le
#print axioms clock_polynomial
#print axioms outputs_polynomial
end
end CurrentAdditive.GenericFeatureFinalAssemblerClock
