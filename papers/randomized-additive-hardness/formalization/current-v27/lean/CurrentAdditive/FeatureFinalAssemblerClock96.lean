import CurrentAdditive.FeatureFinalAssembler96
import CurrentAdditive.FeatureSeedClock96

namespace CurrentAdditive.FeatureFinalAssemblerClock96
noncomputable section
open EthInapproximability.CurrentPaper
open CurrentAdditive.MinimumRatioContext GaussCellPolynomialClock FeatureFinalAssembler96
set_option maxRecDepth 16384
set_option maxHeartbeats 1000000
attribute [local irreducible] PolynomialBound CylinderRawInputProjection.coefficient
  CylinderRawInputProjection.tupleMachine FeatureFinalStateProjection96.qMachine
  FeatureFinalStateProjection96.featureMachine FeatureFinalStateProjection96.tupleMachine

def tupleCap (n : Nat) := n+CylinderRawInputProjection.coefficient*(n+1)^3*CylinderRawInputProjection.tupleMachine.pushBound
def packetCap (n : Nat) := 2*(n+n+tupleCap n)+3
def clockCap (n : Nat) :=
  MachineInvokeFull.uniformBound Q (List.replicate n true) (qClock n n)+
  MachineInvokeFull.uniformBound F (List.replicate n true) (fClock n)+
  MachineInvokeFull.uniformBound T (List.replicate n true) (tClock n n)+
    (2*packetCap n+2)+3
attribute [local irreducible] tupleCap packetCap

theorem raw_length (q : Nat) (ys : List Nat) (raw : List Bool) :
    raw.length ≤ (FeatureGeneratedIteration96.states ys raw q).length := by
  have h := BitMachineBankCodec.word_length_le_encode
    (FeatureCoordinateStage96.initialBank q ys (FeatureGeneratedIteration96.featuresAt q ys) [] [] raw) 29
  simpa only [FeatureGeneratedIteration96.states,FeatureCoordinateTransition96.stateWord,
    FeatureFinalStateProjection96.raw_bank] using h

theorem feature_length (q : Nat) (alphabet : Array Nat) (raw : List Bool) :
    (CylinderFeatureCodec.generatedFeatureBits q 8192 alphabet).length ≤
      (FeatureGeneratedIteration96.states alphabet.toList raw q).length := by
  have h := BitMachineBankCodec.word_length_le_encode
    (FeatureCoordinateStage96.initialBank q alphabet.toList
      (FeatureGeneratedIteration96.featuresAt q alphabet.toList) [] [] raw) 8
  simpa only [FeatureGeneratedIteration96.states,FeatureCoordinateTransition96.stateWord,
    FeatureFinalStateProjection96.feature_bank,FeatureFinalStateProjection96.feature_word] using h

theorem tuple_length {q : Nat} (alphabet : Array (Nat × ℚ))
    (source : Array ((Fin q → Nat) × ℚ)) :
    let raw := CylinderRawInputProjection.input alphabet source
    let state := FeatureGeneratedIteration96.states (alphabet.map Prod.fst).toList raw q
    (SourceListEncoding.encode (CylinderProductionProjection.tupleWords source)).length ≤ tupleCap state.length := by
  let raw := CylinderRawInputProjection.input alphabet source
  let state := FeatureGeneratedIteration96.states (alphabet.map Prod.fst).toList raw q
  have hr : raw.length ≤ state.length := raw_length q _ raw
  have h := BitMachine.output_length_bound CylinderRawInputProjection.tupleMachine
    (CylinderRawInputProjection.tuple_output_polynomial alphabet source)
  apply h.trans
  change raw.length+CylinderRawInputProjection.coefficient*(raw.length+1)^3*
    CylinderRawInputProjection.tupleMachine.pushBound ≤ tupleCap state.length
  unfold tupleCap
  gcongr

theorem packet_length {q : Nat} (alphabet : Array (Nat × ℚ))
    (source : Array ((Fin q → Nat) × ℚ)) :
    let raw := CylinderRawInputProjection.input alphabet source
    let state := FeatureGeneratedIteration96.states (alphabet.map Prod.fst).toList raw q
    (packet q (CylinderFeatureCodec.generatedFeatureBits q 8192 (alphabet.map Prod.fst))
      (SourceListEncoding.encode (CylinderProductionProjection.tupleWords source))).length ≤ packetCap state.length := by
  let raw := CylinderRawInputProjection.input alphabet source
  let state := FeatureGeneratedIteration96.states (alphabet.map Prod.fst).toList raw q
  have hr : raw.length ≤ state.length := raw_length q _ raw
  have hq : q ≤ state.length := by
    have h : q ≤ raw.length := by
      simpa only [Matrix.cons_val_zero,List.length_replicate] using
        CylinderRawInputProjection.field_length_le alphabet source 0
    exact h.trans hr
  have hf := feature_length q (alphabet.map Prod.fst) raw
  change (CylinderFeatureCodec.generatedFeatureBits q 8192 (alphabet.map Prod.fst)).length ≤ state.length at hf
  have ht := tuple_length alphabet source
  change _ ≤ packetCap state.length
  rw [packet,BitMachineBankCodec.encode_length]
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,Matrix.cons_val_zero,Matrix.cons_val_succ,
    List.length_replicate,Nat.add_zero]
  unfold packetCap
  change (SourceListEncoding.encode (CylinderProductionProjection.tupleWords source)).length ≤ tupleCap state.length at ht
  omega

theorem clock_le {q : Nat} (alphabet : Array (Nat × ℚ))
    (source : Array ((Fin q → Nat) × ℚ)) :
    let raw := CylinderRawInputProjection.input alphabet source
    let state := FeatureGeneratedIteration96.states (alphabet.map Prod.fst).toList raw q
    clock state raw q (CylinderFeatureCodec.generatedFeatureBits q 8192 (alphabet.map Prod.fst))
      (SourceListEncoding.encode (CylinderProductionProjection.tupleWords source)) ≤ clockCap state.length := by
  let raw := CylinderRawInputProjection.input alphabet source
  let state := FeatureGeneratedIteration96.states (alphabet.map Prod.fst).toList raw q
  have hr : raw.length ≤ state.length := raw_length q _ raw
  have hq : qClock state.length raw.length ≤ qClock state.length state.length := by unfold qClock; omega
  have ht : tClock state.length raw.length ≤ tClock state.length state.length := by unfold tClock; gcongr
  have hmQ := FeatureSeedClock96.invocation_mono Q state (List.replicate state.length true)
    _ _ (by simp only [List.length_replicate]; exact le_rfl) hq
  have hmT := FeatureSeedClock96.invocation_mono T state (List.replicate state.length true)
    _ _ (by simp only [List.length_replicate]; exact le_rfl) ht
  have hp := packet_length alphabet source
  change clock state raw q _ _ ≤ clockCap state.length
  change (packet q _ _).length ≤ packetCap state.length at hp
  unfold clock clockCap
  simp only [MachineInvokeFull.uniformBound,List.length_replicate] at hmQ hmT ⊢
  omega

theorem clock_polynomial : PolynomialBound (fun _ n => clockCap n) := by
  have htuple : PolynomialBound (fun _ n => tupleCap n) := by
    unfold tupleCap
    exact add second (mul (mul (constant CylinderRawInputProjection.coefficient)
      (power (add second (constant 1)) 3)) (constant _))
  have hpacket : PolynomialBound (fun _ n => packetCap n) := by
    unfold packetCap
    exact add (mul (constant 2) (add (add second second) htuple)) (constant 3)
  have hq : PolynomialBound (fun _ n => qClock n n) := by
    unfold qClock
    repeat' first | exact second | exact (constant _) | apply add | apply mul
  have hf : PolynomialBound (fun _ n => fClock n) := by
    unfold fClock
    exact mul (constant 196) (add second (constant 1))
  have ht : PolynomialBound (fun _ n => tClock n n) := by
    unfold tClock
    exact add (add (add hf (mul (constant 2) second)) (constant 2))
      (mul (constant CylinderRawInputProjection.coefficient) (power (add second (constant 1)) 3))
  have hiQ := uniform_invocation Q second hq
  have hiF := uniform_invocation F second hf
  have hiT := uniform_invocation T second ht
  unfold clockCap
  exact add (add (add (add hiQ hiF) hiT) (add (mul (constant 2) hpacket) (constant 2))) (constant 3)

theorem exists_clock_bound : ∃ C e : Nat, ∀ s n,clockCap n ≤ C*(s+n+1)^e := by
  have h := clock_polynomial
  unfold PolynomialBound at h
  exact h
def coefficient : Nat := exists_clock_bound.choose
def exponent : Nat := exists_clock_bound.choose_spec.choose
theorem cap_polynomial (n : Nat) : clockCap n ≤ coefficient*(n+1)^exponent := by
  simpa only [coefficient,exponent,Nat.zero_add] using exists_clock_bound.choose_spec.choose_spec 0 n

/-- Fixed control and one polynomial in the actual complete input stateword.
No projected field, prepared state, run, or output-size bound is supplied. -/
theorem outputs_polynomial {q : Nat} (alphabet : Array (Nat × ℚ))
    (source : Array ((Fin q → Nat) × ℚ)) :
    let raw := CylinderRawInputProjection.input alphabet source
    let state := FeatureGeneratedIteration96.states (alphabet.map Prod.fst).toList raw q
    machine.OutputsWithin state
      (packet q (CylinderFeatureCodec.generatedFeatureBits q 8192 (alphabet.map Prod.fst))
        (SourceListEncoding.encode (CylinderProductionProjection.tupleWords source)))
      (coefficient*(state.length+1)^exponent) :=
  BitMachine.outputsWithin_mono _ (outputs alphabet source)
    ((clock_le alphabet source).trans (cap_polynomial _))

#print axioms raw_length
#print axioms packet_length
#print axioms clock_le
#print axioms clock_polynomial
#print axioms outputs_polynomial
end
end CurrentAdditive.FeatureFinalAssemblerClock96
