import CurrentAdditive.V42ActualSource
import CurrentAdditive.V40DeterministicSourcePack

/-! Actual v42 source printers. The fixed physical CNF compiler, public
parameter selector, seven-call iteration and literal request formatter are
composed here. Fixed-round polynomiality is derived, not a final premise. -/
namespace CurrentAdditive.V42SourcePhysical
noncomputable section
open Paper2 EthInapproximability.CurrentPaper EncodedCommunication
open EncodedETHSource EncodedETHSourceComposition Unit4Shell.T10Finite
open PhysicalProducer V40StoredOutputPrimitives
set_option maxHeartbeats 8000000
set_option maxRecDepth 65536

variable (D : DinurReduction) (B : BOTReduction (booleanOccurrence D))

def pipeline (P : Producer) := V42GraphRuntime.pipeline (V42ActualSource.k0 D B) P.machine
def exponent (P : Producer) := (V42GraphRuntime.sourceCoefficient (V42ActualSource.k0 D B)+1)*
  V42GraphRuntime.exponent (V42ActualSource.k0 D B) P.machine P.coefficient P.degree
def amplification := V42GraphRuntime.amplification (V42ActualSource.k0 D B)

theorem tail_outputs (P : Producer) (Φ : ValidFormula) (K : ℕ) :
    (pipeline D B P).OutputsWithin
      (V42RuntimePrefix.input (EncodedGraph.encode (t10Graph D B Φ)) K)
      (P.result (V42ActualSource.envelope D B Φ K))
      (((EncodedGraph.encode (t10Graph D B Φ)).length+1)^
        (exponent D B P*(amplification D B)^K)) := by
  have h := V42GraphRuntime.outputs_with_tail (V42ActualSource.k0 D B)
    P.machine P.coefficient P.degree (t10Graph D B Φ) (t10Graph_valid D B Φ) K
    (V42ActualSource.selected_two D B Φ) (V39CurrentSourceJoin.source_geometry D B Φ).1
    (V42GraphRuntime.selected_width B.degreeBound (V42ActualSource.k0 D B) (t10Graph D B Φ)
      (V39CurrentSourceJoin.source_geometry D B Φ).2.2 (V42ActualSource.k0_degree D B))
    _ (P.outputs (V42ActualSource.envelope D B Φ K))
  have hb := V42GraphRuntime.power_source_bound (V42ActualSource.k0 D B) (t10Graph D B Φ)
    (V42GraphRuntime.exponent (V42ActualSource.k0 D B) P.machine P.coefficient P.degree*
      (amplification D B)^K)
  have he : (V42GraphRuntime.sourceCoefficient (V42ActualSource.k0 D B)+1)*
      (V42GraphRuntime.exponent (V42ActualSource.k0 D B) P.machine P.coefficient P.degree*
        (amplification D B)^K)=exponent D B P*(amplification D B)^K := by
    unfold exponent
    ring
  rw [he] at hb
  exact BitMachine.outputsWithin_mono _ h.1 hb

def requestMachine := pipeline D B V42DeterministicRequest.request
def requestExponent := exponent D B V42DeterministicRequest.request

theorem request_outputs (Φ : ValidFormula) (K : ℕ) :
    (requestMachine D B).OutputsWithin
      (V42RuntimePrefix.input (EncodedGraph.encode (t10Graph D B Φ)) K)
      (V42ActualSource.request D B Φ K)
      (((EncodedGraph.encode (t10Graph D B Φ)).length+1)^
        (requestExponent D B*(amplification D B)^K)) := by
  have h := tail_outputs D B V42DeterministicRequest.request Φ K
  have he : V42DeterministicRequest.request.result (V42ActualSource.envelope D B Φ K)=
      V42ActualSource.request D B Φ K := by
    dsimp only [V42ActualSource.envelope,V42RuntimeWords.word]
    rw [V42DeterministicRequest.request_result,V42DeterministicRequest.generated_threshold]
    rfl
  rw [he] at h
  exact h

def rectangle (Φ : ValidFormula) (K : ℕ) : Instance :=
  V42DeterministicRequest.rectangleInstance (4*V42ActualSource.selected D B Φ) K
    (V42ActualSource.run D B Φ K)
def rectangleMachine := pipeline D B V42DeterministicRequest.rectangle
def rectangleExponent := exponent D B V42DeterministicRequest.rectangle

theorem rectangle_outputs (Φ : ValidFormula) (K : ℕ) :
    (rectangleMachine D B).OutputsWithin
      (V42RuntimePrefix.input (EncodedGraph.encode (t10Graph D B Φ)) K)
      (encodeInstance (rectangle D B Φ K))
      (((EncodedGraph.encode (t10Graph D B Φ)).length+1)^
        (rectangleExponent D B*(amplification D B)^K)) := by
  have h := tail_outputs D B V42DeterministicRequest.rectangle Φ K
  have he : V42DeterministicRequest.rectangle.result (V42ActualSource.envelope D B Φ K)=
      encodeInstance (rectangle D B Φ K) := by
    dsimp only [V42ActualSource.envelope,V42RuntimeWords.word]
    rw [V42DeterministicRequest.rectangle_result]
    rfl
  rw [he] at h
  exact h

def fixedFormula := V40DeterministicSourcePack.fixedFormula
def fixedFront (K : ℕ) : Producer := V40DeterministicSourcePack.bank3
  (V40DeterministicSourcePack.graph D B) (UnaryProducer.constant 0).producer
  (UnaryProducer.constant K).producer

theorem fixed_front_result (K : ℕ) (w : List Bool) :
    (fixedFront D B K).result w=
      V42RuntimePrefix.input (EncodedGraph.encode (t10Graph D B (fixedFormula w))) K := by
  rw [fixedFront,V40DeterministicSourcePack.bank3_result]
  rfl

private theorem pointwise_comp_poly (F : Producer) (M : BitMachine.Machine)
    (target : List Bool → List Bool) (d : ℕ)
    (h : ∀ w, M.OutputsWithin (F.result w) (target w) (((F.result w).length+1)^d)) :
    BitMachine.Polytime target := by
  refine ⟨BitMachineComposition.composition F.machine M,
    F.coefficient+2*(F.coefficient*F.machine.pushBound+1)+(F.coefficient*F.machine.pushBound+1)^d,
    (F.degree+1)*(d+1),?_⟩
  intro w
  have hr:=BitMachineComposition.composition_outputsWithin F.machine M (F.outputs w) (h w)
  apply BitMachine.outputsWithin_mono _ hr
  simpa only [one_mul] using BitMachineCompositionArithmetic.composition_time_bound w.length
    F.coefficient F.degree 1 d F.machine.pushBound (F.result w).length
    (BitMachine.output_length_bound F.machine (F.outputs w))

theorem requestSource_polytime (K : ℕ) :
    BitMachine.Polytime (fun w => V42ActualSource.request D B (fixedFormula w) K) := by
  apply pointwise_comp_poly (fixedFront D B K) (requestMachine D B) _
    (requestExponent D B*(amplification D B)^K)
  intro w
  have h := request_outputs D B (fixedFormula w) K
  rw [← fixed_front_result D B K w] at h
  apply BitMachine.outputsWithin_mono _ h
  apply Nat.pow_le_pow_left
  rw [fixed_front_result,V42RuntimePrefix.input_length]
  omega

theorem rectangleSource_polytime (K : ℕ) :
    BitMachine.Polytime (fun w => encodeInstance (rectangle D B (fixedFormula w) K)) := by
  apply pointwise_comp_poly (fixedFront D B K) (rectangleMachine D B) _
    (rectangleExponent D B*(amplification D B)^K)
  intro w
  have h := rectangle_outputs D B (fixedFormula w) K
  rw [← fixed_front_result D B K w] at h
  apply BitMachine.outputsWithin_mono _ h
  apply Nat.pow_le_pow_left
  rw [fixed_front_result,V42RuntimePrefix.input_length]
  omega

#print axioms request_outputs
#print axioms rectangle_outputs
#print axioms requestSource_polytime
#print axioms rectangleSource_polytime
end
end CurrentAdditive.V42SourcePhysical
