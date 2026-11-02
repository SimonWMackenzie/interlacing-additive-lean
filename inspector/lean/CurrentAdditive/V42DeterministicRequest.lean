import CurrentAdditive.V40DeterministicRequest

/-! Literal v42 midpoint formatter for the retained weighted-state envelope.
For L=4k, one successful round has YES cost 10L=40k. -/
namespace CurrentAdditive.V42DeterministicRequest
noncomputable section
open Paper2 EthInapproximability.CurrentPaper EncodedCommunication
open V39GeneratedConstruction V40StoredOutputPrimitives PhysicalProducer
set_option maxHeartbeats 4000000
set_option maxRecDepth 32768
set_option synthInstance.maxSize 32768

def inputL := UnaryProducer.input (0 : Fin 3)
def inputK := UnaryProducer.input (1 : Fin 3)
def seedExponent := UnaryProducer.clog
  (UnaryProducer.binary .mul (UnaryProducer.constant 64)
    (UnaryProducer.binary .add inputL (UnaryProducer.constant 1)))
def stepCost := UnaryProducer.binary .mul (UnaryProducer.constant 10) inputL
def threshold := UnaryProducer.binary .add
  (UnaryProducer.binary .add seedExponent (UnaryProducer.constant 1))
  (UnaryProducer.binary .mul inputK stepCost)
def thresholdNumber (L K : ℕ) := LookupSeed.exponent L+1+K*(10*L)

theorem threshold_value (x : List Bool) : threshold.value x =
    thresholdNumber (BankFieldProjection.result (0 : Fin 3) x).length
      (BankFieldProjection.result (1 : Fin 3) x).length := rfl

def midpointUnary := UnaryProducer.binary .add
  (UnaryProducer.binary .mul (UnaryProducer.constant 2) threshold) inputK
def midpointField : Producer := compose midpointUnary.producer V40StoredThreshold.unaryField
def header : Producer := compose V40StoredEnvelope.route midpointField
def thresholdField : Producer := compose threshold.producer V40StoredThreshold.unaryField
def rectangleCore : Producer := concat V40StoredRectangle.rowHeader
  (concat V40StoredRectangle.colHeader (concat thresholdField V40StoredRectangle.cells))
def rectangle : Producer := compose V40StoredEnvelope.route rectangleCore
def rectangleInstance (L K : ℕ) (R : StoredMatrix) : Instance :=
  ⟨R.rows,R.cols,thresholdNumber L K,StoredWeightedState.cells R⟩

theorem rectangle_result (L K : ℕ) (ctx : List Bool) (R : StoredMatrix) :
    rectangle.result (V40StoredEnvelope.input L K ctx R)=
      encodeInstance (rectangleInstance L K R) := by
  change rectangleCore.result (V40StoredEnvelope.route.result (V40StoredEnvelope.input L K ctx R))=_
  rw [V40StoredEnvelope.route_result]
  change V40StoredRectangle.rowHeader.result _ ++ (V40StoredRectangle.colHeader.result _ ++
    (thresholdField.result _ ++ V40StoredRectangle.cells.result _))=_
  rw [V40StoredRectangle.row_result,V40StoredRectangle.col_result,V40StoredRectangle.cells_result]
  have hfield : thresholdField.result (V40StoredRectangle.input L K ctx R)=
      natField (thresholdNumber L K) := by
    change natField ((threshold.producer.result (V40StoredRectangle.input L K ctx R)).length)=_
    rw [threshold.result_eq,List.length_replicate,threshold_value]
    simp [V40StoredRectangle.input,V40StoredThreshold.input,BankFieldProjection.result_encode]
  rw [hfield]
  simp [encodeInstance,rectangleInstance,List.append_assoc]

theorem midpoint_result (L K : ℕ) (ctx : List Bool) (R : StoredMatrix) :
    header.result (V40StoredEnvelope.input L K ctx R)=natField (2*thresholdNumber L K+K) := by
  change midpointField.result (V40StoredEnvelope.route.result (V40StoredEnvelope.input L K ctx R))=_
  rw [V40StoredEnvelope.route_result]
  change natField ((midpointUnary.producer.result (V40StoredRectangle.input L K ctx R)).length)=_
  rw [midpointUnary.result_eq,List.length_replicate]
  change natField (2*(threshold.value (V40StoredRectangle.input L K ctx R))+
    inputK.value (V40StoredRectangle.input L K ctx R))=_
  rw [threshold_value]
  simp [inputK,UnaryProducer.input,V40StoredRectangle.input,V40StoredThreshold.input,
    BankFieldProjection.result_encode]

def request : Producer := concat header V40DeterministicRequest.square

theorem request_result (L K : ℕ) (ctx : List Bool) (R : StoredMatrix) :
    request.result (V40StoredEnvelope.input L K ctx R)=
      natField (2*thresholdNumber L K+K)++R.squareWord := by
  change header.result _ ++ V40DeterministicRequest.square.result _=_
  rw [midpoint_result,V40DeterministicRequest.square_result]

theorem outputs (L K : ℕ) (ctx : List Bool) (R : StoredMatrix) :
    request.machine.OutputsWithin (V40StoredEnvelope.input L K ctx R)
      (natField (2*thresholdNumber L K+K)++R.squareWord)
      (request.coefficient*((V40StoredEnvelope.input L K ctx R).length+1)^request.degree) := by
  simpa only [request_result] using request.outputs (V40StoredEnvelope.input L K ctx R)

theorem generated_threshold (k K : ℕ) :
    thresholdNumber (4*k) K = LookupSeed.exponent (4*k)+1+K*(40*k) := by
  unfold thresholdNumber
  ring

#print axioms outputs
#print axioms request
#print axioms rectangle_result
end
end CurrentAdditive.V42DeterministicRequest
