import CurrentAdditive.V40StoredEnvelope
import CurrentAdditive.V40BoundedFormatter

/-! A fixed physical request formatter on the retained weighted-state
input. The midpoint is computed from its actual unary L/K parameters and
the square word is preserved exactly. No threshold or desired run is input. -/
namespace CurrentAdditive.V40DeterministicRequest
noncomputable section
open Paper2 EthInapproximability.CurrentPaper EncodedCommunication
open V39GeneratedConstruction V40StoredOutputPrimitives PhysicalProducer
set_option maxHeartbeats 4000000
set_option maxRecDepth 32768
set_option synthInstance.maxSize 32768

def midpointUnary := UnaryProducer.binary .add
  (UnaryProducer.binary .mul (UnaryProducer.constant 2) V40StoredThreshold.threshold)
  V40StoredThreshold.inputK

def midpointField : Producer := compose midpointUnary.producer V40StoredThreshold.unaryField

def header : Producer := compose V40StoredEnvelope.route midpointField

theorem midpoint_result (L K : ℕ) (ctx : List Bool) (R : StoredMatrix) :
    header.result (V40StoredEnvelope.input L K ctx R)=
      natField (2*V40StoredThreshold.thresholdNumber L K+K) := by
  change midpointField.result (V40StoredEnvelope.route.result (V40StoredEnvelope.input L K ctx R))=_
  rw [V40StoredEnvelope.route_result]
  change natField ((midpointUnary.producer.result (V40StoredRectangle.input L K ctx R)).length)=_
  rw [midpointUnary.result_eq,List.length_replicate]
  change natField (2*(V40StoredThreshold.threshold.value (V40StoredRectangle.input L K ctx R))+
    V40StoredThreshold.inputK.value (V40StoredRectangle.input L K ctx R))=_
  rw [V40StoredThreshold.threshold_value]
  simp [V40StoredThreshold.inputK,UnaryProducer.input,V40StoredRectangle.input,
    V40StoredThreshold.input,BankFieldProjection.result_encode]

/-- The existing charged bounded simulator makes the formatter total on
all words, while preserving every canonical retained-state run. -/
def square : Producer := V40BoundedFormatter.bounded V40StoredEnvelope.machine
  V40StoredEnvelope.coefficient V40StoredEnvelope.degree

theorem square_result (L K : ℕ) (ctx : List Bool) (R : StoredMatrix) :
    square.result (V40StoredEnvelope.input L K ctx R)=R.squareWord :=
  V40BoundedFormatter.result_of_run V40StoredEnvelope.machine
    V40StoredEnvelope.coefficient V40StoredEnvelope.degree _ _
    (V40StoredEnvelope.outputs L K ctx R)

def request : Producer := concat header square

theorem request_result (L K : ℕ) (ctx : List Bool) (R : StoredMatrix) :
    request.result (V40StoredEnvelope.input L K ctx R)=
      natField (2*V40StoredThreshold.thresholdNumber L K+K)++R.squareWord := by
  change header.result _ ++ square.result _=_
  rw [midpoint_result,square_result]

theorem outputs (L K : ℕ) (ctx : List Bool) (R : StoredMatrix) :
    request.machine.OutputsWithin (V40StoredEnvelope.input L K ctx R)
      (natField (2*V40StoredThreshold.thresholdNumber L K+K)++R.squareWord)
      (request.coefficient*((V40StoredEnvelope.input L K ctx R).length+1)^request.degree) := by
  simpa only [request_result] using request.outputs (V40StoredEnvelope.input L K ctx R)

theorem public_outputs (p : SourceConstants) (floor : ℕ) {n m : ℕ}
    (hn : 0<n) (hlow : n≤2*m) (hdegree : 2*m≤p.degree*n)
    (edge : Fin m → Bool → Fin n) (K : ℕ) (ctx : List Bool) :
    let L:=publicLogFrom p floor n m hn hlow hdegree
    let R:=publicGraphRunFrom p floor hn hlow hdegree edge K
    request.machine.OutputsWithin (V40StoredEnvelope.input L K ctx R)
      (natField (2*publicGraphThresholdFrom p floor n m hn hlow hdegree K+K)++R.squareWord)
      (request.coefficient*((V40StoredEnvelope.input L K ctx R).length+1)^request.degree) :=
  outputs _ _ _ _

#print axioms outputs
#print axioms public_outputs
end
end CurrentAdditive.V40DeterministicRequest
