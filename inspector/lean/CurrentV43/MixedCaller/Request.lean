import CurrentAdditive.V42ETHPhysical
import CurrentAdditive.V40ClassifierTail
import CurrentAdditive.V39ActualOutputMajority

/-! Actual deterministic construction followed by a randomized estimator.
Private v43 `thm:time-tradeoff` candidate, main.tex 3238--3287.
The constructor and midpoint are physically computed by one fixed machine;
the independent estimator tape is preserved until that exact request exists. -/
namespace CurrentV43.MixedCaller
noncomputable section
open CurrentAdditive Paper2 EthInapproximability.CurrentPaper
open EncodedETHSource EncodedETHSourceComposition Unit4Shell.T10Finite
set_option maxHeartbeats 1500000
set_option maxRecDepth 65536

variable (D : DinurReduction) (B : BOTReduction (booleanOccurrence D))

def requestMachine := V42GraphRuntime.pipeline (V42ActualSource.k0 D B)
  V42DeterministicRequest.request.machine

def requestExponent := V42GraphRuntime.dyadicExponent B.degreeBound (V42ActualSource.k0 D B)
  V42DeterministicRequest.request.machine V42DeterministicRequest.request.coefficient
  V42DeterministicRequest.request.degree

def requestTime (Φ : ValidFormula) (K : ℕ) :=
  (V42ETHPhysical.N D B Φ)^(requestExponent D B*(V42ETHPhysical.amplification D B)^K)

def graphInput (Φ : ValidFormula) (K : ℕ) :=
  V42RuntimePrefix.input (EncodedGraph.encode (t10Graph D B Φ)) K

/-- Both the printed request and its time bound come from the actual
deterministic graph constructor, at an arbitrary round count. -/
theorem request_outputs (Φ : ValidFormula) (K : ℕ) :
    (requestMachine D B).OutputsWithin (graphInput D B Φ K)
      (V42ActualSource.request D B Φ K) (requestTime D B Φ K) ∧
    (V42ActualSource.request D B Φ K).length ≤ requestTime D B Φ K := by
  exact V42GraphRuntime.dyadic_outputs_with_tail B.degreeBound (V42ActualSource.k0 D B)
    V42DeterministicRequest.request.machine V42DeterministicRequest.request.coefficient
    V42DeterministicRequest.request.degree (t10Graph D B Φ) (t10Graph_valid D B Φ) K
    (V42ActualSource.k0_two D B) (V39CurrentSourceJoin.source_geometry D B Φ).1
    (V39CurrentSourceJoin.source_geometry D B Φ).2.2 (V42ActualSource.k0_degree D B)
    _ (V42ActualSource.request_tail_outputs D B Φ K)

def machine (C : SelectedTape.Algorithm) := V40ClassifierTail.after (requestMachine D B) C
def output (C : SelectedTape.Algorithm) (Φ : ValidFormula) (K : ℕ) (tape : List Bool) :=
  C.output (V42ActualSource.request D B Φ K)
    (tape.take (C.tapeLength (V42ActualSource.request D B Φ K)))
def clock (C : SelectedTape.Algorithm) (Φ : ValidFormula) (K : ℕ) (tape : List Bool) :=
  V40ClassifierTail.afterClock C (graphInput D B Φ K) (V42ActualSource.request D B Φ K)
    tape (requestTime D B Φ K)

/-- The actual classifier machine cuts its independent tape to the exact
request-dependent length. No classifier execution is assumed. -/
theorem outputs (C : SelectedTape.Algorithm) (Φ : ValidFormula) (K : ℕ) (tape : List Bool)
    (ht : C.tapeLength (V42ActualSource.request D B Φ K) ≤ tape.length) :
    (machine D B C).OutputsWithin (EncodedComplexity.pair (graphInput D B Φ K) tape)
      (output D B C Φ K tape) (clock D B C Φ K tape) :=
  V40ClassifierTail.outputs_after _ C _ _ _ _ (request_outputs D B Φ K).1 ht

/-- The actual fair-tape law is exactly the extracted classifier law. -/
theorem output_law (C : SelectedTape.Algorithm) (Φ : ValidFormula) (K R : ℕ)
    (ht : C.tapeLength (V42ActualSource.request D B Φ K) ≤ R) (P : List Bool → Prop) :
    (Unit4Shell.Definitions.uniformTape R).prob
      (fun t => P (output D B C Φ K (List.ofFn t))) =
      C.prob (V42ActualSource.request D B Φ K) P :=
  AModel.uniformTape_take_prob ht (fun t => P (C.output (V42ActualSource.request D B Φ K) t))

/-- A literal polynomial upper bound for the mixed tail, uniform in the
source formula, round count, and every bit of the independent tape. -/
def clockCap (C : SelectedTape.Algorithm) (n : ℕ) :=
  2*n+n+2*n+6+2*(3*n+1)+2+V40ClassifierTail.cap C (3*n+1)

theorem clockCap_poly (C : SelectedTape.Algorithm) :
    Unit4Shell.Poly.PolyIn id (clockCap C) := by
  unfold clockCap V40ClassifierTail.cap NPOwner1.Trunc.timeBound
  repeat (first
    | exact Unit4Shell.Poly.self
    | exact Unit4Shell.Poly.const _
    | apply Unit4Shell.Poly.add
    | apply Unit4Shell.Poly.mul
    | apply Unit4Shell.Poly.pow)

theorem cap_mono (C : SelectedTape.Algorithm) {m n : ℕ} (h : m ≤ n) :
    V40ClassifierTail.cap C m ≤ V40ClassifierTail.cap C n := by
  unfold V40ClassifierTail.cap NPOwner1.Trunc.timeBound
  gcongr

theorem clock_le (C : SelectedTape.Algorithm) (Φ : ValidFormula) (K : ℕ)
    (tape : List Bool) (n : ℕ) (hi : (graphInput D B Φ K).length ≤ n)
    (hr : requestTime D B Φ K ≤ n) (ht : tape.length ≤ n) :
    clock D B C Φ K tape ≤ clockCap C n := by
  have hreq := (request_outputs D B Φ K).2.trans hr
  have hp : (EncodedComplexity.pair (V42ActualSource.request D B Φ K) tape).length ≤ 3*n+1 := by
    rw [EncodedComplexity.pair_length]
    omega
  have hc := cap_mono C hp
  unfold clock V40ClassifierTail.afterClock clockCap
  omega

#print axioms request_outputs
#print axioms outputs
#print axioms output_law
#print axioms clock_le
end
end CurrentV43.MixedCaller
