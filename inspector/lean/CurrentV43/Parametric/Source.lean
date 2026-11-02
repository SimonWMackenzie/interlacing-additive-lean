import CurrentAdditive.V42SourceClassifierRun
import CurrentAdditive.V42AllRoundSampleAccess
import CurrentAdditive.PhysicalProducer

set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 32768
set_option synthInstance.maxSize 32768
namespace CurrentV43.ParametricSource
noncomputable section
open Paper2 Turing EthInapproximability.CurrentPaper
open EncodedETHSource EncodedETHSourceComposition
open Unit4Shell Unit4Shell.T10Finite
open CurrentAdditive
local instance : DecidableEq V42RawMidpointRequest.Raw := Classical.decEq _

/-- A gap schedule carries its finite implementation.  The separate clock
bound permits unary outputs larger than a polynomial in input length. -/
structure Schedule where
  gap : Nat → Nat
  producer : PhysicalConcat.Producer
  correct : ∀ Φ : ValidFormula, producer.result (EncodedCNF.encode Φ.val) =
    List.replicate (gap Φ.val.variables) true
  paid : ∀ density : Nat, ∃ c d : Nat, ∀ Φ : ValidFormula,
    Φ.val.clauses.length ≤ density*Φ.val.variables →
    producer.clock (EncodedCNF.encode Φ.val) ≤ c*(Φ.val.variables+gap Φ.val.variables+1)^d

def kFront (S : Schedule) : BitMachine.Machine :=
  BitMachineComposition.composition KofLoops.DupField.machine
    (BitMachineComposition.composition (PairMap.machine S.producer.machine) KofLoops.Swap.machine)

def kFrontClock (S : Schedule) (w tape : List Bool) : Nat :=
  let y := S.producer.result w
  let mid1 := EncodedComplexity.pair w (EncodedComplexity.pair w tape)
  let mid2 := EncodedComplexity.pair y (EncodedComplexity.pair w tape)
  6*((EncodedComplexity.pair w tape).length+1)+2*mid1.length+2+
    (2*w.length+S.producer.clock w+2*y.length+6+2*mid2.length+2+
      3*(mid2.length+1))

theorem kFront_outputs (S : Schedule) (w tape : List Bool) :
    (kFront S).OutputsWithin (EncodedComplexity.pair w tape)
      (EncodedComplexity.pair w (EncodedComplexity.pair (S.producer.result w) tape))
      (kFrontClock S w tape) := by
  have h1 := KofLoops.DupField.machine_outputs w tape
  have h2 := PairMap.machine_outputs S.producer.machine w (S.producer.result w) (EncodedComplexity.pair w tape)
    (S.producer.clock w) (S.producer.outputs w)
  have h3 := KofLoops.Swap.machine_outputs (S.producer.result w) w tape
  exact BitMachineComposition.composition_outputsWithin _ _ h1
    (BitMachineComposition.composition_outputsWithin _ _ h2 h3)

variable (D : DinurReduction) (B : BOTReduction (booleanOccurrence D))

def uniformMachine := Classical.choose (FrontUniform.front_uniform_raw D B)
def uniformCoefficient := Classical.choose (Classical.choose_spec (FrontUniform.front_uniform_raw D B))
def uniformDegree := Classical.choose (Classical.choose_spec (Classical.choose_spec (FrontUniform.front_uniform_raw D B)))

theorem uniform_outputs (K : Nat) (Φ : ValidFormula) (tape : List Bool) :
    (uniformMachine D B).OutputsWithin
      (EncodedComplexity.pair (EncodedCNF.encode Φ.val) (EncodedComplexity.pair (List.replicate K true) tape))
      (BitMachineBankCodec.encode ![EncodedGraph.encode (t10Graph D B Φ),List.replicate K true,tape])
      (uniformCoefficient D B*((EncodedComplexity.pair (EncodedCNF.encode Φ.val)
        (EncodedComplexity.pair (List.replicate K true) tape)).length+1)^uniformDegree D B) :=
  Classical.choose_spec (Classical.choose_spec (Classical.choose_spec (FrontUniform.front_uniform_raw D B))) K Φ tape

abbrev gPort := V42RawRequestPacket.graphPort
abbrev kPort := V42RawRequestPacket.kPort
abbrev tPort := V42RawRequestPacket.tapePort
abbrev hgk := V42RawRequestPacket.graph_ne_k
abbrev hgt := V42RawRequestPacket.graph_ne_tape
abbrev hkt := V42RawRequestPacket.k_ne_tape

def sourceMachine (S : Schedule) := BitMachineComposition.composition (kFront S)
  (BitMachineComposition.composition (uniformMachine D B)
    (Unit4Post.Pre.machine (V39ThreePortFrame.workCount gPort kPort tPort)))

def sourceWord (S : Schedule) (Φ : ValidFormula) (tape : List Bool) :=
  BitMachineBankCodec.encode (fun i => V39ThreePortFrame.inputBank gPort kPort tPort
    (EncodedGraph.encode (t10Graph D B Φ)) (List.replicate (S.gap Φ.val.variables) true) tape
    ((V39TypedPacket.number gPort kPort tPort hgk hgt hkt).symm i))

def sourceClock (S : Schedule) (Φ : ValidFormula) (tape : List Bool) :=
  let mid := EncodedComplexity.pair (EncodedCNF.encode Φ.val)
    (EncodedComplexity.pair (List.replicate (S.gap Φ.val.variables) true) tape)
  let bank := BitMachineBankCodec.encode ![EncodedGraph.encode (t10Graph D B Φ),
    List.replicate (S.gap Φ.val.variables) true,tape]
  kFrontClock S (EncodedCNF.encode Φ.val) tape+2*mid.length+2+
    (uniformCoefficient D B*(mid.length+1)^uniformDegree D B+2*bank.length+2+
      (V39ThreePortFrame.workCount gPort kPort tPort+1))

theorem source_outputs (S : Schedule) (Φ : ValidFormula) (tape : List Bool) :
    (sourceMachine D B S).OutputsWithin (EncodedComplexity.pair (EncodedCNF.encode Φ.val) tape)
      (sourceWord D B S Φ tape) (sourceClock D B S Φ tape) := by
  have h1 := kFront_outputs S (EncodedCNF.encode Φ.val) tape
  rw [S.correct Φ] at h1
  have h2 := uniform_outputs D B (S.gap Φ.val.variables) Φ tape
  have h3 := V39ThreePortFrame.frame_outputs gPort kPort tPort hgk hgt hkt
    (EncodedGraph.encode (t10Graph D B Φ)) (List.replicate (S.gap Φ.val.variables) true) tape
  exact BitMachineComposition.composition_outputsWithin _ _ h1
    (BitMachineComposition.composition_outputsWithin _ _ h2 h3)

/-- One fixed front preserves the independent classifier stream. -/
def frontMachine (S : Schedule) := PairMap.machine (sourceMachine D B S)
def frontWord (S : Schedule) (Φ : ValidFormula) (tape classifierTape : List Bool) :=
  EncodedComplexity.pair (sourceWord D B S Φ tape) classifierTape

def frontClock (S : Schedule) (Φ : ValidFormula) (tape : List Bool) :=
  2*(EncodedComplexity.pair (EncodedCNF.encode Φ.val) tape).length+
    sourceClock D B S Φ tape+2*(sourceWord D B S Φ tape).length+6

theorem front_outputs (S : Schedule) (Φ : ValidFormula) (tape classifierTape : List Bool) :
    (frontMachine D B S).OutputsWithin
      (EncodedComplexity.pair (EncodedComplexity.pair (EncodedCNF.encode Φ.val) tape) classifierTape)
      (frontWord D B S Φ tape classifierTape) (frontClock D B S Φ tape) :=
  PairMap.machine_outputs (sourceMachine D B S) _ _ classifierTape _ (source_outputs D B S Φ tape)

#print axioms kFront_outputs
#print axioms source_outputs
#print axioms front_outputs
end
end CurrentV43.ParametricSource


