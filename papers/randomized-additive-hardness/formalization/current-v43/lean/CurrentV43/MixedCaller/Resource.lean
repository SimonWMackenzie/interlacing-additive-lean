import CurrentV43.MixedCaller.Request
import CurrentV43.Parametric.Carrier

/-! The finite random carrier is printed from the actual deterministic
request, with no promise that randomness is polynomial in the CNF length.
This supports arbitrary paid schedules whose unary gaps may be very large. -/
namespace CurrentV43.MixedCaller
noncomputable section
open CurrentAdditive Paper2 EthInapproximability.CurrentPaper
open V40StoredOutputPrimitives
set_option maxHeartbeats 2000000
set_option maxRecDepth 65536

def lengthUnary : UnaryProducer where
  value x := x.length
  producer := normalizer
  result_eq _ := rfl

def successorUnary : UnaryProducer := UnaryProducer.binary .add lengthUnary (UnaryProducer.constant 1)

def fixedPower : ℕ → UnaryProducer
  | 0 => UnaryProducer.constant 1
  | d+1 => UnaryProducer.binary .mul (fixedPower d) successorUnary

theorem fixedPower_value (d : ℕ) (x : List Bool) :
    (fixedPower d).value x=(x.length+1)^d := by
  induction d with
  | zero => rfl
  | succ d ih =>
    change (fixedPower d).value x*(x.length+1)=(x.length+1)^(d+1)
    rw [ih,pow_succ]

/-- This is the classifier's literal request-dependent random-bit count,
computed by fixed finite unary arithmetic. -/
def tapeUnary (C : SelectedTape.Algorithm) : UnaryProducer :=
  UnaryProducer.binary .mul (UnaryProducer.constant C.cR) (fixedPower C.dR)

theorem tapeUnary_result (C : SelectedTape.Algorithm) (x : List Bool) :
    (tapeUnary C).producer.result x=List.replicate (C.tapeLength x) true := by
  rw [(tapeUnary C).result_eq]
  congr 1
  change C.cR*(fixedPower C.dR).value x=C.cR*(x.length+1)^C.dR
  rw [fixedPower_value]

/-- P is an actual all-input request producer, not a decision certificate.
The resource printer executes P and then physically counts its required bits. -/
def tapeResource (P : PhysicalConcat.Producer) (C : SelectedTape.Algorithm) :=
  ParametricSource.compose P (PhysicalProducer.localProducer (tapeUnary C).producer)

theorem tapeResource_result (P : PhysicalConcat.Producer) (C : SelectedTape.Algorithm)
    (w : List Bool) :
    (tapeResource P C).result w=List.replicate (C.tapeLength (P.result w)) true :=
  tapeUnary_result C (P.result w)

def tapeLength (P : PhysicalConcat.Producer) (C : SelectedTape.Algorithm) (w : List Bool) :=
  ParametricSource.carrierLength (tapeResource P C) w

def tapeProducer (P : PhysicalConcat.Producer) (C : SelectedTape.Algorithm) :=
  ParametricSource.carrierProducer (tapeResource P C)

/-- An actual machine computes the finite tape length, before any fair bits
are chosen. The carrier may exceed every fixed polynomial of source length. -/
theorem tapeProducer_outputs (P : PhysicalConcat.Producer) (C : SelectedTape.Algorithm)
    (w : List Bool) :
    (tapeProducer P C).machine.OutputsWithin w (List.replicate (tapeLength P C w) true)
      ((tapeProducer P C).clock w) :=
  ParametricSource.carrier_outputs (tapeResource P C) w

theorem selected_le_block (P : PhysicalConcat.Producer) (C : SelectedTape.Algorithm)
    (w : List Bool) :
    C.tapeLength (P.result w)≤ParametricSource.blockLength (tapeResource P C) w := by
  have h:=ParametricSource.resource_le_block (tapeResource P C) w
  rwa [tapeResource_result,List.length_replicate] at h

theorem selected_le_carrier (P : PhysicalConcat.Producer) (C : SelectedTape.Algorithm)
    (w : List Bool) : C.tapeLength (P.result w)≤tapeLength P C w := by
  have h:=selected_le_block P C w
  unfold tapeLength ParametricSource.carrierLength
  omega

/-- The raw algorithm uses its exact finite carrier; the physical classifier
cutter selects the necessary prefix after P has printed the actual request. -/
def finiteMachine (P : PhysicalConcat.Producer) (C : SelectedTape.Algorithm) :=
  V40ClassifierTail.after P.machine C

def finiteOutput (P : PhysicalConcat.Producer) (C : SelectedTape.Algorithm)
    (w tape : List Bool) :=
  C.output (P.result w) (tape.take (C.tapeLength (P.result w)))

def finiteClock (P : PhysicalConcat.Producer) (C : SelectedTape.Algorithm)
    (w tape : List Bool) :=
  V40ClassifierTail.afterClock C w (P.result w) tape (P.clock w)

theorem finite_outputs (P : PhysicalConcat.Producer) (C : SelectedTape.Algorithm)
    (w : List Bool) (tape : Fin (tapeLength P C w)→Bool) :
    (finiteMachine P C).OutputsWithin (EncodedComplexity.pair w (List.ofFn tape))
      (finiteOutput P C w (List.ofFn tape)) (finiteClock P C w (List.ofFn tape)) := by
  apply V40ClassifierTail.outputs_after P.machine C w (P.result w) (List.ofFn tape)
    (P.clock w) (P.outputs w)
  simpa only [List.length_ofFn] using selected_le_carrier P C w

/-- Exact law on the same tapes on which the fixed machine was just run. -/
theorem finite_law (P : PhysicalConcat.Producer) (C : SelectedTape.Algorithm)
    (w : List Bool) (event : List Bool→Prop) :
    (Unit4Shell.Definitions.uniformTape (tapeLength P C w)).prob
      (fun tape=>event (finiteOutput P C w (List.ofFn tape))) =
      C.prob (P.result w) event :=
  AModel.uniformTape_take_prob (selected_le_carrier P C w)
    (fun tape=>event (C.output (P.result w) tape))

/-- Fixed polynomial bound for the actual full-source mixed clock. -/
theorem finiteClock_poly (P : PhysicalConcat.Producer) (C : SelectedTape.Algorithm) :
    Unit4Shell.Poly.PolyIn
      (fun z : List Bool×List Bool => z.1.length+P.clock z.1+(P.result z.1).length+z.2.length)
      (fun z => finiteClock P C z.1 z.2) := by
  let sz:=fun z : List Bool×List Bool => z.1.length+P.clock z.1+(P.result z.1).length+z.2.length
  have hi : Unit4Shell.Poly.PolyIn sz (fun z=>z.1.length) :=
    Unit4Shell.Poly.mono (by intro z; dsimp [sz]; omega) Unit4Shell.Poly.self
  have ht : Unit4Shell.Poly.PolyIn sz (fun z=>P.clock z.1) :=
    Unit4Shell.Poly.mono (by intro z; dsimp [sz]; omega) Unit4Shell.Poly.self
  have hr : Unit4Shell.Poly.PolyIn sz (fun z=>(P.result z.1).length) :=
    Unit4Shell.Poly.mono (by intro z; dsimp [sz]; omega) Unit4Shell.Poly.self
  have hb : Unit4Shell.Poly.PolyIn sz (fun z=>z.2.length) :=
    Unit4Shell.Poly.mono (by intro z; dsimp [sz]; omega) Unit4Shell.Poly.self
  change Unit4Shell.Poly.PolyIn sz _
  unfold finiteClock V40ClassifierTail.afterClock V40ClassifierTail.cap NPOwner1.Trunc.timeBound
  simp only [EncodedComplexity.pair_length]
  repeat (first
    | exact hi
    | exact ht
    | exact hr
    | exact hb
    | exact Unit4Shell.Poly.const _
    | apply Unit4Shell.Poly.add
    | apply Unit4Shell.Poly.mul
    | apply Unit4Shell.Poly.pow)

#print axioms tapeProducer_outputs
#print axioms finite_outputs
#print axioms finite_law
#print axioms finiteClock_poly
end
end CurrentV43.MixedCaller
