import CurrentV43.Parametric.Carrier
import CurrentV43.ResourcePower

set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 32768
namespace CurrentV43.ParametricSource
noncomputable section
open Paper2 Turing EthInapproximability.CurrentPaper CurrentAdditive
open EncodedETHSource
open PhysicalConcat

/-- Canonical bank framing for the two physical unary arguments. -/
def bank2 (A B : Producer) : Producer :=
  append (compose A (PhysicalProducer.localProducer PhysicalProducer.field))
    (compose B (PhysicalProducer.localProducer PhysicalProducer.field))

theorem bank2_result (A B : Producer) (w : List Bool) :
    (bank2 A B).result w=BitMachineBankCodec.encode ![A.result w,B.result w] := by
  simp only [bank2,append,compose,PhysicalProducer.localProducer,PhysicalProducer.field]
  simp [BitMachineBankCodec.encode_eq_list]

/-- Normalize every raw schedule output to its actual unary length.
On canonical formula inputs this changes no bit and preserves K exactly. -/
def resourceInput (S : Schedule) : Producer :=
  let len := PhysicalProducer.localProducer DynamicGetterPrimitives.literalLength
  bank2 len (compose S.producer len)

theorem resourceInput_result (S : Schedule) (w : List Bool) :
    (resourceInput S).result w=PowerMachine.input w.length (S.producer.result w).length := by
  rw [resourceInput,bank2_result]
  rfl

/-- A fixed paid resource printer.  The source word length and the gap
are data, and the variable exponent is executed by the unary power machine. -/
def resourceProducer (S : Schedule) (C : Nat) : Producer where
  machine := BitMachineComposition.composition (resourceInput S).machine (PowerMachine.resourceMachine C)
  result := fun w => List.replicate ((w.length+2)^(C*((S.producer.result w).length+1))) true
  clock := fun w => (resourceInput S).clock w+2*((resourceInput S).result w).length+2+
    PowerMachine.resourceClock C w.length (S.producer.result w).length
  outputs w := by
    have h1 := (resourceInput S).outputs w
    have h2 := PowerMachine.resource_outputs C w.length (S.producer.result w).length
    rw [←resourceInput_result S w] at h2
    exact BitMachineComposition.composition_outputsWithin _ _ h1 h2

theorem resource_result (S : Schedule) (C : Nat) (Φ : ValidFormula) :
    (resourceProducer S C).result (EncodedCNF.encode Φ.val)=
      List.replicate (((EncodedCNF.encode Φ.val).length+2)^(C*(S.gap Φ.val.variables+1))) true := by
  change List.replicate (((EncodedCNF.encode Φ.val).length+2)^
    (C*((S.producer.result (EncodedCNF.encode Φ.val)).length+1))) true=_
  rw [S.correct Φ,List.length_replicate]

theorem resource_length (S : Schedule) (C : Nat) (Φ : ValidFormula) :
    ((resourceProducer S C).result (EncodedCNF.encode Φ.val)).length=
      ((EncodedCNF.encode Φ.val).length+2)^(C*(S.gap Φ.val.variables+1)) := by
  rw [resource_result,List.length_replicate]

/-- Concrete source-size carrier, with its literal length-generation run. -/
theorem concrete_carrier_outputs (S : Schedule) (C : Nat) (w : List Bool) :
    (carrierProducer (resourceProducer S C)).machine.OutputsWithin w
      (List.replicate (carrierLength (resourceProducer S C) w) true)
      ((carrierProducer (resourceProducer S C)).clock w) :=
  carrier_outputs (resourceProducer S C) w

#print axioms resourceProducer
#print axioms resource_result
#print axioms concrete_carrier_outputs
end
end CurrentV43.ParametricSource

