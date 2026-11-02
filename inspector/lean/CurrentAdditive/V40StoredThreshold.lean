import CurrentAdditive.V40StoredOutputPrimitives
import CurrentAdditive.V39PublicFloor

namespace CurrentAdditive.V40StoredThreshold
noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 32768
open Paper2 EthInapproximability.CurrentPaper V38Schedule
open V39GeneratedConstruction V40StoredOutputPrimitives PhysicalProducer

def inputL := UnaryProducer.input (0 : Fin 3)
def inputK := UnaryProducer.input (1 : Fin 3)
def quarter := UnaryProducer.binary .quot
  (UnaryProducer.binary .add inputL (UnaryProducer.constant 3)) (UnaryProducer.constant 4)
def seedExponent := UnaryProducer.clog
  (UnaryProducer.binary .mul (UnaryProducer.constant 64)
    (UnaryProducer.binary .add inputL (UnaryProducer.constant 1)))
def stepCost := UnaryProducer.binary .add
  (UnaryProducer.binary .mul (UnaryProducer.constant 12) inputL)
  (UnaryProducer.binary .mul (UnaryProducer.constant 2) quarter)
def threshold := UnaryProducer.binary .add
  (UnaryProducer.binary .add seedExponent (UnaryProducer.constant 1))
  (UnaryProducer.binary .mul inputK stepCost)

def thresholdNumber (L K : Nat) := LookupSeed.exponent L+1+K*(12*L+2*quarterCeil L)

theorem threshold_value (x : List Bool) : threshold.value x=
    thresholdNumber (BankFieldProjection.result (0 : Fin 3) x).length
      (BankFieldProjection.result (1 : Fin 3) x).length := rfl

def unaryField : Producer where
  machine := SourceFieldWriter.unaryFieldMachine
  result := fun word => EncodedCommunication.natField word.length
  coefficient := UnaryBinaryEncoding.coefficient+10
  degree := 2
  outputs := SourceFieldWriter.unary_field_outputs

def fieldProducer : Producer := compose threshold.producer unaryField

def input (L K : Nat) (stateword : List Bool) :=
  BitMachineBankCodec.encode ![List.replicate L true,List.replicate K true,stateword]

theorem field_result (x : List Bool) : fieldProducer.result x=
    EncodedCommunication.natField (thresholdNumber
      (BankFieldProjection.result (0 : Fin 3) x).length
      (BankFieldProjection.result (1 : Fin 3) x).length) := by
  simp only [fieldProducer,compose,Function.comp_apply,unaryField,threshold.result_eq,
    List.length_replicate,threshold_value]

theorem field_result_input (L K : Nat) (stateword : List Bool) :
    fieldProducer.result (input L K stateword)=EncodedCommunication.natField (thresholdNumber L K) := by
  rw [field_result]
  simp [input,BankFieldProjection.result_encode]

theorem threshold_eq_public (p : SourceConstants) (floor n m : Nat)
    (hn : 0<n) (hlow : n≤2*m) (hdegree : 2*m≤p.degree*n) (K : Nat) :
    thresholdNumber (publicLogFrom p floor n m hn hlow hdegree) K=
      publicGraphThresholdFrom p floor n m hn hlow hdegree K := rfl

#print axioms field_result_input
#print axioms threshold_eq_public
#print axioms fieldProducer
end
end CurrentAdditive.V40StoredThreshold
