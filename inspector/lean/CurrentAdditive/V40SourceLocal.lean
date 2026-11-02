import CurrentAdditive.D22PacketPrimitives
import CurrentAdditive.V40SeedProducer

/-! Fixed physical composition and arbitrary finite-bank serialization.
The local metadata contains no assumed execution certificate. Each consumer
proves execution from the concrete component machines. -/
namespace CurrentAdditive.V40SourceLocal
noncomputable section
open EthInapproximability.CurrentPaper BitMachineComposition
open D22PacketPrimitives
open BitMachineBankCodec
set_option maxHeartbeats 3000000
set_option maxRecDepth 32768

abbrev Producer := D22PacketPrimitives.Producer
def physical (A : PhysicalProducer.Producer) : Producer :=
  ⟨A.machine,A.result,fun x => A.coefficient*(x.length+1)^A.degree⟩
theorem physical_outputs (A : PhysicalProducer.Producer) (x : List Bool) :
    (physical A).machine.OutputsWithin x ((physical A).result x) ((physical A).clock x) := A.outputs x
def constant (w : List Bool) : Producer := physical (V40SeedProducer.constant w)
theorem constant_outputs (w x : List Bool) :
    (constant w).machine.OutputsWithin x ((constant w).result x) ((constant w).clock x) :=
  physical_outputs _ _

def compose (A B : Producer) : Producer :=
  ⟨composition A.machine B.machine,B.result ∘ A.result,
    fun x => A.clock x+2*(A.result x).length+2+B.clock (A.result x)⟩
theorem compose_outputs (A B : Producer) (x : List Bool)
    (ha : A.machine.OutputsWithin x (A.result x) (A.clock x))
    (hb : B.machine.OutputsWithin (A.result x) (B.result (A.result x)) (B.clock (A.result x))) :
    (compose A B).machine.OutputsWithin x ((compose A B).result x) ((compose A B).clock x) :=
  composition_outputsWithin A.machine B.machine ha hb

def serialise : {k : Nat} → (Fin k → Producer) → Producer
  | 0,_ => constant []
  | k+1,A => append (frame (A 0)) (serialise (fun i : Fin k => A i.succ))

theorem serialise_result {k : Nat} (A : Fin k → Producer) (x : List Bool) :
    (serialise A).result x=encode (fun i => (A i).result x) := by
  induction k with
  | zero => simp [serialise,constant,physical,V40SeedProducer.constant,encode,encodeFrom]
  | succ k ih =>
    simp only [serialise,append,frame,ih]
    rw [encode_eq_list]
    simp [List.ofFn_succ,encode_eq_list,List.append_assoc]

theorem serialise_outputs {k : Nat} (A : Fin k → Producer) (x : List Bool)
    (h : ∀ i, (A i).machine.OutputsWithin x ((A i).result x) ((A i).clock x)) :
    (serialise A).machine.OutputsWithin x ((serialise A).result x) ((serialise A).clock x) := by
  induction k with
  | zero => exact constant_outputs [] x
  | succ k ih =>
    exact append_outputs _ _ x (frame_outputs _ x (h 0)) (ih _ (fun i => h i.succ))

def unaryField : Producer :=
  ⟨SourceFieldWriter.unaryFieldMachine,fun x => EncodedCommunication.natField x.length,
    fun x => (UnaryBinaryEncoding.coefficient+10)*(x.length+1)^2⟩
theorem unaryField_outputs (x : List Bool) :
    unaryField.machine.OutputsWithin x (unaryField.result x) (unaryField.clock x) :=
  SourceFieldWriter.unary_field_outputs x

def physicalBank : {k : Nat} → (Fin k → PhysicalProducer.Producer) → PhysicalProducer.Producer
  | 0,_ => V40SeedProducer.constant []
  | k+1,A => PhysicalProducer.concat (PhysicalProducer.compose (A 0) PhysicalProducer.field)
      (physicalBank (fun i : Fin k => A i.succ))
theorem physicalBank_result {k : Nat} (A : Fin k → PhysicalProducer.Producer) (x : List Bool) :
    (physicalBank A).result x=encode (fun i => (A i).result x) := by
  induction k with
  | zero => simp [physicalBank,V40SeedProducer.constant,encode,encodeFrom]
  | succ k ih =>
    simp only [physicalBank,PhysicalProducer.concat,PhysicalProducer.compose,
      PhysicalProducer.field,Function.comp_apply,ih]
    rw [encode_eq_list]
    simp [List.ofFn_succ,encode_eq_list,List.append_assoc]

#print axioms serialise_outputs
end
end CurrentAdditive.V40SourceLocal
