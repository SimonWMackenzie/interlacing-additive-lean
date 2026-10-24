import CurrentAdditive.V40StoredSquare

namespace CurrentAdditive.V40StoredEnvelope
noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 32768
open EthInapproximability.CurrentPaper EncodedCommunication
open V39GeneratedConstruction PhysicalProducer

def input (L K : Nat) (context : List Bool) (R : StoredMatrix) :=
  BitMachineBankCodec.encode ![BitMachineBankCodec.encode
    ![List.replicate L true,List.replicate K true,context],StoredWeightedState.encode R]

def envelope := PhysicalProducer.projection (0 : Fin 2)
def publicL := compose envelope (PhysicalProducer.projection (0 : Fin 3))
def publicK := compose envelope (PhysicalProducer.projection (1 : Fin 3))
def context := compose envelope (PhysicalProducer.projection (2 : Fin 3))
def weightedState := PhysicalProducer.projection (1 : Fin 2)
def plainState := concat (compose context field) (compose weightedState field)
def route := concat (compose publicL field)
  (concat (compose publicK field) (compose plainState field))

private theorem compose_result (A B : Producer) (x : List Bool) :
    (compose A B).result x=B.result (A.result x) := rfl
private theorem concat_result (A B : Producer) (x : List Bool) :
    (concat A B).result x=A.result x++B.result x := rfl
private theorem field_result (x : List Bool) :
    PhysicalProducer.field.result x=EncodedCommunication.field x := rfl
private theorem projection_result {N : Nat} (j : Fin N) (x : List Bool) :
    (PhysicalProducer.projection j).result x=BankFieldProjection.result j x := rfl

theorem route_result (L K : Nat) (ctx : List Bool) (R : StoredMatrix) :
    route.result (input L K ctx R)=V40StoredRectangle.input L K ctx R := by
  simp only [route,concat_result,compose_result,publicL,publicK,context,
    envelope,weightedState,plainState,projection_result,field_result,input,
    BankFieldProjection.result_encode,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two]
  simp [V40StoredRectangle.input,V40StoredThreshold.input,BitMachineBankCodec.encode_eq_list]
#print axioms route_result
def rectangle := compose route V40StoredRectangle.rectangle
theorem rectangle_result (L K : Nat) (ctx : List Bool) (R : StoredMatrix) :
    rectangle.result (input L K ctx R)=
      encodeInstance (V40StoredRectangle.rectangleInstance L K R) := by
  change V40StoredRectangle.rectangle.result (route.result (input L K ctx R))=_
  rw [route_result,V40StoredRectangle.rectangle_result]

theorem rectangle_outputs (L K : Nat) (ctx : List Bool) (R : StoredMatrix) :
    rectangle.machine.OutputsWithin (input L K ctx R)
      (encodeInstance (V40StoredRectangle.rectangleInstance L K R))
      (rectangle.coefficient*((input L K ctx R).length+1)^rectangle.degree) := by
  simpa only [rectangle_result] using rectangle.outputs (input L K ctx R)
#print axioms rectangle_outputs

def machine := BitMachineComposition.composition route.machine V40StoredSquare.machine
def coefficient : Nat := route.coefficient+2*(route.coefficient*route.machine.pushBound+1)+
  V40StoredSquare.coefficient*(route.coefficient*route.machine.pushBound+1)^V40StoredSquare.degree
def degree : Nat := (route.degree+1)*(V40StoredSquare.degree+1)

/-- The retained iteration envelope is consumed directly. All routing,
arithmetic, dimension extraction, rectangle writing and square padding are
charged to the length of this complete input word. -/
theorem outputs (L K : Nat) (ctx : List Bool) (R : StoredMatrix) :
    machine.OutputsWithin (input L K ctx R) R.squareWord
      (coefficient*((input L K ctx R).length+1)^degree) := by
  have hr := route.outputs (input L K ctx R)
  have hs := V40StoredSquare.outputs L K ctx R
  rw [← route_result L K ctx R] at hs
  have h := BitMachineComposition.composition_outputsWithin route.machine
    V40StoredSquare.machine hr hs
  apply BitMachine.outputsWithin_mono _ h
  exact BitMachineCompositionArithmetic.composition_time_bound
    (input L K ctx R).length route.coefficient route.degree
    V40StoredSquare.coefficient V40StoredSquare.degree route.machine.pushBound
    (route.result (input L K ctx R)).length
    (BitMachine.output_length_bound route.machine hr)
#print axioms outputs

theorem public_outputs (p : SourceConstants) (floor : Nat) {n m : Nat}
    (hn : 0<n) (hlow : n≤2*m) (hdegree : 2*m≤p.degree*n)
    (edge : Fin m → Bool → Fin n) (K : Nat) (ctx : List Bool) :
    let L := publicLogFrom p floor n m hn hlow hdegree
    let R := publicGraphRunFrom p floor hn hlow hdegree edge K
    machine.OutputsWithin (input L K ctx R) R.squareWord
      (coefficient*((input L K ctx R).length+1)^degree) := outputs _ _ _ _

#print axioms public_outputs
end
end CurrentAdditive.V40StoredEnvelope
