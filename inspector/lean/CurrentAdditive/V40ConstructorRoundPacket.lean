import CurrentAdditive.V40GraphConstructorFront
import CurrentAdditive.V40StoredEnvelope
import CurrentAdditive.WeightedIterationDriver

namespace CurrentAdditive.V40ConstructorRoundPacket
noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 32768
open Turing EthInapproximability.CurrentPaper BitMachineEncoding PhysicalProducer
open V39GeneratedConstruction

def identityProgram (_ : Unit) : TM2.Stmt (fun _ : Fin 1=>Bool) Unit Unit := .halt
def identity : Producer where
  machine := ofFinite (0 : Fin 1) 0 () () identityProgram
  result := id
  coefficient := 1
  degree := 0
  outputs x := by
    apply outputsWithin_of_raw_run (0 : Fin 1) 0 () () identityProgram x x 1 1 le_rfl
    · rfl
    · rfl

def envelope := PhysicalProducer.projection (0 : Fin 2)
def rounds := compose envelope (PhysicalProducer.projection (1 : Fin 3))
def packet := V40GraphConstructorFront.bank2 identity rounds

private theorem compose_result (A B : Producer) (x : List Bool) :
    (compose A B).result x=B.result (A.result x) := rfl
private theorem projection_result {N : Nat} (j : Fin N) (x : List Bool) :
    (PhysicalProducer.projection j).result x=BankFieldProjection.result j x := rfl

/-- The actual retained unary K supplies the iteration fuel. It is read
from the produced envelope, rather than inserted as prepared advice. -/
theorem packet_result (L K : Nat) (ctx : List Bool) (R : StoredMatrix) :
    packet.result (V40StoredEnvelope.input L K ctx R)=
      WeightedIterationDriver.input (V40StoredEnvelope.input L K ctx R) K := by
  rw [packet,V40GraphConstructorFront.bank2_result]
  simp only [rounds,compose_result,envelope,projection_result,V40StoredEnvelope.input,
    BankFieldProjection.result_encode,Matrix.cons_val_zero,Matrix.cons_val_one,identity,id_eq]
  rfl

theorem outputs (L K : Nat) (ctx : List Bool) (R : StoredMatrix) :
    packet.machine.OutputsWithin (V40StoredEnvelope.input L K ctx R)
      (WeightedIterationDriver.input (V40StoredEnvelope.input L K ctx R) K)
      (packet.coefficient*((V40StoredEnvelope.input L K ctx R).length+1)^packet.degree) := by
  simpa only [packet_result] using packet.outputs (V40StoredEnvelope.input L K ctx R)

#print axioms outputs
end
end CurrentAdditive.V40ConstructorRoundPacket
