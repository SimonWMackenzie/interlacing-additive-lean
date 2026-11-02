import CurrentAdditive.CodeDFixedWordProducer
import CurrentAdditive.CodeDPacketRouting
import CurrentAdditive.CodeDTargetV2
import CurrentAdditive.LabelTrace

/-! Physical literal seed and packet construction. Every field producer,
projection, framing bit and transfer is paid by PhysicalProducer. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 16384
namespace CurrentAdditive.CodeDSeedLayout
open EthInapproximability.CurrentPaper BitMachineBankCodec
open PhysicalProducer CodeDTargetV2 LabelTrace

def seedSource : Array ((Fin 0 → Nat) × ℚ) := #[(Fin.elim0,1)]
def seedWord : List Bool := CodeDCanonicalSourceV2.encodedSource seedSource

theorem seed_exact (D : Nat) (alphabet : Array (Nat × ℚ)) :
    sequentialPreprocessed D alphabet 0=some seedSource := rfl

def state (lawBytes : List Bool) := encode ![[],lawBytes,seedWord]
def packet (fuel lawBytes : List Bool) := encode ![fuel,lawBytes]
def output (fuel lawBytes : List Bool) := encode ![state lawBytes,fuel]

noncomputable def stateProducer : Producer :=
  CodeDPacketRouting.bank3 (CodeDFixedWordProducer.producer [])
    (projection (1 : Fin 2)) (CodeDFixedWordProducer.producer seedWord)

noncomputable def producer : Producer :=
  CodeDPacketRouting.bank2 stateProducer (projection (0 : Fin 2))

theorem state_result (fuel lawBytes : List Bool) :
    stateProducer.result (packet fuel lawBytes)=state lawBytes := by
  unfold stateProducer
  rw [CodeDPacketRouting.bank3_result]
  simp only [CodeDFixedWordProducer.producer,projection,packet,BankFieldProjection.result_encode,
    Matrix.cons_val_one,Matrix.cons_val_zero,state]

theorem result_exact (fuel lawBytes : List Bool) :
    producer.result (packet fuel lawBytes)=output fuel lawBytes := by
  unfold producer
  rw [CodeDPacketRouting.bank2_result,state_result]
  simp only [projection,packet,BankFieldProjection.result_encode,Matrix.cons_val_zero,output]

theorem outputs (fuel lawBytes : List Bool) :
    producer.machine.OutputsWithin (packet fuel lawBytes) (output fuel lawBytes)
      (producer.coefficient*((packet fuel lawBytes).length+1)^producer.degree) := by
  simpa only [result_exact] using producer.outputs (packet fuel lawBytes)

#print axioms seed_exact
#print axioms outputs
end CurrentAdditive.CodeDSeedLayout
