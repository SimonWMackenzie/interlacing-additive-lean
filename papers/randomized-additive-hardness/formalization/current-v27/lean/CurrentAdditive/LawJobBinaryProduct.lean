import CurrentAdditive.LawJobBitPrimitives
import CurrentAdditive.StoredBinaryAdd
import CurrentAdditive.CodeDCanonicalSourceV2
import EthInapproximability.CurrentPaper.BitMachineBinaryMultiply

namespace CurrentAdditive.LawJobBinaryProduct

open EthInapproximability.CurrentPaper PhysicalProducer LawJobBitPrimitives

noncomputable section

def prepare : Producer :=
  concat (compose empty field) (concat (compose empty field)
    (concat (compose empty field) (concat (compose (projection (0 : Fin 2)) field)
      (concat (compose (compose (projection (1 : Fin 2)) reverse) field)
        (compose empty field)))))

theorem prepare_result (word : List Bool) :
    prepare.result word=BitMachineBinaryMultiply.packedInput
      (BankFieldProjection.result (0 : Fin 2) word)
      (BankFieldProjection.result (1 : Fin 2) word).reverse := by
  have hb (a b : List Bool) : BitMachineBinaryMultiply.initialBank a b =
      (![[],[],[],a,b,[]] : Fin 6 → List Bool) := by
    funext i
    fin_cases i <;> rfl
  simp [prepare,concat,compose,projection,field,empty,reverse,
    BitMachineBinaryMultiply.packedInput,hb,BitMachineBankCodec.encode_eq_list]

def packedProducer : Producer where
  machine := BitMachineComposition.composition prepare.machine BitMachineBinaryMultiply.packedMachine
  result := fun word=>BitMachineBankCodec.encode (BitMachineBinaryMultiply.finalBank
    (BankFieldProjection.result (0 : Fin 2) word)
    (BankFieldProjection.result (1 : Fin 2) word).reverse)
  coefficient := prepare.coefficient+2*(prepare.coefficient*prepare.machine.pushBound+1)+
    100*(prepare.coefficient*prepare.machine.pushBound+1)^2
  degree := (prepare.degree+1)*3
  outputs word := by
    have ha:=prepare.outputs word
    have hb:=BitMachineBinaryMultiply.packed_outputs
      (BankFieldProjection.result (0 : Fin 2) word)
      (BankFieldProjection.result (1 : Fin 2) word).reverse
    rw [←prepare_result] at hb
    apply BitMachine.outputsWithin_mono _
      (BitMachineComposition.composition_outputsWithin _ _ ha hb)
    exact BitMachineCompositionArithmetic.composition_time_bound word.length
      prepare.coefficient prepare.degree 100 2 prepare.machine.pushBound
      (prepare.result word).length (BitMachine.output_length_bound _ ha)

def multiply : Producer := compose (compose packedProducer (projection (0 : Fin 6))) canon

theorem msb_reverse (word : List Bool) :
    BitMachineBinaryMultiply.msbValue word.reverse=EncodedCommunication.bitsValue word := by
  exact CodeDCanonicalSourceV2.msbValue_reverse word

theorem multiply_result (word : List Bool) :
    multiply.result word=
      (EncodedCommunication.bitsValue (BankFieldProjection.result (0 : Fin 2) word)*
        EncodedCommunication.bitsValue (BankFieldProjection.result (1 : Fin 2) word)).bits := by
  simp only [multiply,compose,Function.comp_apply,canon,projection,packedProducer,
    BankFieldProjection.result_encode]
  change BG34Canon.canon (BitMachineBinaryMultiply.multiplyFrom [] _ _) = _
  rw [canon_eq_bits,BitMachineBinaryMultiply.standard_value,msb_reverse]

theorem multiply_packet (a b : List Bool) :
    multiply.result (BitMachineBankCodec.encode ![a,b])=
      (EncodedCommunication.bitsValue a*EncodedCommunication.bitsValue b).bits := by
  simp [multiply_result]

theorem multiply_nats (m n : Nat) :
    multiply.result (BitMachineBankCodec.encode ![m.bits,n.bits])=(m*n).bits := by
  simp [multiply_packet]

def add : Producer := compose StoredBinaryAdd.producer canon

theorem add_packet (a b : List Bool) :
    add.result (BitMachineBankCodec.encode ![a,b])=
      (EncodedCommunication.bitsValue a+EncodedCommunication.bitsValue b).bits := by
  change BG34Canon.canon (StoredBinaryAdd.producer.result _) = _
  rw [StoredBinaryAdd.result_packet,canon_eq_bits,BitMachineBinaryAddAny.result_value]

#print axioms packedProducer
#print axioms multiply
#print axioms multiply_nats
#print axioms add_packet

end
end CurrentAdditive.LawJobBinaryProduct
