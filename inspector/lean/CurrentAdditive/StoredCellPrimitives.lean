import CurrentAdditive.StoredQuery
import CurrentAdditive.StoredCellBytes
import CurrentAdditive.LawJobBinaryProduct
import CurrentAdditive.CylinderEvalConjunction
import EthInapproximability.CurrentPaper.ProtocolBinaryHeader
import EthInapproximability.CurrentPaper.UnaryBinaryEncoding

namespace CurrentAdditive.StoredCellPrimitives
open Turing EthInapproximability.CurrentPaper BitMachineEncoding PhysicalProducer
noncomputable section

def unaryBits : Producer := ⟨UnaryBinaryEncoding.machine,fun x=>x.length.bits,
  UnaryBinaryEncoding.coefficient,2,UnaryBinaryEncoding.outputs⟩

def binaryHeader : Producer where
  machine := ProtocolBinaryHeader.machine
  result := ProtocolBinaryHeader.result
  coefficient := 2
  degree := 1
  outputs x := by simpa only [pow_one,Nat.mul_add] using ProtocolBinaryHeader.outputs x

def countBits := compose binaryHeader DynamicGetterPrimitives.tail

theorem countBits_list (xs : List (List Bool)) :
    countBits.result (SourceListEncoding.encode xs)=xs.length.bits := by
  simp [countBits,compose,binaryHeader,DynamicGetterPrimitives.tail,
    ProtocolBinaryHeader.result,SourceListEncoding.encode,
    SourceListMachineFields.readChecked_natField]

theorem countBits_law {n : Nat} (μ : Paper2.PositiveRationalLaw (Fin n)) :
    countBits.result (StoredWeightedState.lawBytes μ)=n.bits := by
  have h := countBits_list ((StoredWeightedState.lawAlphabet μ).toList.map CodeDTargetV2.alphabetEntry)
  simpa [StoredWeightedState.lawBytes,CodeDTargetV2.alphabetBytes,CodeDCodecV2.encodeItems] using h

def conjunction : Producer where
  machine := CylinderEvalConjunction.machine
  result := fun x=>[CylinderConjunctionMachine.conjunction true x]
  coefficient := 1
  degree := 1
  outputs x := by simpa only [one_mul,pow_one] using CylinderEvalConjunction.outputs x

def constantBitProgram (b : Bool) (_ : Unit) : TM2.Stmt (fun _ : Fin 2=>Bool) Unit Unit :=
  .push 1 (fun _=>b) .halt

def constantBitMachine (b : Bool) := ofFinite (0 : Fin 2) 1 () () (constantBitProgram b)

theorem constantBit_outputs (b : Bool) (x : List Bool) :
    (constantBitMachine b).OutputsWithin x [b] 1 := by
  apply outputsWithin_of_raw_run (0 : Fin 2) 1 () () (constantBitProgram b) x [b] 1 1 le_rfl
  · rfl
  · rfl

def constantBit (b : Bool) : Producer :=
  ⟨constantBitMachine b,fun _=>[b],1,0,by simpa using constantBit_outputs b⟩

def address : Producer :=
  compose (StoredRetainedGetter.bank2
    (compose (StoredRetainedGetter.bank2 (projection (0 : Fin 3)) (projection (1 : Fin 3)))
      LawJobBinaryProduct.multiply) (projection (2 : Fin 3))) LawJobBinaryProduct.add

theorem address_packet (row width col : List Bool) :
    address.result (BitMachineBankCodec.encode ![row,width,col])=
      (EncodedCommunication.bitsValue row*EncodedCommunication.bitsValue width+
        EncodedCommunication.bitsValue col).bits := by
  simp only [address,compose,Function.comp_apply,StoredRetainedGetter.bank2_result]
  simp only [projection,BankFieldProjection.result_encode,Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.cons_val_two]
  rw [LawJobBinaryProduct.multiply_packet,LawJobBinaryProduct.add_packet,
    EncodedCommunication.bitsValue_bits]
  rfl

end
end CurrentAdditive.StoredCellPrimitives

#print axioms CurrentAdditive.StoredCellPrimitives.address
#print axioms CurrentAdditive.StoredCellPrimitives.countBits_law
