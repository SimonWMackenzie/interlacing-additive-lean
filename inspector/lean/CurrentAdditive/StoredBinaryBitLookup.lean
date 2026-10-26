import CurrentAdditive.StoredRetainedGetter
import EthInapproximability.CurrentPaper.ProtocolBitLookup

/-! Literal raw Boolean-vector access from a binary address. Conversion is
bounded by the actual input bytes, so oversized addresses cannot cause an
unpaid exponential unary expansion. The requested answer is asserted only
for an address within the supplied vector. -/

namespace CurrentAdditive.StoredBinaryBitLookup

open EthInapproximability.CurrentPaper PhysicalProducer
noncomputable section

def packet (bits address : List Bool) := BitMachineBankCodec.encode ![bits,address]
def source := projection (0 : Fin 2)
def unary := DynamicGetterOrdinary.unaryIndex
def separator := compose DynamicGetterPrimitives.empty field
def prep := concat unary (concat separator source)
def index (x : List Bool) : Nat :=
  min (EncodedCommunication.bitsValue (DynamicGetterOrdinary.indexBits x)) x.length

theorem unary_result (x : List Bool) :
    unary.result x = List.replicate (index x) true := by
  simp [unary,DynamicGetterOrdinary.unaryIndex,compose,DynamicGetterOrdinary.flag,
    DynamicGetterPrimitives.tail,ProtocolBoundedUnary.result,DynamicGetterOrdinary.budget,index]

theorem prep_result (x : List Bool) :
    prep.result x = ProtocolBitLookup.encodeInput (index x) (source.result x) := by
  simp [prep,concat,unary_result,separator,compose,DynamicGetterPrimitives.empty,field,
    ProtocolBitLookup.encodeInput,EncodedCommunication.field]

def machine := BitMachineComposition.composition prep.machine ProtocolBitLookup.bitMachine

def coefficient := DynamicGetterOrdinary.composeCoefficient prep.machine prep.coefficient 3 1
def degree := DynamicGetterOrdinary.composeDegree prep.degree 1

def producer : Producer where
  machine := machine
  result := fun x => [(source.result x)[index x]?.getD false]
  coefficient := coefficient
  degree := degree
  outputs x := by
    have hp := prep.outputs x
    have h := ProtocolBitLookup.bitMachine_outputs (index x) (source.result x)
    have hm : ProtocolBitLookup.bitMachine.OutputsWithin (prep.result x)
        [(source.result x)[index x]?.getD false] (3*((prep.result x).length+1)^1) := by
      apply BitMachine.outputsWithin_mono _ (by simpa only [prep_result] using h)
      rw [prep_result]
      simp only [pow_one]
      omega
    exact DynamicGetterOrdinary.compose_outputs _ _ _ _ _ _ _ _ _ hp hm

theorem result_packet (bits address : List Bool)
    (hi : EncodedCommunication.bitsValue address < bits.length) :
    producer.result (packet bits address) = [bits[EncodedCommunication.bitsValue address]] := by
  have hb := BitMachineBankCodec.word_length_le_encode (![bits,address]) (0 : Fin 2)
  have hcap : EncodedCommunication.bitsValue address ≤ (packet bits address).length := by
    change bits.length ≤ (packet bits address).length at hb
    omega
  have hi' : index (packet bits address) = EncodedCommunication.bitsValue address := by
    unfold index
    have ha : DynamicGetterOrdinary.indexBits (packet bits address)=address :=
      BankFieldProjection.result_encode (1 : Fin 2) _
    rw [ha,Nat.min_eq_left hcap]
  have hs : source.result (packet bits address)=bits :=
    BankFieldProjection.result_encode (0 : Fin 2) _
  change [(source.result (packet bits address))[index (packet bits address)]?.getD false] = _
  rw [hs]
  rw [hi']
  simp [hi]

theorem outputs (bits address : List Bool)
    (hi : EncodedCommunication.bitsValue address < bits.length) :
    machine.OutputsWithin (packet bits address) [bits[EncodedCommunication.bitsValue address]]
      (coefficient*((packet bits address).length+1)^degree) := by
  have h := producer.outputs (packet bits address)
  rw [result_packet bits address hi] at h
  exact h

end
end CurrentAdditive.StoredBinaryBitLookup

#print axioms CurrentAdditive.StoredBinaryBitLookup.producer
#print axioms CurrentAdditive.StoredBinaryBitLookup.outputs
