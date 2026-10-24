import CurrentAdditive.V40LawJobsRouting
import CurrentAdditive.LawMixtureFormatter

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 32768

namespace CurrentAdditive.V40LawMixtureRouting
open EthInapproximability.CurrentPaper
open PhysicalProducer V40LawJobsClock
noncomputable section

def totalCount : Producer := PhysicalProducer.compose
  (pair V40LawJobsRouting.leftCount V40LawJobsRouting.rightCount) LawJobBinaryProduct.add
def rightInput : Producer := pair V40LawJobsRouting.leftCount V40LawJobsRouting.right
def saved : Producer := triple identity totalCount rightInput
def prepare : Producer := pair saved (pair LawJobBitPrimitives.empty V40LawJobsRouting.left)

theorem prepare_input (q : List Bool) (xs ys : List (List Bool)) :
    prepare.result (V40LawJobsRouting.input q xs ys)=
      V40LawPacket.packet
        (BitMachineBankCodec.encode (![V40LawJobsRouting.input q xs ys,(xs.length+ys.length).bits,
          V40LawPacket.packet xs.length.bits (SourceListEncoding.encode ys)] : Fin 3 → List Bool))
        (V40LawPacket.packet (0 : ℕ).bits (SourceListEncoding.encode xs)) := by
  simp [prepare,saved,totalCount,rightInput,V40LawJobsRouting.leftCount,
    V40LawJobsRouting.rightCount,V40LawJobsRouting.left,V40LawJobsRouting.right,
    PhysicalProducer.compose,projection,V40LawJobsRouting.input,V40LawJobsRouting.countBits_encode,
    LawJobBinaryProduct.add_packet,LawJobBitPrimitives.empty,packet_eq]

def header : Producer := projection (0 : Fin 2)
def leftFields : Producer := projection (1 : Fin 2)
def original : Producer := PhysicalProducer.compose header (projection (0 : Fin 3))
def count : Producer := PhysicalProducer.compose header (projection (1 : Fin 3))
def pendingRight : Producer := PhysicalProducer.compose header (projection (2 : Fin 3))
def prepareRight : Producer := pair (triple original count leftFields) pendingRight

theorem prepareRight_input (originalWord countWord rightWord leftWord : List Bool) :
    prepareRight.result (V40LawPacket.packet
      (BitMachineBankCodec.encode (![originalWord,countWord,rightWord] : Fin 3 → List Bool)) leftWord)=
      V40LawPacket.packet
        (BitMachineBankCodec.encode (![originalWord,countWord,leftWord] : Fin 3 → List Bool)) rightWord := by
  simp [prepareRight,original,count,leftFields,pendingRight,header,PhysicalProducer.compose,
    projection,packet_eq]

def oldLeft : Producer := PhysicalProducer.compose header (projection (2 : Fin 3))
def rightFields : Producer := projection (1 : Fin 2)
def counted : Producer := PhysicalProducer.concat (PhysicalProducer.compose count field)
  (PhysicalProducer.concat oldLeft rightFields)
def finish : Producer := pair original counted

theorem finish_input (originalWord : List Bool) (n : ℕ) (leftWord rightWord : List Bool) :
    finish.result (V40LawPacket.packet
      (BitMachineBankCodec.encode (![originalWord,n.bits,leftWord] : Fin 3 → List Bool)) rightWord)=
      V40LawPacket.packet originalWord
        (EncodedCommunication.natField n ++ (leftWord ++ rightWord)) := by
  simp [finish,original,count,header,counted,oldLeft,rightFields,PhysicalProducer.compose,
    PhysicalProducer.concat,field,projection,packet_eq,EncodedCommunication.natField]

#print axioms prepare_input
#print axioms prepareRight_input
#print axioms finish_input
end
end CurrentAdditive.V40LawMixtureRouting
