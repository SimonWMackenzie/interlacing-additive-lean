import CurrentAdditive.V40LawJobsClock
import CurrentAdditive.LawJobBinaryProduct
import CurrentAdditive.FeatureMapListCount

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 32768

namespace CurrentAdditive.V40LawJobsRouting
open EthInapproximability.CurrentPaper
open PhysicalProducer V40LawJobsClock
noncomputable section

def headerProducer : Producer where
  machine := ProtocolBinaryHeader.machine
  result := ProtocolBinaryHeader.result
  coefficient := 2
  degree := 1
  outputs x := by simpa only [pow_one,Nat.mul_add,Nat.mul_one] using ProtocolBinaryHeader.outputs x

def tailProducer : Producer where
  machine := FeatureMapListCount.tailMachine
  result := List.tail
  coefficient := 1
  degree := 0
  outputs x := by simpa using FeatureMapListCount.tail_outputs x

def countBits : Producer := PhysicalProducer.compose headerProducer tailProducer

theorem countBits_encode (xs : List (List Bool)) :
    countBits.result (SourceListEncoding.encode xs)=xs.length.bits := by
  have h := FeatureMapListCount.header_outputs xs.length (SourceListEncoding.fields xs)
  change countBits.machine.OutputsWithin (SourceListEncoding.encode xs) xs.length.bits _ at h
  exact BitMachine.outputsWithin_unique _ (countBits.outputs _) h

def input (q : List Bool) (xs ys : List (List Bool)) : List Bool :=
  BitMachineBankCodec.encode (![q,SourceListEncoding.encode xs,SourceListEncoding.encode ys] : Fin 3 → List Bool)

def left : Producer := projection (1 : Fin 3)
def right : Producer := projection (2 : Fin 3)
def rightCount : Producer := PhysicalProducer.compose right countBits
def leftCount : Producer := PhysicalProducer.compose left countBits
def productCount : Producer := PhysicalProducer.compose (pair leftCount rightCount) LawJobBinaryProduct.multiply
def outerContext : Producer := pair rightCount right
def mapInput : Producer := pair outerContext left
def retained : Producer := pair identity productCount
def prepare : Producer := pair retained mapInput

theorem prepare_input (q : List Bool) (xs ys : List (List Bool)) :
    prepare.result (input q xs ys)=
      V40LawPacket.packet
        (V40LawPacket.packet (input q xs ys) (xs.length*ys.length).bits)
        (V40LawPacket.packet
          (V40LawPacket.packet ys.length.bits (SourceListEncoding.encode ys))
          (SourceListEncoding.encode xs)) := by
  simp [prepare,retained,mapInput,outerContext,productCount,rightCount,leftCount,
    pair_result,identity_result,PhysicalProducer.compose,Function.comp_apply,left,right,
    projection,input,BankFieldProjection.result_encode,
    countBits_encode,LawJobBinaryProduct.multiply_nats,
    packet_eq]

def saved : Producer := projection (0 : Fin 2)
def fields : Producer := projection (1 : Fin 2)
def original : Producer := PhysicalProducer.compose saved (projection (0 : Fin 2))
def count : Producer := PhysicalProducer.compose saved (projection (1 : Fin 2))
def countedRecords : Producer := PhysicalProducer.concat (PhysicalProducer.compose count field) fields
def finishCartesian : Producer := pair original countedRecords

theorem finishCartesian_input (originalWord : List Bool) (n : ℕ) (payload : List Bool) :
    finishCartesian.result (V40LawPacket.packet (V40LawPacket.packet originalWord n.bits) payload)=
      V40LawPacket.packet originalWord (EncodedCommunication.natField n ++ payload) := by
  simp [finishCartesian,countedRecords,count,original,saved,fields,PhysicalProducer.compose,
    PhysicalProducer.concat,projection,field,packet_eq,EncodedCommunication.natField]

def source : Producer := projection (0 : Fin 2)
def parts : Producer := projection (1 : Fin 2)
def jobs : Producer := PhysicalProducer.compose parts (projection (0 : Fin 2))
def companions : Producer := PhysicalProducer.compose parts (projection (1 : Fin 2))
def qPort : Producer := PhysicalProducer.compose source (projection (0 : Fin 3))
def finish : Producer := triple source (pair qPort jobs) companions

theorem finish_input (q : List Bool) (xs ys : List (List Bool)) (jobsWord companionWord : List Bool) :
    finish.result (V40LawPacket.packet (input q xs ys)
      (V40LawPacket.packet jobsWord companionWord))=
      BitMachineBankCodec.encode (![input q xs ys,V40LawPacket.packet q jobsWord,companionWord] : Fin 3 → List Bool) := by
  simp [finish,source,qPort,jobs,companions,parts,PhysicalProducer.compose,projection,input,packet_eq]

#print axioms countBits_encode
#print axioms prepare_input
#print axioms finishCartesian_input
#print axioms finish_input
end
end CurrentAdditive.V40LawJobsRouting
