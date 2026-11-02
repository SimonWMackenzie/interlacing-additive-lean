import CurrentAdditive.V40LawJobsClock
import CurrentAdditive.V40LawCodeDPacket

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 32768

namespace CurrentAdditive.V40LawSerializeJobs
open EthInapproximability.CurrentPaper
open PhysicalProducer V40LawJobsClock
noncomputable section

def original : Producer := projection (0 : Fin 3)
def request : Producer := projection (1 : Fin 3)
def companion : Producer := projection (2 : Fin 3)
def prepare : Producer := pair (pair original companion) request

def saved : Producer := projection (0 : Fin 2)
def body : Producer := projection (1 : Fin 2)
def finish : Producer := triple
  (PhysicalProducer.compose saved (projection (0 : Fin 2))) body
  (PhysicalProducer.compose saved (projection (1 : Fin 2)))

def first : BitMachine.Machine := BitMachineComposition.composition prepare.machine
  (V40LawBankMap.liftMachine V40LawCodeDPacket.machine)
def machine : BitMachine.Machine := BitMachineComposition.composition first finish.machine

def input (originalWord : List Bool) (q : ℕ) (jobs : List V40LawProductList.Job)
    (companionWord : List Bool) : List Bool :=
  BitMachineBankCodec.encode (![originalWord,V40LawCodeDPacket.input q jobs,companionWord] : Fin 3 → List Bool)

def output (originalWord : List Bool) (q : ℕ) (jobs : List V40LawProductList.Job)
    (companionWord : List Bool) : List Bool :=
  BitMachineBankCodec.encode (![originalWord,
    V40LawCodeDPacket.codeDInput q (V40LawProductList.alphabet jobs),companionWord] : Fin 3 → List Bool)

theorem prepare_input (o : List Bool) (q : ℕ) (jobs : List V40LawProductList.Job)
    (c : List Bool) :
    prepare.result (input o q jobs c)=
      V40LawPacket.packet (V40LawPacket.packet o c) (V40LawCodeDPacket.input q jobs) := by
  simp [prepare,original,companion,request,input,projection,packet_eq]

theorem finish_input (o c word : List Bool) :
    finish.result (V40LawPacket.packet (V40LawPacket.packet o c) word)=
      BitMachineBankCodec.encode (![o,word,c] : Fin 3 → List Bool) := by
  simp [finish,saved,body,PhysicalProducer.compose,projection,packet_eq]

/-- Canonical multiplication is physically executed on each ordered job.
Both the original input and its decoder companions remain literal output
fields of the same fixed ordinary-input machine. -/
theorem realizes {α : Type*} (originalWord : α → List Bool) (q : α → ℕ)
    (jobs : α → List V40LawProductList.Job) (companionWord : α → List Bool) :
    Realizes machine
      (fun a => input (originalWord a) (q a) (jobs a) (companionWord a))
      (fun a => output (originalWord a) (q a) (jobs a) (companionWord a)) := by
  have h0 := producer prepare
    (fun a => input (originalWord a) (q a) (jobs a) (companionWord a))
  simp only [prepare_input] at h0
  have hInner : Realizes V40LawCodeDPacket.machine
      (fun a => V40LawCodeDPacket.input (q a) (jobs a))
      (fun a => V40LawCodeDPacket.codeDInput (q a) (V40LawProductList.alphabet (jobs a))) := by
    obtain ⟨C,d,h⟩ := V40LawCodeDPacket.outputs
    refine ⟨C*3^d,d,?_⟩
    intro a
    apply BitMachine.outputsWithin_mono _ (h (q a) (jobs a))
    have hp : (V40LawCodeDPacket.input (q a) (jobs a)).length+3 ≤
        3*((V40LawCodeDPacket.input (q a) (jobs a)).length+1) := by omega
    have hb := Nat.mul_le_mul_left C (Nat.pow_le_pow_left hp d)
    simpa only [mul_pow,Nat.mul_assoc] using hb
  have h1 := bank_map _ (fun a => V40LawPacket.packet (originalWord a) (companionWord a)) _ _ hInner
  have h2 := producer finish (fun a => V40LawPacket.packet
    (V40LawPacket.packet (originalWord a) (companionWord a))
    (V40LawCodeDPacket.codeDInput (q a) (V40LawProductList.alphabet (jobs a))))
  simp only [finish_input] at h2
  exact V40LawJobsClock.compose _ _ _ _ _ (V40LawJobsClock.compose _ _ _ _ _ h0 h1) h2

#print axioms realizes
end
end CurrentAdditive.V40LawSerializeJobs
