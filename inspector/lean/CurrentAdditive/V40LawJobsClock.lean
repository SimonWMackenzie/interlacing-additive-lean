import CurrentAdditive.V40LawBankClock
import CurrentAdditive.V40LawListClock
import CurrentAdditive.AppendOrdinaryPrep
import EthInapproximability.CurrentPaper.ComplexityReductionClosure

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 32768

namespace CurrentAdditive.V40LawJobsClock
open EthInapproximability.CurrentPaper
open PhysicalProducer
noncomputable section

/-- A byte-clock statement about a specified fixed machine on a typed input
family. The following lemmas compose existing physical machines only. -/
def Realizes {α : Type*} (M : BitMachine.Machine)
    (input output : α → List Bool) : Prop :=
  ∃ c d : ℕ, ∀ a, M.OutputsWithin (input a) (output a)
    (c*((input a).length+1)^d)

theorem producer {α : Type*} (P : Producer) (input : α → List Bool) :
    Realizes P.machine input (fun a => P.result (input a)) :=
  ⟨P.coefficient,P.degree,fun a => P.outputs (input a)⟩

theorem compose {α : Type*} (M N : BitMachine.Machine)
    (input middle output : α → List Bool)
    (hM : Realizes M input middle) (hN : Realizes N middle output) :
    Realizes (BitMachineComposition.composition M N) input output := by
  obtain ⟨c,d,hM⟩ := hM
  obtain ⟨a,e,hN⟩ := hN
  refine ⟨c+2*(c*M.pushBound+1)+a*(c*M.pushBound+1)^e,(d+1)*(e+1),?_⟩
  intro i
  exact BitMachine.outputsWithin_mono _
    (BitMachineComposition.composition_outputsWithin M N (hM i) (hN i))
    (BitMachineCompositionArithmetic.composition_time_bound
      (input i).length c d a e M.pushBound (middle i).length
      (BitMachine.output_length_bound M (hM i)))

theorem bank_map {α : Type*} (M : BitMachine.Machine)
    (header input output : α → List Bool) (hM : Realizes M input output) :
    Realizes (V40LawBankMap.liftMachine M)
      (fun a => V40LawPacket.packet (header a) (input a))
      (fun a => V40LawPacket.packet (header a) (output a)) := by
  obtain ⟨c,d,hM⟩ := hM
  refine ⟨10*(c+1)*(M.pushBound+1)*3^(d+1),d+1,?_⟩
  intro a
  apply BitMachine.outputsWithin_mono _
    (V40LawBankMap.outputs_polynomial M c d (header a) (input a) (output a) (hM a))
  have h : (V40LawPacket.packet (header a) (input a)).length+3 ≤
      3*((V40LawPacket.packet (header a) (input a)).length+1) := by omega
  have hp := Nat.mul_le_mul_left (10*(c+1)*(M.pushBound+1))
    (Nat.pow_le_pow_left h (d+1))
  simpa only [mul_pow,Nat.mul_assoc] using hp

def identity : Producer where
  machine := ComplexityReductionClosure.identityMachine
  result := id
  coefficient := 1
  degree := 0
  outputs input := by
    refine ⟨1,by simp,?_,?_⟩ <;>
      simp [BitMachine.Machine.run,BitMachine.Machine.step,BitMachine.Machine.init,
        ComplexityReductionClosure.identityMachine,Turing.TM2.step,Turing.TM2.stepAux]

def pair (A B : Producer) : Producer :=
  PhysicalProducer.concat (PhysicalProducer.compose A field) (PhysicalProducer.compose B field)

def triple (A B C : Producer) : Producer :=
  PhysicalProducer.concat (PhysicalProducer.compose A field)
    (PhysicalProducer.concat (PhysicalProducer.compose B field) (PhysicalProducer.compose C field))

@[simp] theorem pair_result (A B : Producer) (x : List Bool) :
    (pair A B).result x = BitMachineBankCodec.encode (![A.result x,B.result x] : Fin 2 → List Bool) := by
  simp [pair,PhysicalProducer.concat,PhysicalProducer.compose,field,
    BitMachineBankCodec.encode_eq_list]

@[simp] theorem triple_result (A B C : Producer) (x : List Bool) :
    (triple A B C).result x =
      BitMachineBankCodec.encode (![A.result x,B.result x,C.result x] : Fin 3 → List Bool) := by
  simp [triple,PhysicalProducer.concat,PhysicalProducer.compose,field,
    BitMachineBankCodec.encode_eq_list]

@[simp] theorem identity_result (x : List Bool) : identity.result x=x := rfl

@[simp] theorem packet_eq (a b : List Bool) :
    V40LawPacket.packet a b=BitMachineBankCodec.encode (![a,b] : Fin 2 → List Bool) := by
  unfold V40LawPacket.packet
  congr 1
  funext i
  fin_cases i <;> rfl

#print axioms compose
#print axioms bank_map
#print axioms pair_result
end
end CurrentAdditive.V40LawJobsClock
