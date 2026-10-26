import CurrentAdditive.LawJobBinaryProduct
import CurrentAdditive.V40LawProductEntry

/-! One physical Cartesian-product record formatter. The flattened label is
computed by binary multiply/add; original label and canonical rational bytes
are routed unchanged to the job and its decoder companion. -/

namespace CurrentAdditive.LawProductFormatter

open EthInapproximability.CurrentPaper PhysicalProducer LawJobBitPrimitives

noncomputable section

def input (n i j : Nat) (x y : Rat) : List Bool :=
  BitMachineBankCodec.encode ![BitMachineBankCodec.encode ![n.bits,CodeDTargetV2.alphabetEntry (i,x)],
    CodeDTargetV2.alphabetEntry (j,y)]

def output (n i j : Nat) (x y : Rat) : List Bool :=
  BitMachineBankCodec.encode ![V40LawProductEntry.input (i*n+j) x y,
    BitMachineBankCodec.encode ![i.bits,j.bits]]

def context : Producer := projection (0 : Fin 2)
def rightSize : Producer := compose context (projection (0 : Fin 2))
def leftEntry : Producer := compose context (projection (1 : Fin 2))
def rightEntry : Producer := projection (1 : Fin 2)
def leftLabel : Producer := compose leftEntry (projection (0 : Fin 2))
def rightLabel : Producer := compose rightEntry (projection (0 : Fin 2))
def leftRat : Producer := compose leftEntry (projection (1 : Fin 2))
def rightRat : Producer := compose rightEntry (projection (1 : Fin 2))

def flatLabel : Producer :=
  compose (pair (compose (pair leftLabel rightSize) LawJobBinaryProduct.multiply) rightLabel)
    LawJobBinaryProduct.add

def job : Producer := pair flatLabel (pair leftRat rightRat)
def companion : Producer := pair leftLabel rightLabel
def producer : Producer := pair job companion
def machine : BitMachine.Machine := producer.machine

theorem entry_eq (i : Nat) (x : Rat) : CodeDTargetV2.alphabetEntry (i,x)=
    BitMachineBankCodec.encode ![i.bits,CodeDCodec.encodeRawRat (CodeDCanonicalSource.rawOfRat x)] := by
  unfold CodeDTargetV2.alphabetEntry
  congr 1
  funext k
  fin_cases k <;> rfl

theorem pairBytes_eq (x y : CodeDCodec.RawRat) : CodeDPairProductTargetV2.pairBytes x y=
    BitMachineBankCodec.encode ![CodeDCodec.encodeRawRat x,CodeDCodec.encodeRawRat y] := by
  unfold CodeDPairProductTargetV2.pairBytes CodeDPairProductTargetV2.pairBank
  congr 1
  funext k
  fin_cases k <;> rfl

theorem lawPacket_eq (a b : List Bool) : V40LawPacket.packet a b=
    BitMachineBankCodec.encode ![a,b] := by
  unfold V40LawPacket.packet V40LawPacket.bank
  congr 1
  funext k
  fin_cases k <;> rfl

theorem basis_result (n i j : Nat) (x y : Rat) :
    rightSize.result (input n i j x y)=n.bits ∧
    leftLabel.result (input n i j x y)=i.bits ∧
    rightLabel.result (input n i j x y)=j.bits ∧
    leftRat.result (input n i j x y)=CodeDCodec.encodeRawRat (CodeDCanonicalSource.rawOfRat x) ∧
    rightRat.result (input n i j x y)=CodeDCodec.encodeRawRat (CodeDCanonicalSource.rawOfRat y) := by
  simp [rightSize,context,leftLabel,rightLabel,leftRat,rightRat,leftEntry,rightEntry,
    compose,projection,input,entry_eq]

theorem flatLabel_input (n i j : Nat) (x y : Rat) :
    flatLabel.result (input n i j x y)=(i*n+j).bits := by
  obtain ⟨hn,hi,hj,_,_⟩:=basis_result n i j x y
  simp only [flatLabel,compose,Function.comp_apply,pair_result]
  rw [LawJobBinaryProduct.add_packet,LawJobBinaryProduct.multiply_packet,hn,hi,hj]
  simp

theorem result_input (n i j : Nat) (x y : Rat) :
    producer.result (input n i j x y)=output n i j x y := by
  obtain ⟨_,hi,hj,hx,hy⟩:=basis_result n i j x y
  have hjob : job.result (input n i j x y)=V40LawProductEntry.input (i*n+j) x y := by
    simp only [job,pair_result,flatLabel_input,hx,hy,V40LawProductEntry.input,
      lawPacket_eq,pairBytes_eq]
  have hc : companion.result (input n i j x y)=BitMachineBankCodec.encode ![i.bits,j.bits] := by
    simp only [companion,pair_result,hi,hj]
  simp only [producer,pair_result,hjob,hc,output]

theorem outputs (n i j : Nat) (x y : Rat) :
    machine.OutputsWithin (input n i j x y) (output n i j x y)
      (producer.coefficient*((input n i j x y).length+1)^producer.degree) := by
  have h:=producer.outputs (input n i j x y)
  rw [result_input] at h
  exact h

theorem uniform_outputs : ∃ C d : Nat, ∀ (n i j : Nat) (x y : Rat),
    machine.OutputsWithin (input n i j x y) (output n i j x y)
      (C*((input n i j x y).length+1)^d) :=
  ⟨producer.coefficient,producer.degree,outputs⟩

#print axioms result_input
#print axioms outputs
#print axioms uniform_outputs

end
end CurrentAdditive.LawProductFormatter
