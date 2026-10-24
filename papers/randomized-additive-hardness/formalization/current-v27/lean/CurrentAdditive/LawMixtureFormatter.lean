import CurrentAdditive.LawProductFormatter

namespace CurrentAdditive.LawMixtureFormatter

open Turing TM2.Stmt EthInapproximability.CurrentPaper BitMachineEncoding
open PhysicalProducer LawJobBitPrimitives

noncomputable section

def pushWord : List Bool → TM2.Stmt (fun _ : Fin 2=>Bool) Unit Unit
  | []=>halt
  | b::bs=>push 1 (fun _=>b) (pushWord bs)

theorem pushWord_aux (word : List Bool) (S : Fin 2→List Bool) :
    TM2.stepAux (pushWord word) () S =
      ⟨none,(),Function.update S 1 (word.reverse++S 1)⟩ := by
  induction word generalizing S with
  | nil => simp [pushWord,TM2.stepAux]
  | cons b bs ih =>
      simp only [pushWord,TM2.stepAux,ih,Function.update_self,Function.update_idem]
      congr 1
      simp [List.reverse_cons,List.append_assoc]

def literalMachine (word : List Bool) : BitMachine.Machine :=
  ofFinite (0 : Fin 2) 1 () () (fun _=>pushWord word.reverse)

theorem literal_outputs (word input : List Bool) :
    (literalMachine word).OutputsWithin input word (word.length+1) := by
  apply outputsWithin_of_raw_run (0 : Fin 2) 1 () () (fun _=>pushWord word.reverse)
    input word 1 (word.length+1) (by omega)
  · simp [Function.iterate_one,advance,rawInit,TM2.step,pushWord_aux]
  · simp [Function.iterate_one,advance,rawInit,TM2.step,pushWord_aux]

def literal (word : List Bool) : Producer :=
  ⟨literalMachine word,fun _=>word,word.length+1,0,by simpa using literal_outputs word⟩

def mass (branch : Bool) : Rat := if branch then 1/256 else 255/256

def input (offset j : Nat) (y : Rat) : List Bool :=
  BitMachineBankCodec.encode ![offset.bits,CodeDTargetV2.alphabetEntry (j,y)]

def output (branch : Bool) (offset j : Nat) (y : Rat) : List Bool :=
  BitMachineBankCodec.encode ![V40LawProductEntry.input (offset+j) (mass branch) y,
    BitMachineBankCodec.encode ![[branch],j.bits]]

def offsetField : Producer := projection (0 : Fin 2)
def entry : Producer := projection (1 : Fin 2)
def label : Producer := compose entry (projection (0 : Fin 2))
def rational : Producer := compose entry (projection (1 : Fin 2))
def index : Producer := compose (pair offsetField label) LawJobBinaryProduct.add

def job (branch : Bool) : Producer := pair index
  (pair (literal (CodeDCodec.encodeRawRat (CodeDCanonicalSource.rawOfRat (mass branch)))) rational)

def companion (branch : Bool) : Producer := pair (literal [branch]) label
def producer (branch : Bool) : Producer := pair (job branch) (companion branch)
def machine (branch : Bool) : BitMachine.Machine := (producer branch).machine

theorem basis_result (offset j : Nat) (y : Rat) :
    offsetField.result (input offset j y)=offset.bits ∧
    label.result (input offset j y)=j.bits ∧
    rational.result (input offset j y)=CodeDCodec.encodeRawRat (CodeDCanonicalSource.rawOfRat y) := by
  simp [offsetField,label,rational,entry,compose,projection,input,LawProductFormatter.entry_eq]

theorem index_input (offset j : Nat) (y : Rat) :
    index.result (input offset j y)=(offset+j).bits := by
  obtain ⟨ho,hj,_⟩:=basis_result offset j y
  simp only [index,compose,Function.comp_apply,pair_result]
  rw [LawJobBinaryProduct.add_packet,ho,hj]
  simp

theorem result_input (branch : Bool) (offset j : Nat) (y : Rat) :
    (producer branch).result (input offset j y)=output branch offset j y := by
  obtain ⟨_,hj,hy⟩:=basis_result offset j y
  have hjob : (job branch).result (input offset j y)=
      V40LawProductEntry.input (offset+j) (mass branch) y := by
    simp only [job,pair_result,index_input,literal,hy,V40LawProductEntry.input,
      LawProductFormatter.lawPacket_eq,LawProductFormatter.pairBytes_eq]
  have hc : (companion branch).result (input offset j y)=BitMachineBankCodec.encode ![[branch],j.bits] := by
    simp only [companion,pair_result,literal,hj]
  simp only [producer,pair_result,hjob,hc,output]

theorem outputs (branch : Bool) (offset j : Nat) (y : Rat) :
    (machine branch).OutputsWithin (input offset j y) (output branch offset j y)
      ((producer branch).coefficient*((input offset j y).length+1)^(producer branch).degree) := by
  have h:=(producer branch).outputs (input offset j y)
  rw [result_input] at h
  exact h

theorem uniform_outputs (branch : Bool) : ∃ C d : Nat, ∀ (offset j : Nat) (y : Rat),
    (machine branch).OutputsWithin (input offset j y) (output branch offset j y)
      (C*((input offset j y).length+1)^d) :=
  ⟨(producer branch).coefficient,(producer branch).degree,outputs branch⟩

#print axioms literal_outputs
#print axioms result_input
#print axioms uniform_outputs

end
end CurrentAdditive.LawMixtureFormatter
