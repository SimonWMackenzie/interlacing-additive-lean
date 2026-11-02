import CurrentAdditive.PhysicalProducer
import EthInapproximability.CurrentPaper.BitMachineBinaryAddAny

/-! A literal ordinary-input binary addition primitive for dynamic source
addresses. Its output may keep harmless high zero bits; its numeric value
is exact, and every input word has one polynomial physical clock. -/

set_option maxHeartbeats 1000000

namespace CurrentAdditive.StoredBinaryAdd

open Turing EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineBankCodec
open CurrentAdditive.PhysicalProducer

def rawFinal (S : Bank 3) : Bank 3 :=
  ![ (S 2).reverse++BitMachineBinaryAddAny.addAny (S 0) (S 1) false,[],[] ]

theorem bank_length (S : Bank 3) :
    (encode S).length=2*(S 0).length+2*(S 1).length+2*(S 2).length+3 := by
  simp [encode_length,Fin.sum_univ_succ]
  omega

theorem raw_run (S : Bank 3) :
    ((advance BitMachineBinaryAddAny.program)^[2*max (S 0).length (S 1).length+(S 2).length+2])
      (⟨some .scan,BitMachineBinaryAddAny.initial,S⟩ : TM2.Cfg _ _ _)=
        ⟨none,BitMachineBinaryAddAny.initial,rawFinal S⟩ := by
  have hs : S=BitMachineBinaryAddAny.bank (S 0) (S 1) (S 2) := by
    funext i
    fin_cases i <;> rfl
  have h:=BitMachineBinaryAddAny.scan_correct (S 0) (S 1) BitMachineBinaryAddAny.initial (S 2)
  change ((advance BitMachineBinaryAddAny.program)^[_])
    (⟨some .scan,BitMachineBinaryAddAny.initial,BitMachineBinaryAddAny.bank (S 0) (S 1) (S 2)⟩ :
      TM2.Cfg _ _ _) = _ at h
  rw [←hs] at h
  convert h using 1
  congr 1
  funext i
  fin_cases i <;> rfl

theorem raw_time (S : Bank 3) :
    2*max (S 0).length (S 1).length+(S 2).length+2≤4*((encode S).length+1) := by
  rw [bank_length]
  omega

theorem raw_size (S : Bank 3) :
    (encode (rawFinal S)).length≤3*((encode S).length+1) := by
  rw [bank_length,bank_length]
  change 2*((S 2).reverse++BitMachineBinaryAddAny.addAny (S 0) (S 1) false).length+2*0+2*0+3≤_
  simp only [List.length_append,List.length_reverse,BitMachineBinaryAddAny.addAny_length]
  omega

noncomputable def rawMachine : BitMachine.Machine :=
  BitMachineBankWrapper.machine BitMachineBinaryAddAny.program .scan BitMachineBinaryAddAny.initial

theorem raw_outputs (word : List Bool) :
    rawMachine.OutputsWithin word (BitMachineBankWrapper.result rawFinal word)
      (21*(word.length+1)^3) := by
  have h:=BitMachineBankWrapper.outputs BitMachineBinaryAddAny.program .scan
    BitMachineBinaryAddAny.initial rawFinal word (4*(word.length+1)) (3*(word.length+1))
    (by
      intro S hS
      refine ⟨_,⟨none,BitMachineBinaryAddAny.initial,rawFinal S⟩,?_,raw_run S,rfl,rfl⟩
      have he:=BitMachineBankCodec.encode_decode hS
      simpa only [he] using raw_time S)
    (by
      intro S hS
      have he:=BitMachineBankCodec.encode_decode hS
      simpa only [he] using raw_size S)
  apply BitMachine.outputsWithin_mono rawMachine h
  have hp : word.length+1≤(word.length+1)^3:=le_self_pow (by omega) (by decide)
  nlinarith

noncomputable def rawProducer : Producer :=
  ⟨rawMachine,BitMachineBankWrapper.result rawFinal,21,3,raw_outputs⟩

noncomputable def emptyMachine : BitMachine.Machine :=
  ofFinite (0 : Fin 2) 1 () () (fun _ => .halt)

theorem empty_outputs (word : List Bool) : emptyMachine.OutputsWithin word [] 1 := by
  apply outputsWithin_of_raw_run (0 : Fin 2) 1 () () (fun _ => .halt) word [] 1 1 le_rfl
  · rfl
  · rfl

noncomputable def empty : Producer := ⟨emptyMachine,fun _=>[],1,0,by simpa using empty_outputs⟩

noncomputable def prepare : Producer := concat
  (compose (projection (0 : Fin 2)) field)
  (concat (compose (projection (1 : Fin 2)) field) (compose empty field))

noncomputable def producer : Producer :=
  compose (compose prepare rawProducer) (projection (0 : Fin 3))

noncomputable def machine : BitMachine.Machine := producer.machine

theorem prepare_packet (a b : List Bool) :
    prepare.result (encode ![a,b])=encode ![a,b,[]] := by
  simp only [prepare,concat,compose,projection,field,empty,Function.comp_apply,
    BankFieldProjection.result_encode,Matrix.cons_val_zero,Matrix.cons_val_one]
  simp [encode_eq_list]

theorem result_packet (a b : List Bool) :
    producer.result (encode ![a,b])=BitMachineBinaryAddAny.addAny a b false := by
  simp only [producer,compose,projection,Function.comp_apply,prepare_packet,rawProducer,
    BitMachineBankWrapper.result,decode_encode]
  rw [BankFieldProjection.result_encode]
  simp [rawFinal]

theorem outputs (a b : List Bool) :
    machine.OutputsWithin (encode ![a,b]) (BitMachineBinaryAddAny.addAny a b false)
      (producer.coefficient*((encode ![a,b]).length+1)^producer.degree) := by
  have h:=producer.outputs (encode ![a,b])
  rw [result_packet] at h
  exact h

theorem output_value (a b : List Bool) :
    EncodedCommunication.bitsValue (BitMachineBinaryAddAny.addAny a b false)=
      EncodedCommunication.bitsValue a+EncodedCommunication.bitsValue b :=
  BitMachineBinaryAddAny.result_value a b

end CurrentAdditive.StoredBinaryAdd

#print axioms CurrentAdditive.StoredBinaryAdd.outputs
