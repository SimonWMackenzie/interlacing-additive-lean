import CurrentAdditive.PhysicalProducer
import EthInapproximability.CurrentPaper.BG34Canon
import EthInapproximability.CurrentPaper.CutoffBitMachine

namespace CurrentAdditive.LawJobBitPrimitives

open Turing TM2.Stmt EthInapproximability.CurrentPaper BitMachineEncoding
open PhysicalProducer

noncomputable section

def emptyMachine : BitMachine.Machine :=
  ofFinite (0 : Fin 2) 1 () () (fun _=>halt)

theorem empty_outputs (q : List Bool) : emptyMachine.OutputsWithin q [] 1 := by
  apply outputsWithin_of_raw_run (0 : Fin 2) 1 () () (fun _=>halt) q [] 1 1 le_rfl
  · rfl
  · rfl

def empty : Producer := ⟨emptyMachine,fun _=>[],1,0,by simpa using empty_outputs⟩

def reverseProgram (_ : Unit) : TM2.Stmt (fun _ : Fin 2=>Bool) Unit (Option Bool) :=
  pop 0 (fun _ b=>b) (branch Option.isSome
    (push 1 (fun b=>b.getD false) (goto (fun _=>()))) halt)

def reverseCfg (l : Option Unit) (v : Option Bool) (q saved : List Bool) :
    TM2.Cfg (fun _ : Fin 2=>Bool) Unit (Option Bool) := ⟨l,v,![q,saved]⟩

theorem reverse_run (q saved : List Bool) (v : Option Bool) :
    ((advance reverseProgram)^[q.length+1]) (reverseCfg (some ()) v q saved) =
      reverseCfg none none [] (q.reverse++saved) := by
  induction q generalizing saved v with
  | nil =>
      simp [advance,reverseProgram,reverseCfg,TM2.step,TM2.stepAux]
  | cons b q ih =>
      have hs : advance reverseProgram (reverseCfg (some ()) v (b::q) saved) =
          reverseCfg (some ()) (some b) q (b::saved) := by
        simp [advance,reverseProgram,reverseCfg,TM2.step,TM2.stepAux]
        funext i
        fin_cases i <;> rfl
      rw [List.length_cons,Function.iterate_succ_apply,hs,ih]
      simp [List.reverse_cons,List.append_assoc]

def reverseMachine : BitMachine.Machine :=
  ofFinite (0 : Fin 2) 1 () (none : Option Bool) reverseProgram

theorem reverse_outputs (q : List Bool) :
    reverseMachine.OutputsWithin q q.reverse (q.length+1) := by
  apply outputsWithin_of_raw_run (0 : Fin 2) 1 () (none : Option Bool) reverseProgram
    q q.reverse (q.length+1) (q.length+1) le_rfl
  all_goals
    have hi : rawInit (0 : Fin 2) () (none : Option Bool) q = reverseCfg (some ()) none q [] := by
      unfold rawInit reverseCfg
      congr 1
      funext i
      fin_cases i <;> rfl
    rw [hi]
    have hr:=reverse_run q [] none
    simp only [List.append_nil] at hr
    rw [hr]
  · rfl
  · rfl

def reverse : Producer := ⟨reverseMachine,List.reverse,1,1,by simpa using reverse_outputs⟩

def canon : Producer := ⟨BG34Canon.machine,BG34Canon.canon,2,1,by
  intro q
  simpa [pow_one,Nat.mul_add] using BG34Canon.outputs q⟩

theorem canon_eq_bits (q : List Bool) :
    BG34Canon.canon q=(EncodedCommunication.bitsValue q).bits := by
  obtain ⟨n,hn⟩:=BG34Canon.canon_canonical q
  have hv:=CutoffBitMachine.Totalizer.bitsValue_canon q
  rw [hn,EncodedCommunication.bitsValue_bits] at hv
  exact hn.trans (congrArg Nat.bits hv)

def pair (A B : Producer) : Producer := concat (compose A field) (compose B field)

theorem pair_result (A B : Producer) (q : List Bool) :
    (pair A B).result q=BitMachineBankCodec.encode ![A.result q,B.result q] := by
  simp [pair,concat,compose,field,BitMachineBankCodec.encode_eq_list]

#print axioms reverse_outputs
#print axioms pair

end
end CurrentAdditive.LawJobBitPrimitives
