import CurrentAdditive.PhysicalProducer
import EthInapproximability.CurrentPaper.BitMachineEncoding

/-! A finite literal printer. Each literal push is an actual instruction in
the fixed statement; its length is part of the fixed machine push bound. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 8192
namespace CurrentAdditive.CodeDFixedWordProducer
open Turing EthInapproximability.CurrentPaper BitMachineEncoding

def pushes : List Bool → TM2.Stmt (fun _ : Fin 2 => Bool) Unit Unit
  | [] => .halt
  | b::bs => .push 1 (fun _ => b) (pushes bs)

theorem pushes_aux (bits : List Bool) (S : Fin 2 → List Bool) :
    TM2.stepAux (pushes bits) () S=⟨none,(),Function.update S 1 (bits.reverse++S 1)⟩ := by
  induction bits generalizing S with
  | nil => simp [pushes,TM2.stepAux,Function.update_eq_self]
  | cons b bs ih =>
    simp only [pushes,TM2.stepAux]
    rw [ih]
    simp only [Function.update_self,Function.update_idem,List.reverse_cons,List.append_assoc]
    rfl

noncomputable def machine (word : List Bool) : BitMachine.Machine :=
  ofFinite (0 : Fin 2) 1 () () (fun _ => pushes word.reverse)

theorem outputs (word input : List Bool) :
    (machine word).OutputsWithin input word 1 := by
  apply outputsWithin_of_raw_run (0 : Fin 2) 1 () () (fun _ => pushes word.reverse) input word 1 1 le_rfl
  · simp [Function.iterate_one,advance,TM2.step,rawInit,pushes_aux]
  · simp [Function.iterate_one,advance,TM2.step,rawInit,pushes_aux]

noncomputable def producer (word : List Bool) : PhysicalProducer.Producer where
  machine := machine word
  result := fun _ => word
  coefficient := 1
  degree := 0
  outputs x := by simpa only [pow_zero,Nat.mul_one] using outputs word x

#print axioms outputs
#print axioms producer
end CurrentAdditive.CodeDFixedWordProducer
