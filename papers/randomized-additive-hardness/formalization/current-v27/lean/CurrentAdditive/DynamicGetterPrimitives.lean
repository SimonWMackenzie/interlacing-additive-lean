import CurrentAdditive.PhysicalProducer
import EthInapproximability.CurrentPaper.SourceInputLengthUnary

namespace CurrentAdditive.DynamicGetterPrimitives
open Turing EthInapproximability.CurrentPaper BitMachineEncoding PhysicalProducer
noncomputable section

def emptyProgram (_ : Unit) : TM2.Stmt (fun _ : Fin 2 => Bool) Unit Unit := .halt
def emptyMachine : BitMachine.Machine := ofFinite (0 : Fin 2) 1 () () emptyProgram
theorem empty_outputs (x : List Bool) : emptyMachine.OutputsWithin x [] 1 := by
  apply outputsWithin_of_raw_run (0 : Fin 2) 1 () () emptyProgram x [] 1 1 le_rfl
  · rfl
  · rfl
def empty : Producer where
  machine := emptyMachine
  result := fun _ => []
  coefficient := 1
  degree := 0
  outputs x := by simpa using empty_outputs x

def tailProgram (_ : Unit) : TM2.Stmt (fun _ : Fin 1 => Bool) Unit (Option Bool) :=
  .pop 0 (fun _ b => b) .halt
def tailMachine : BitMachine.Machine := ofFinite (0 : Fin 1) 0 () none tailProgram
theorem tail_outputs (x : List Bool) : tailMachine.OutputsWithin x x.tail 1 := by
  apply outputsWithin_of_raw_run (0 : Fin 1) 0 () none tailProgram x x.tail 1 1 le_rfl
  · rfl
  · cases x <;> rfl
def tail : Producer where
  machine := tailMachine
  result := List.tail
  coefficient := 1
  degree := 0
  outputs x := by simpa using tail_outputs x

def lengthMachine : BitMachine.Machine := ofFinite (0 : Fin 4) 3
  (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)
  (none,none) SourceInputLengthUnary.program

theorem length_outputs (x : List Bool) : lengthMachine.OutputsWithin x
    (List.replicate x.length true) (4*(x.length+1)) := by
  obtain ⟨t,ht,hr⟩ := SourceInputLengthUnary.length_run x
  have hi : rawInit (0 : Fin 4)
      (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)
      (none,none) x =
      (⟨some (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan),
       (none,none),SourceInputLengthUnary.contents x [] [] []⟩ :
        SourceInputLengthUnary.Config) := by
    unfold rawInit
    congr 1
    funext k
    fin_cases k <;> rfl
  apply outputsWithin_of_raw_run (0 : Fin 4) 3
    (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)
    (none,none) SourceInputLengthUnary.program x _ t _ (by omega)
  · rw [hi,hr]
  · rw [hi,hr]; rfl

def literalLength : Producer where
  machine := lengthMachine
  result := fun x => List.replicate x.length true
  coefficient := 4
  degree := 1
  outputs x := by simpa only [pow_one] using length_outputs x

#print axioms literalLength
#print axioms tail
end
end CurrentAdditive.DynamicGetterPrimitives
