import CurrentAdditive.FeatureMapListCount
import EthInapproximability.CurrentPaper.SourceListMachineWriter

namespace CurrentAdditive.FeatureMapHeaders

open Turing EthInapproximability.CurrentPaper BitMachineEncoding

def emptyProgram (_ : Unit) : TM2.Stmt (fun _ : Fin 2 => Bool) Unit Unit := .halt
noncomputable def emptyMachine : BitMachine.Machine :=
 ofFinite (0 : Fin 2) 1 () () emptyProgram

theorem empty_outputs (input : List Bool) : emptyMachine.OutputsWithin input [] 1 := by
 apply outputsWithin_of_raw_run (0 : Fin 2) 1 () () emptyProgram input [] 1 1 le_rfl
 · rfl
 · rfl

noncomputable def machine (framed : Bool) : BitMachine.Machine :=
 if framed then SourceListMachineWriter.framingMachine false else emptyMachine

def output (framed : Bool) (n : Nat) : List Bool :=
 if framed then EncodedCommunication.natField n else []

noncomputable def bound (framed : Bool) (n : Nat) : Nat :=
 if framed then (UnaryBinaryEncoding.coefficient+7)*(n+1)^2 else 1

theorem outputs (framed : Bool) (n : Nat) :
 (machine framed).OutputsWithin (List.replicate n true) (output framed n) (bound framed n) := by
 cases framed
 · exact empty_outputs _
 · simpa [machine,output,bound,SourceListMachineWriter.result] using
     SourceListMachineWriter.outputs false (List.replicate n true)

#print axioms outputs

end CurrentAdditive.FeatureMapHeaders
