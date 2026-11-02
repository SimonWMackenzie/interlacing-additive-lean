import CurrentAdditive.IndexedLawBytesModel
import CurrentAdditive.PhysicalProducer
import CurrentAdditive.CodeDPacketRouting
import CurrentAdditive.DynamicGetterPrimitives
import EthInapproximability.CurrentPaper.BitMachineCopy

noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 16384
namespace CurrentAdditive.IndexedLawBytes
open Turing EthInapproximability.CurrentPaper BitMachineEncoding PhysicalProducer

def identity : Producer where
  machine := BitMachineCopy.bitMachine
  result := id
  coefficient := 2
  degree := 1
  outputs x := by simpa only [pow_one,Nat.mul_add,Nat.mul_one,id_eq] using BitMachineCopy.bitMachine_outputs x

def unaryBinary : Producer where
  machine := UnaryBinaryEncoding.machine
  result := fun x => x.length.bits
  coefficient := UnaryBinaryEncoding.coefficient
  degree := 2
  outputs := UnaryBinaryEncoding.outputs

def unarySuccProgram (_ : Unit) : TM2.Stmt (fun _ : Fin 1 => Bool) Unit Unit :=
  .push 0 (fun _ => true) .halt

def unarySuccMachine : BitMachine.Machine := ofFinite (0 : Fin 1) 0 () () unarySuccProgram

theorem unarySucc_outputs (x : List Bool) : unarySuccMachine.OutputsWithin x (true::x) 1 := by
  apply outputsWithin_of_raw_run (0 : Fin 1) 0 () () unarySuccProgram x (true::x) 1 1 le_rfl
  · rfl
  · rfl

def unarySucc : Producer where
  machine := unarySuccMachine
  result := fun x => true::x
  coefficient := 1
  degree := 0
  outputs x := by simpa only [pow_zero,Nat.mul_one] using unarySucc_outputs x

end CurrentAdditive.IndexedLawBytes
