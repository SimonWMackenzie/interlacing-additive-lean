import CurrentAdditive.AppendEntryPhysical

namespace CurrentAdditive.AppendOrdinaryPrep
open Turing EthInapproximability.CurrentPaper BitMachineEncoding
open PhysicalProducer
noncomputable section

def swap := concat (compose (projection (1 : Fin 2)) field)
  (compose (projection (0 : Fin 2)) field)

theorem swap_packet (a b : List Bool) :
    swap.result (BitMachineBankCodec.encode (![a,b] : Fin 2 → List Bool)) =
      BitMachineBankCodec.encode (![b,a] : Fin 2 → List Bool) := by
  simp only [swap,AppendEntryPhysical.concat_result,AppendEntryPhysical.compose_result,
    AppendEntryPhysical.projection_result,BankFieldProjection.result_encode]
  simp [PhysicalProducer.field,BitMachineBankCodec.encode_eq_list]

def oneProgram (_ : Unit) : TM2.Stmt (fun _ : Fin 2 => Bool) Unit Unit :=
  .push 1 (fun _ => true) .halt

def oneMachine : BitMachine.Machine := ofFinite (0 : Fin 2) 1 () () oneProgram

theorem one_outputs (x : List Bool) : oneMachine.OutputsWithin x [true] 1 := by
  apply outputsWithin_of_raw_run (0 : Fin 2) 1 () () oneProgram x [true] 1 1 le_rfl
  · rfl
  · rfl

def one : Producer where
  machine := oneMachine
  result := fun _ => [true]
  coefficient := 1
  degree := 0
  outputs x := by simpa using one_outputs x

def unaryField : Producer where
  machine := SourceListMachineWriter.framingMachine false
  result := fun x => EncodedCommunication.natField x.length
  coefficient := UnaryBinaryEncoding.coefficient+7
  degree := 2
  outputs x := by simpa [SourceListMachineWriter.result] using
    SourceListMachineWriter.outputs false x

#print axioms swap
#print axioms one_outputs
#print axioms unaryField
end
end CurrentAdditive.AppendOrdinaryPrep
