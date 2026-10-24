import CurrentAdditive.StoredWeightedState
import CurrentAdditive.PhysicalProducer

/-! Physical final-state framing. The cells and the two law packets are
parsed from the supplied original word and serialized into the reusable
three-field state; no final bank is supplied to the execution theorem. -/

namespace CurrentAdditive.StoredWeightedFrame

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineBankCodec
open CurrentAdditive.PhysicalProducer

noncomputable section

def cellField := compose (projection (0 : Fin 2)) field
def rowField := compose (compose (projection (1 : Fin 2)) (projection (0 : Fin 2))) field
def colField := compose (compose (projection (1 : Fin 2)) (projection (1 : Fin 2))) field

def producer := concat cellField (concat rowField colField)
def machine : BitMachine.Machine := producer.machine

def input (cells row col : List Bool) : List Bool :=
  encode ![cells,encode ![row,col]]

def output (cells row col : List Bool) : List Bool := encode ![cells,row,col]

theorem result_packet (cells row col : List Bool) :
    producer.result (input cells row col)=output cells row col := by
  simp only [producer,cellField,rowField,colField,concat,compose,projection,field,input,
    Function.comp_apply,BankFieldProjection.result_encode,Matrix.cons_val_zero,Matrix.cons_val_one]
  simp [output,BitMachineBankCodec.encode_eq_list]

theorem outputs (cells row col : List Bool) :
    machine.OutputsWithin (input cells row col) (output cells row col)
      (producer.coefficient*((input cells row col).length+1)^producer.degree) := by
  have h:=producer.outputs (input cells row col)
  rw [result_packet] at h
  exact h

theorem outputs_state (R : V39GeneratedConstruction.StoredMatrix) :
    machine.OutputsWithin
      (input (StoredWeightedState.cells R) (StoredWeightedState.lawBytes R.rowLaw)
        (StoredWeightedState.lawBytes R.colLaw))
      (StoredWeightedState.encode R)
      (producer.coefficient*
        ((input (StoredWeightedState.cells R) (StoredWeightedState.lawBytes R.rowLaw)
          (StoredWeightedState.lawBytes R.colLaw)).length+1)^producer.degree) :=
  outputs _ _ _

end
end CurrentAdditive.StoredWeightedFrame

#print axioms CurrentAdditive.StoredWeightedFrame.outputs
#print axioms CurrentAdditive.StoredWeightedFrame.outputs_state
