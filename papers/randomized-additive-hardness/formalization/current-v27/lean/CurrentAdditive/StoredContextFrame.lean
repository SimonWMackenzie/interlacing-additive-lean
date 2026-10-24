import CurrentAdditive.StoredWeightedFrame
import CurrentAdditive.StoredStepContext

namespace CurrentAdditive.StoredContextFrame

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineBankCodec
open CurrentAdditive.PhysicalProducer

noncomputable section

def contextField := compose (projection (0 : Fin 2)) field
def stateField := compose (compose (projection (1 : Fin 2)) StoredWeightedFrame.producer) field
def producer := concat contextField stateField
def machine : BitMachine.Machine := producer.machine

def input (context cells row col : List Bool) : List Bool :=
  encode ![context,StoredWeightedFrame.input cells row col]

def output (context cells row col : List Bool) : List Bool :=
  encode ![context,StoredWeightedFrame.output cells row col]

theorem result_packet (context cells row col : List Bool) :
    producer.result (input context cells row col)=output context cells row col := by
  simp only [producer,contextField,stateField,concat,compose,projection,field,input,
    Function.comp_apply,BankFieldProjection.result_encode,Matrix.cons_val_zero,Matrix.cons_val_one,
    StoredWeightedFrame.result_packet]
  simp [output,BitMachineBankCodec.encode_eq_list]

theorem outputs (context cells row col : List Bool) :
    machine.OutputsWithin (input context cells row col) (output context cells row col)
      (producer.coefficient*((input context cells row col).length+1)^producer.degree) := by
  have h:=producer.outputs (input context cells row col)
  rw [result_packet] at h
  exact h

theorem outputs_state {ni q₂ s : ℕ} (q₁ w Q : ℕ)
    (μI : Paper2.PositiveRationalLaw (Fin ni))
    (activity : Fin ni → Fin q₂ → Option (Fin s)) (R : V39GeneratedConstruction.StoredMatrix) :
    machine.OutputsWithin
      (input (StoredStepContext.context q₁ w Q μI activity)
        (StoredWeightedState.cells R) (StoredWeightedState.lawBytes R.rowLaw)
        (StoredWeightedState.lawBytes R.colLaw))
      (StoredStepContext.packet q₁ w Q μI activity R)
      (producer.coefficient*
        ((input (StoredStepContext.context q₁ w Q μI activity)
          (StoredWeightedState.cells R) (StoredWeightedState.lawBytes R.rowLaw)
          (StoredWeightedState.lawBytes R.colLaw)).length+1)^producer.degree) :=
  outputs _ _ _ _

end
end CurrentAdditive.StoredContextFrame

#print axioms CurrentAdditive.StoredContextFrame.outputs_state
