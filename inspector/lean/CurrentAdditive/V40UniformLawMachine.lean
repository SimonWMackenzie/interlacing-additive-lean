import CurrentAdditive.V40UniformLawSize

namespace CurrentAdditive.V40UniformLaw
noncomputable section
set_option maxHeartbeats 16000000
set_option maxRecDepth 32768
open EthInapproximability.CurrentPaper BitMachineComposition
open V40UniformLawLoop

def prepared (n : Nat) := WeightedIterationDriver.input (state n 0) n
def initializationClock (n : Nat) := withFuel.coefficient*(n+1)^withFuel.degree
def middleMachine := composition withFuel.machine loopMachine
def middleClock (n : Nat) := initializationClock n+2*(prepared n).length+2+loopBound n
def machine := composition middleMachine (BankFieldProjection.machine (2:Fin 3))
def clock (n : Nat) := middleClock n+2*(state n n).length+2+10*((state n n).length+1)
def word (n : Nat) := SourceListEncoding.encode (entries n n)

theorem outputs_word (n : Nat) (hn : 0<n) :
    machine.OutputsWithin (List.replicate n true) (word n) (clock n) := by
  have hi : withFuel.machine.OutputsWithin (List.replicate n true) (prepared n)
      (initializationClock n) := by
    simpa only [withFuel_result,prepared,initializationClock,List.length_replicate] using
      withFuel.outputs (List.replicate n true)
  have hm := composition_outputsWithin withFuel.machine loopMachine hi (loop_outputs_bounded n hn)
  have hp := BankFieldProjection.outputs (2:Fin 3) (state n n)
  rw [final_projection] at hp
  simpa only [machine,middleMachine,clock,middleClock,word,prepared] using
    composition_outputsWithin middleMachine (BankFieldProjection.machine (2:Fin 3)) hm hp

theorem outputs (n : Nat) [NeZero n] :
    machine.OutputsWithin (List.replicate n true)
      (StoredWeightedState.lawBytes (Paper2.PositiveRationalLaw.uniform (Fin n))) (clock n) := by
  rw [←entries_uniform]
  exact outputs_word n (NeZero.pos n)

#print axioms outputs
end
end CurrentAdditive.V40UniformLaw
