import CurrentAdditive.V40NativeIterationRuntime
import EthInapproximability.CurrentPaper.BitMachineComposition

/-! The prefix emits the actual driver packet. Its physical output-length
bound supplies the seed length; no seed encoding is advice. -/
namespace CurrentAdditive.V40PipelineSeedBound
noncomputable section
set_option maxHeartbeats 8000000
open EthInapproximability.CurrentPaper

def seedCoefficient (P : BitMachine.Machine) (inputC cp : Nat) := inputC+cp*P.pushBound
def seedDegree (inputD dp : Nat) := inputD+dp

theorem seed_length (P : BitMachine.Machine) (inputC inputD cp dp B K : Nat)
    (x seed : List Bool) (hB : 1 ≤ B)
    (hx : x.length ≤ inputC*B^inputD)
    (hP : P.OutputsWithin x (WeightedIterationDriver.input seed K) (cp*B^dp)) :
    seed.length  ≤  seedCoefficient P inputC cp*B^(seedDegree inputD dp) := by
  have hw := BitMachineBankCodec.word_length_le_encode
    (![seed,List.replicate K true] : Fin 2 → List Bool) (0:Fin 2)
  have hseed : seed.length ≤ (WeightedIterationDriver.input seed K).length := by
    simpa only [WeightedIterationDriver.input,WeightedIterationLoader.packet,Matrix.cons_val_zero] using hw
  have ho := BitMachine.output_length_bound P hP
  have hi := Nat.pow_le_pow_right hB (show inputD ≤ inputD+dp by omega)
  have hp := Nat.pow_le_pow_right hB (show dp ≤ inputD+dp by omega)
  have hix := Nat.mul_le_mul_left inputC hi
  have hpx := Nat.mul_le_mul_left (cp*P.pushBound) hp
  unfold seedCoefficient seedDegree
  nlinarith

#print axioms seed_length
end
end CurrentAdditive.V40PipelineSeedBound
