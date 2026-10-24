import EthInapproximability.CurrentPaper.BitMachineComposition

/-! Physical composition when two checked valid-input executions are both
clocked by the original input length. Intermediate transfer bytes follow
from the actual first execution, without an output-size premise. -/
noncomputable section
set_option autoImplicit false
namespace CurrentAdditive.FeaturePhysicalCompositionBounds
open EthInapproximability.CurrentPaper

def coefficient (ca cb pushes : Nat) := ca+2*ca*pushes+cb+2
def exponent (da db : Nat) := da+db+1

theorem time_bound (n ca da cb db pushes middle : Nat)
    (hsize : middle ≤ n+ca*(n+1)^da*pushes) :
    ca*(n+1)^da+2*middle+2+cb*(n+1)^db ≤
      coefficient ca cb pushes*(n+1)^(exponent da db) := by
  have hbase : 1 ≤ n+1 := by omega
  have ha := Nat.pow_le_pow_right hbase (show da ≤ exponent da db by dsimp [exponent]; omega)
  have hb := Nat.pow_le_pow_right hbase (show db ≤ exponent da db by dsimp [exponent]; omega)
  have hn := Nat.pow_le_pow_right hbase (show 1 ≤ exponent da db by dsimp [exponent]; omega)
  simp only [pow_one] at hn
  have hca := Nat.mul_le_mul_left ca ha
  have hcap := Nat.mul_le_mul_right pushes hca
  have hcb := Nat.mul_le_mul_left cb hb
  dsimp only [coefficient]
  nlinarith

theorem outputs (A B : BitMachine.Machine) (input middle output : List Bool)
    (ca da cb db : Nat)
    (ha : A.OutputsWithin input middle (ca*(input.length+1)^da))
    (hb : B.OutputsWithin middle output (cb*(input.length+1)^db)) :
    (BitMachineComposition.composition A B).OutputsWithin input output
      (coefficient ca cb A.pushBound*(input.length+1)^(exponent da db)) := by
  apply BitMachine.outputsWithin_mono _
    (BitMachineComposition.composition_outputsWithin A B ha hb)
  exact time_bound input.length ca da cb db A.pushBound middle.length
    (BitMachine.output_length_bound A ha)

def inputCoefficient (ca cb db pushes : Nat) :=
  ca+2*(ca*pushes+1)+cb*(ca*pushes+1)^db
def inputExponent (da db : Nat) := (da+1)*(db+1)

theorem outputs_input_clock (A B : BitMachine.Machine) (input middle output : List Bool)
    (ca da cb db : Nat)
    (ha : A.OutputsWithin input middle (ca*(input.length+1)^da))
    (hb : B.OutputsWithin middle output (cb*(middle.length+1)^db)) :
    (BitMachineComposition.composition A B).OutputsWithin input output
      (inputCoefficient ca cb db A.pushBound*(input.length+1)^(inputExponent da db)) := by
  apply BitMachine.outputsWithin_mono _
    (BitMachineComposition.composition_outputsWithin A B ha hb)
  exact BitMachineCompositionArithmetic.composition_time_bound
    input.length ca da cb db A.pushBound middle.length
      (BitMachine.output_length_bound A ha)

#print axioms outputs
#print axioms outputs_input_clock
end CurrentAdditive.FeaturePhysicalCompositionBounds
