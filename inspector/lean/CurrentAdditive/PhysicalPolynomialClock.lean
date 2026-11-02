import CurrentAdditive.PolynomialFuelPrefix
import CurrentAdditive.ClockedPackedWrapper

/-!
An ordinary-input finite-stack clock wrapper.  Its first component physically
builds unary fuel `(input.length + 2)^12`; its second component executes an
arbitrary fixed Boolean-stack program for that fuel and returns `[]` if the
simulation expires.  Both components are literal TM2 programs.
-/
namespace CurrentAdditive.PhysicalPolynomialClock

open EthInapproximability.CurrentPaper

noncomputable def machine (M : BitMachine.Machine) : BitMachine.Machine :=
  BitMachineComposition.composition PolynomialFuelPrefix.machine
    (ClockedPackedWrapper.machine M)

def packed (bits : List Bool) : List Bool :=
  BoundedBitMachine.packed (PolynomialFuelPrefix.clockLength bits) bits

noncomputable def result (M : BitMachine.Machine) (bits : List Bool) : List Bool :=
  ClockedPackedWrapper.result M (packed bits)

noncomputable def time (M : BitMachine.Machine) (bits : List Bool) : ℕ :=
  PolynomialFuelPrefix.rawTime bits + 2*(packed bits).length+2 +
    ClockedPackedWrapper.clockCoefficient M*((packed bits).length+1)

/-- Every ordinary bitstring terminates, including malformed source inputs.
The result is the literal empty default if the source has not halted by the
physically generated clock. -/
theorem outputs_all (M : BitMachine.Machine) (bits : List Bool) :
    (machine M).OutputsWithin bits (result M bits) (time M bits) := by
  exact BitMachineComposition.composition_outputsWithin _ _
    (PolynomialFuelPrefix.outputsWithin_raw bits)
    (ClockedPackedWrapper.outputs_all_linear M (packed bits))

/-- A source run within the twelfth-power budget survives unchanged. -/
theorem outputs_valid (M : BitMachine.Machine) (bits output : List Bool)
    (h : M.OutputsWithin bits output (PolynomialFuelPrefix.clockLength bits)) :
    (machine M).OutputsWithin bits output (time M bits) := by
  exact BitMachineComposition.composition_outputsWithin _ _
    (PolynomialFuelPrefix.outputsWithin_raw bits)
    (ClockedPackedWrapper.outputs_packed_success M
      (PolynomialFuelPrefix.clockLength bits) bits output h)

#print axioms outputs_all
#print axioms outputs_valid

end CurrentAdditive.PhysicalPolynomialClock
