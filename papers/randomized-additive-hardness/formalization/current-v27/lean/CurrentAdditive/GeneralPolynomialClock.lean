import CurrentAdditive.GeneralPolynomialFuelPrefix
import CurrentAdditive.ClockedPackedWrapper

noncomputable section
namespace CurrentAdditive.GeneralPolynomialClock

open EthInapproximability.CurrentPaper

noncomputable def machine (degree : ℕ) (M : BitMachine.Machine) : BitMachine.Machine :=
  BitMachineComposition.composition
    (GeneralPolynomialFuelPrefix.machine (degree := degree))
    (ClockedPackedWrapper.machine M)

def packed (degree : ℕ) (bits : List Bool) : List Bool :=
  BoundedBitMachine.packed
    (GeneralPolynomialFuelPrefix.clockLength (degree := degree) bits) bits

noncomputable def result (degree : ℕ) (M : BitMachine.Machine)
    (bits : List Bool) : List Bool :=
  ClockedPackedWrapper.result M (packed degree bits)

def time (degree : ℕ) (M : BitMachine.Machine)
    (bits : List Bool) : ℕ :=
  GeneralPolynomialFuelPrefix.rawTime (degree := degree) bits +
    2*(packed degree bits).length+2 +
    ClockedPackedWrapper.clockCoefficient M*((packed degree bits).length+1)

theorem outputs_all (degree : ℕ) (M : BitMachine.Machine)
    (bits : List Bool) :
    (machine degree M).OutputsWithin bits (result degree M bits)
      (time degree M bits) := by
  exact BitMachineComposition.composition_outputsWithin _ _
    (GeneralPolynomialFuelPrefix.outputsWithin_raw (degree := degree) bits)
    (ClockedPackedWrapper.outputs_all_linear M (packed degree bits))

theorem outputs_valid (degree : ℕ) (M : BitMachine.Machine)
    (bits output : List Bool)
    (h : M.OutputsWithin bits output
      (GeneralPolynomialFuelPrefix.clockLength (degree := degree) bits)) :
    (machine degree M).OutputsWithin bits output (time degree M bits) := by
  exact BitMachineComposition.composition_outputsWithin _ _
    (GeneralPolynomialFuelPrefix.outputsWithin_raw (degree := degree) bits)
    (ClockedPackedWrapper.outputs_packed_success M
      (GeneralPolynomialFuelPrefix.clockLength (degree := degree) bits)
      bits output h)

#print axioms outputs_all
#print axioms outputs_valid

end CurrentAdditive.GeneralPolynomialClock
