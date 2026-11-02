import CurrentAdditive.GaussCoefficientMachine
import CurrentAdditive.PhysicalPolynomialClockPoly

/-! The ordinary-input total coefficient machine. Its fuel prefix and timeout
are physical and fixed independently of the matrix dimensions. -/

namespace CurrentAdditive.GaussCoefficientProgram

open EthInapproximability.CurrentPaper

noncomputable def machine : BitMachine.Machine :=
  CurrentAdditive.PhysicalPolynomialClock.machine coefficientMachine

noncomputable def result (input : List Bool) : List Bool :=
  CurrentAdditive.PhysicalPolynomialClock.result coefficientMachine input

noncomputable def polynomialCoefficient : Nat :=
  1010000 + 5000 *
    CurrentAdditive.ClockedPackedWrapper.clockCoefficient coefficientMachine

def polynomialExponent : Nat := 13

theorem outputs_all (input : List Bool) :
    machine.OutputsWithin input (result input)
      (CurrentAdditive.PhysicalPolynomialClock.time coefficientMachine input) := by
  exact CurrentAdditive.PhysicalPolynomialClock.outputs_all coefficientMachine input

theorem outputs_poly (input : List Bool) :
    machine.OutputsWithin input (result input)
      (polynomialCoefficient * (input.length+1)^polynomialExponent) := by
  exact BitMachine.outputsWithin_mono machine (outputs_all input)
    (CurrentAdditive.PhysicalPolynomialClock.time_le coefficientMachine input)

theorem polytime : BitMachine.Polytime result := by
  exact CurrentAdditive.PhysicalPolynomialClock.polytime coefficientMachine

theorem canonical_outputs {m k : Nat} (B : Fin m → Fin k → ℚ)
    (f j : Fin k) (hf : f.val ≤ m) :
    machine.OutputsWithin
      (CurrentAdditive.GaussCertificateWorkList.workPacket B f j)
      (CurrentAdditive.GaussCertificateVectorABI.coefficientPacket
        (CurrentAdditive.GaussFirstFreeCandidate.directCandidate B f hf j))
      (CurrentAdditive.PhysicalPolynomialClock.time coefficientMachine
        (CurrentAdditive.GaussCertificateWorkList.workPacket B f j)) := by
  apply CurrentAdditive.PhysicalPolynomialClock.outputs_valid coefficientMachine
  exact BitMachine.outputsWithin_mono coefficientMachine
    (coefficient_outputs B f j hf) (coefficientClock_le_poly B f j hf)

theorem canonical_outputs_poly {m k : Nat} (B : Fin m → Fin k → ℚ)
    (f j : Fin k) (hf : f.val ≤ m) :
    machine.OutputsWithin
      (CurrentAdditive.GaussCertificateWorkList.workPacket B f j)
      (CurrentAdditive.GaussCertificateVectorABI.coefficientPacket
        (CurrentAdditive.GaussFirstFreeCandidate.directCandidate B f hf j))
      (polynomialCoefficient *
        ((CurrentAdditive.GaussCertificateWorkList.workPacket B f j).length+1)^polynomialExponent) := by
  exact BitMachine.outputsWithin_mono machine
    (canonical_outputs B f j hf)
    (CurrentAdditive.PhysicalPolynomialClock.time_le coefficientMachine
      (CurrentAdditive.GaussCertificateWorkList.workPacket B f j))

#print axioms outputs_all
#print axioms outputs_poly
#print axioms polytime
#print axioms canonical_outputs
#print axioms canonical_outputs_poly

end CurrentAdditive.GaussCoefficientProgram
