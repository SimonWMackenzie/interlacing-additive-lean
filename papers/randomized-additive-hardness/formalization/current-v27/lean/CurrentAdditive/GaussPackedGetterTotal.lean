import CurrentAdditive.GaussPackedClock64
import CurrentAdditive.PhysicalPolynomialClockPoly

set_option maxHeartbeats 2000000

/-! The fixed ordinary-input packed Gauss getter, with a physically written
twelfth-power clock and a literal timeout gate. -/

namespace CurrentAdditive.GaussPackedGetterTotal

open EthInapproximability.CurrentPaper

noncomputable def machine : BitMachine.Machine :=
  PhysicalPolynomialClock.machine GaussPackedMachine64.machine

noncomputable def result (input : List Bool) : List Bool :=
  PhysicalPolynomialClock.result GaussPackedMachine64.machine input

noncomputable def coefficient : Nat :=
  1010000 + 5000 *
    ClockedPackedWrapper.clockCoefficient GaussPackedMachine64.machine

def exponent : Nat := 13

theorem outputs_all (input : List Bool) :
    machine.OutputsWithin input (result input)
      (PhysicalPolynomialClock.time GaussPackedMachine64.machine input) := by
  exact PhysicalPolynomialClock.outputs_all GaussPackedMachine64.machine input

theorem outputs (input : List Bool) :
    machine.OutputsWithin input (result input)
      (coefficient * (input.length+1)^exponent) := by
  exact BitMachine.outputsWithin_mono machine (outputs_all input)
    (PhysicalPolynomialClock.time_le GaussPackedMachine64.machine input)

theorem polytime : BitMachine.Polytime result := by
  exact PhysicalPolynomialClock.polytime GaussPackedMachine64.machine

theorem canonical_outputs {m k : Nat}
    (B : Fin m → Fin k → ℚ) (i : Fin m) (j : Fin k) :
    machine.OutputsWithin
      (GaussPackedFetch64.input B i j)
      (CodeDCodec.encodeRawRat (GaussPhysical.rawOfRat (B i j)))
      (PhysicalPolynomialClock.time GaussPackedMachine64.machine
        (GaussPackedFetch64.input B i j)) := by
  apply PhysicalPolynomialClock.outputs_valid GaussPackedMachine64.machine
  simpa only [PolynomialFuelPrefix.clockLength,
    PolynomialFuelPrefix.baseLength] using
    GaussPackedClock64.canonical_outputs_budget B i j

theorem canonical_outputs_poly {m k : Nat}
    (B : Fin m → Fin k → ℚ) (i : Fin m) (j : Fin k) :
    machine.OutputsWithin
      (GaussPackedFetch64.input B i j)
      (CodeDCodec.encodeRawRat (GaussPhysical.rawOfRat (B i j)))
      (coefficient * ((GaussPackedFetch64.input B i j).length+1)^exponent) := by
  exact BitMachine.outputsWithin_mono machine
    (canonical_outputs B i j)
    (PhysicalPolynomialClock.time_le GaussPackedMachine64.machine
      (GaussPackedFetch64.input B i j))

#print axioms outputs_all
#print axioms outputs
#print axioms polytime
#print axioms canonical_outputs
#print axioms canonical_outputs_poly

end CurrentAdditive.GaussPackedGetterTotal
