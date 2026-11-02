import CurrentAdditive.PhysicalProducer
import CurrentAdditive.V39DomainClockTotalization

namespace CurrentAdditive.V40BoundedFormatter
noncomputable section
open EthInapproximability.CurrentPaper PhysicalProducer
set_option maxHeartbeats 1000000

def bounded (M : BitMachine.Machine) (c d : ℕ) : Producer where
  machine := GeneralPolynomialClock.machine (c+d) M
  result := GeneralPolynomialClock.result (c+d) M
  coefficient := GeneralPolynomialClock.timeCoefficient (c+d) M
  degree := GeneralPolynomialClock.exponent (c+d)
  outputs x := BitMachine.outputsWithin_mono _
    (GeneralPolynomialClock.outputs_all (c+d) M x)
    (GeneralPolynomialClock.time_le (c+d) M x)

theorem result_of_run (M : BitMachine.Machine) (c d : ℕ) (x out : List Bool)
    (h : M.OutputsWithin x out (c*(x.length+1)^d)) :
    (bounded M c d).result x=out := by
  have hf := V39DomainClockTotalization.polynomial_le_written_fuel c d x.length
  have hrun := GeneralPolynomialClock.outputs_valid (c+d) M x out
    (BitMachine.outputsWithin_mono M h hf)
  exact BitMachine.outputsWithin_unique _ (GeneralPolynomialClock.outputs_all (c+d) M x) hrun

#print axioms bounded
#print axioms result_of_run
end
end CurrentAdditive.V40BoundedFormatter
