import CurrentAdditive.V40DeterministicSourcePack

/-! The actual formula front and physical handoff are paid in original
encoded bytes, independently of the later constructor/classifier clock. -/
namespace CurrentAdditive.V40DeterministicETHEndpoint
open EthInapproximability.CurrentPaper PhysicalProducer
noncomputable section
set_option maxHeartbeats 1500000

def frontClock (F : Producer) (w : List Bool) :=
  F.coefficient*(w.length+1)^F.degree+2*(F.result w).length+2

def frontClockCoefficient (F : Producer) := F.coefficient*(1+2*F.machine.pushBound)+2

def frontClockDegree (F : Producer) := F.degree+1

theorem frontClock_le (F : Producer) (w : List Bool) :
    frontClock F w≤frontClockCoefficient F*(w.length+1)^frontClockDegree F := by
  have hl:=BitMachine.output_length_bound F.machine (F.outputs w)
  have hbase : 1≤w.length+1 := by omega
  have hp : (w.length+1)^F.degree≤(w.length+1)^(F.degree+1) :=
    Nat.pow_le_pow_right hbase (by omega)
  have hx : w.length+1≤(w.length+1)^(F.degree+1) := Nat.le_self_pow (by omega) _
  have hmul:=Nat.mul_le_mul_left (F.coefficient*(1+2*F.machine.pushBound)) hp
  dsimp [frontClock,frontClockCoefficient,frontClockDegree]
  nlinarith

/-- Scalar absorption for the later concrete serial run; no run is inferred
from the numerical main-clock inequality. -/
theorem frontClock_combine (F : Producer) (w : List Bool) (Q p c main : ℕ)
    (hQ : 1≤Q) (hmain : main≤c*Q^p) :
    frontClock F w+main≤
      (frontClockCoefficient F+c)*Q^p*(w.length+1)^frontClockDegree F := by
  have hfront:=frontClock_le F w
  have hq : 1≤Q^p := Nat.one_le_pow _ _ hQ
  have hx : 1≤(w.length+1)^frontClockDegree F := Nat.one_le_pow _ _ (by omega)
  have ha : frontClockCoefficient F*(w.length+1)^frontClockDegree F≤
      frontClockCoefficient F*Q^p*(w.length+1)^frontClockDegree F := by
    exact Nat.mul_le_mul_right _ (by nlinarith)
  have hb : c*Q^p≤c*Q^p*(w.length+1)^frontClockDegree F := by nlinarith
  nlinarith

#print axioms frontClock_le
#print axioms frontClock_combine
end
end CurrentAdditive.V40DeterministicETHEndpoint
