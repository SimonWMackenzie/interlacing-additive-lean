import Paper2.CodeGeneratorExponentInput

/-! Collapse the public fixed polynomial to one exponential clock. -/

set_option maxHeartbeats 12000000
set_option maxRecDepth 32768

namespace Paper2.CodeGeneratorExponent

open Paper2.CodeGeneratorClockSum
open Paper2.CodeGeneratorExponentCore
open Paper2.CodeGeneratorExponentAlgebra
open Paper2.CodeGeneratorExponentInput

def coefficient : Nat :=
  1000000000 * (Paper2.CodeGeneratorReentryBound.factor + 1) *
    (Paper2.CodeGeneratorStepGrowth.stepPush + 1)

theorem roundPoly_self_bound (X : Nat) (hX : 1 ≤ X) :
    Paper2.CodeGeneratorStepGrowth.roundPoly X X X X X X X X ≤
      coefficient * (X+1)^6 := by
  have hB : 1 ≤ (X+1)^6 := by
    have hp : 0 < (X+1)^6 := pow_pos (by omega) _
    omega
  have h := round_algebra
    (Paper2.CodeRecursiveStepClock.polynomialClock X X X X X X X X)
    X Paper2.CodeGeneratorReentryBound.factor
    Paper2.CodeGeneratorStepGrowth.stepPush ((X+1)^6)
    (step_self_bound X) (input_self_bound X) hB
  unfold Paper2.CodeGeneratorStepGrowth.roundPoly coefficient
  dsimp only
  have heq : X+X+X+X+X+X+X+X+1 = 8*X+1 := by omega
  rw [heq]
  exact h

#print axioms roundPoly_self_bound

end Paper2.CodeGeneratorExponent
