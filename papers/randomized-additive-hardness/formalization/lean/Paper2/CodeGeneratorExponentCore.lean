import Paper2.CodeGeneratorClockSum

/-! Unfrozen algebra-only candidate; no physical machine theorems are
altered. -/

set_option maxHeartbeats 12000000
set_option maxRecDepth 32768

namespace Paper2.CodeGeneratorExponentCore

theorem step_self_bound (X : Nat) :
    Paper2.CodeRecursiveStepClock.polynomialClock X X X X X X X X ≤
      1000000 * (X+1)^6 := by
  dsimp [Paper2.CodeRecursiveStepClock.polynomialClock,
    Paper2.CodeRecursiveStepClock.graphCap,
    Paper2.CodeRecursiveStepClock.taggedCap,
    Paper2.TaggedCompiler.polynomialClock]
  ring_nf
  omega

#print axioms step_self_bound

end Paper2.CodeGeneratorExponentCore
