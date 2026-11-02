import CurrentAdditive.CodeDOuterLoopV2

/-!
Arithmetic closure of the physical unary-fuel controller.  Once a concrete
one-stage finite-stack machine has an exact output theorem and a polynomial
clock, and its actual intermediate packets have polynomial length, the
existing literal loop has the displayed polynomial clock.  These premises
are explicit and remain open for the full Code D stage.
-/

namespace CurrentAdditive.CodeDLoopClockV2

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineIteration
open CodeDOuterLoopV2

def polynomialClock (M : BitMachine.Machine) (N C e d : Nat) : Nat :=
  (N + 1) * roundBound M (C * (N + 1) ^ e) (C * (N + 1) ^ d) + 1

theorem conditional_polynomial_clock (M : BitMachine.Machine)
    (D : Nat) (alphabet : Array (Nat × ℚ))
    (q N C e d : Nat)
    (hq : q ≤ N)
    (hstep : ∀ j < q,
      M.OutputsWithin (stateAt D alphabet j) (stateAt D alphabet (j + 1))
        (C * (N + 1) ^ d))
    (hlen : ∀ j < q,
      (stateAt D alphabet j).length ≤ C * (N + 1) ^ e) :
    ∃ t ≤ polynomialClock M N C e d,
      run M t (ready M (stateAt D alphabet 0) (List.replicate q true)) =
        finished M (stateAt D alphabet q) := by
  obtain ⟨t, ht, hr⟩ := conditional_outer_run M D alphabet q
    (C * (N + 1) ^ e) (C * (N + 1) ^ d) hstep hlen
  refine ⟨t, ?_, hr⟩
  unfold polynomialClock
  have hm : q * roundBound M (C * (N + 1) ^ e) (C * (N + 1) ^ d) ≤
      (N + 1) * roundBound M (C * (N + 1) ^ e) (C * (N + 1) ^ d) :=
    Nat.mul_le_mul_right _ (by omega)
  omega

#print axioms conditional_polynomial_clock

end CurrentAdditive.CodeDLoopClockV2
