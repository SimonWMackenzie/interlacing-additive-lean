import Mathlib.NumberTheory.Bertrand

namespace EthInapproximability.ParameterizedNP

/-- The balanced materializer's exact prime-window producer: for every
`X ≥ 2`, it produces a prime in the half-open interval `[X, 2 * X)`. -/
theorem primeWindow (X : ℕ) (hX : 2 ≤ X) :
    ∃ p : ℕ, Nat.Prime p ∧ X ≤ p ∧ p < 2 * X := by
  obtain ⟨p, hp, hlo, hhi⟩ :=
    Nat.exists_prime_lt_and_le_two_mul (X - 1) (by omega)
  exact ⟨p, hp, by omega, by omega⟩

end EthInapproximability.ParameterizedNP
