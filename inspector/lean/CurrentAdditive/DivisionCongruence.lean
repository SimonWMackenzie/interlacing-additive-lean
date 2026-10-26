import CurrentAdditive.DivisionRec

namespace CurrentAdditive.FiniteFieldConstructor.BitPolynomialBridge

open Polynomial

theorem run_relation (d e divisor m acc : ℕ)
    (hem : e + m ≤ d + 1) (hdivisor : divisor < 2 ^ (e + 1)) :
    ∃ q : Polynomial (ZMod 2),
      polynomial (d + 1) (run e divisor m acc) =
        polynomial (d + 1) acc + polynomial (e + 1) divisor * q := by
  induction m generalizing acc with
  | zero =>
      refine ⟨0, ?_⟩
      simp [run]
  | succ m ih =>
      let next := step e m divisor acc
      have hnext := ih next (by omega)
      obtain ⟨q, hq⟩ := hnext
      let f := polynomial (e + 1) divisor
      refine ⟨q + (if acc.testBit (e + m) then X ^ m else 0), ?_⟩
      change polynomial (d + 1) (run e divisor m next) = _
      rw [hq]
      have hs : polynomial (d + 1) next =
          polynomial (d + 1) acc +
            (if acc.testBit (e + m) then X ^ m * f else 0) := by
        exact divisionStep_polynomial d e m divisor acc (by omega) hdivisor
      rw [hs]
      dsimp [f]
      split_ifs <;> ring

theorem remainder_relation (d e tailDivisor tailDividend : ℕ)
    (he : e ≤ d) (hdivisor : tailDivisor < 2 ^ e) :
    ∃ q : Polynomial (ZMod 2),
      polynomial (d + 1)
        (TrialSearch.remainder d e (TrialSearch.monicBits e tailDivisor)
          (TrialSearch.monicBits d tailDividend)) =
      polynomial (d + 1) (TrialSearch.monicBits d tailDividend) +
        polynomial (e + 1) (TrialSearch.monicBits e tailDivisor) * q := by
  rw [remainder_eq_run]
  exact run_relation d e (TrialSearch.monicBits e tailDivisor)
    (d - e + 1) (TrialSearch.monicBits d tailDividend)
    (by omega) (monicBits_lt e tailDivisor hdivisor)

#print axioms remainder_relation

end CurrentAdditive.FiniteFieldConstructor.BitPolynomialBridge
