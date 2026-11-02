import CurrentAdditive.DivisionCongruence

namespace CurrentAdditive.FiniteFieldConstructor.BitPolynomialBridge

open Polynomial

theorem polynomial_degree_lt (bound code : ℕ) :
    (polynomial bound code).degree < bound := by
  apply (Polynomial.degree_lt_iff_coeff_zero _ _).mpr
  intro j hj
  rw [coeff_polynomial]
  simp [show ¬ j < bound by omega]

theorem polynomial_zero_code (bound code : ℕ) (hsize : code < 2 ^ bound)
    (hzero : polynomial bound code = 0) : code = 0 := by
  apply Nat.zero_of_testBit_eq_false
  intro j
  by_cases hj : j < bound
  · have hc := congrArg (fun p : Polynomial (ZMod 2) => p.coeff j) hzero
    change (polynomial bound code).coeff j = (0 : Polynomial (ZMod 2)).coeff j at hc
    rw [coeff_polynomial] at hc
    simp only [hj, ↓reduceIte, Polynomial.coeff_zero] at hc
    cases hbit : code.testBit j
    · rfl
    · simp [hbit] at hc
  · have hp : 2 ^ bound ≤ 2 ^ j := Nat.pow_le_pow_right (by omega) (by omega)
    exact Nat.testBit_eq_false_of_lt (hsize.trans_le hp)

theorem remainder_zero_iff_dvd (d e tailDivisor tailDividend : ℕ)
    (he : e ≤ d) (hdivisor : tailDivisor < 2 ^ e)
    (hdividend : tailDividend < 2 ^ d) :
    TrialSearch.remainder d e (TrialSearch.monicBits e tailDivisor)
        (TrialSearch.monicBits d tailDividend) = 0 ↔
      polynomial (e + 1) (TrialSearch.monicBits e tailDivisor) ∣
        polynomial (d + 1) (TrialSearch.monicBits d tailDividend) := by
  let rem := TrialSearch.remainder d e
    (TrialSearch.monicBits e tailDivisor)
    (TrialSearch.monicBits d tailDividend)
  let f := polynomial (e + 1) (TrialSearch.monicBits e tailDivisor)
  let g := polynomial (d + 1) (TrialSearch.monicBits d tailDividend)
  obtain ⟨q, hq⟩ := remainder_relation d e tailDivisor tailDividend he hdivisor
  have hq' : polynomial (d + 1) rem = g + f * q := hq
  constructor
  · intro hrem
    have hzero : polynomial (d + 1) rem = 0 := by simp [hrem, rem, polynomial]
    rw [hzero] at hq'
    refine ⟨-q, ?_⟩
    linear_combination -hq'
  · intro hdvd
    have hdivrem : f ∣ polynomial (d + 1) rem := by
      rw [hq']
      exact dvd_add hdvd (dvd_mul_right f q)
    have hdegree : (polynomial (d + 1) rem).degree < f.degree := by
      have hrem_lt := remainder_lt d e tailDivisor tailDividend he hdivisor hdividend
      have hpoly : polynomial (d + 1) rem = polynomial e rem :=
        polynomial_extend e (d + 1) rem hrem_lt (by omega)
      rw [hpoly]
      have hfdegree : f.natDegree = e := monicBits_degree e tailDivisor hdivisor
      have hfnonzero : f ≠ 0 := (monicBits_monic e tailDivisor hdivisor).ne_zero
      rw [Polynomial.degree_eq_natDegree hfnonzero, hfdegree]
      exact polynomial_degree_lt e rem
    have hpolyzero := Polynomial.eq_zero_of_dvd_of_degree_lt hdivrem hdegree
    have hsize : rem < 2 ^ (d + 1) :=
      (remainder_lt d e tailDivisor tailDividend he hdivisor hdividend).trans_le
        (Nat.pow_le_pow_right (by omega) (by omega))
    exact polynomial_zero_code (d + 1) rem hsize hpolyzero

#print axioms remainder_zero_iff_dvd

end CurrentAdditive.FiniteFieldConstructor.BitPolynomialBridge
