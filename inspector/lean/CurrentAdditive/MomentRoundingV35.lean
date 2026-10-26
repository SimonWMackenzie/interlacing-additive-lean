import CurrentAdditive.ExactAdmissibility

/-! The v35 rational moment test implies the older rounded-natural test for
the same public exponent, because the right-hand threshold becomes an integer
after multiplying by the dyadic `s^128`. -/

namespace FiniteV35Continuation

open CurrentAdditive.DeterministicParameters
open CurrentAdditive.DeterministicAdmissibility
open CurrentAdditive.PublicScheduleExactAdmissibility

def momentIntegerTarget (L : ℕ) : ℕ :=
  2 ^ (128 * ((L + 3) / 4) - (11 + 6 * L))

private theorem momentExponent_nonneg {L : ℕ} (hL : 1 ≤ L) :
    11 + 6 * L ≤ 128 * ((L + 3) / 4) := by
  have hceil : L ≤ 4 * ((L + 3) / 4) := by omega
  omega

theorem moment_target_exact {L : ℕ} (hL : 1 ≤ L) :
    ((momentIntegerTarget L : ℕ) : ℚ) =
      (θ L / 4) * (s L : ℚ)^128 := by
  let k := (L + 3) / 4
  let e := 128 * k - (11 + 6 * L)
  have he : e + (11 + 6 * L) = 128 * k := by
    dsimp [e, k]
    have := momentExponent_nonneg hL
    omega
  have hpow : (2 : ℚ)^(128*k) =
      (2 : ℚ)^e * (2 : ℚ)^(11+6*L) := by
    rw [← pow_add, he]
  have hden : (2 : ℚ)^(11+6*L) ≠ 0 := by positivity
  have hformula : (θ L / 4) * (s L : ℚ)^128 =
      (2 : ℚ)^(128*k) / (2 : ℚ)^(11+6*L) := by
    simp only [θ, Q_eq_pow, s, k, Nat.cast_pow, Nat.cast_ofNat]
    rw [← pow_mul]
    rw [show ((L+3)/4)*128 = 128*((L+3)/4) by omega]
    rw [pow_add]
    norm_num
    ring
  rw [hformula, hpow]
  field_simp
  simp [momentIntegerTarget, e, k]

/-- The rational comparison in v35 implies the seemingly stronger v27
integer-ceiling comparison at every positive public exponent. -/
theorem rational_moment_implies_rounded {L : ℕ} (hL : 1 ≤ L)
    (h : sourceC128 / (s L : ℚ)^128 ≤ θ L / 4) :
    (sourceC128Ceil : ℚ) / (s L : ℚ)^128 ≤ θ L / 4 := by
  have hs : (0 : ℚ) < (s L : ℚ)^128 := by positivity [s_pos L]
  have hm : sourceC128 ≤ (momentIntegerTarget L : ℚ) := by
    have hm' : sourceC128 ≤ (θ L / 4) * (s L : ℚ)^128 :=
      (div_le_iff₀ hs).mp h
    simpa only [← moment_target_exact hL] using hm'
  have hceil : sourceC128Ceil ≤ momentIntegerTarget L := by
    exact (Nat.ceil_le).2 hm
  have hceilQ : (sourceC128Ceil : ℚ) ≤ momentIntegerTarget L := by
    exact_mod_cast hceil
  apply (div_le_iff₀ hs).2
  rw [← moment_target_exact hL]
  exact hceilQ

/-- All twenty-seven literal v35 tests imply the existing construction
record for the **same** `L`. The only nontrivial change of coefficient is the
proved integer-threshold rounding above. No later or stronger dyadic log is
substituted. -/
theorem literalTests_to_Admissible
    (L n m Δ : ℕ) (γ : ℚ) (hΔ : 0 < Δ) (hγ : 0 < γ)
    (h : literalTests L n m Δ γ) :
    n ≤ N L ∧ Admissible L Δ n m sourceC128Ceil γ := by
  rcases h with ⟨hn, hexX, hexTheta, hexQuarter, hexRho,
    hmoment, hownerReserve, hownerMass, hgraphWidth, hrowWidth,
    hrung, hsquareRho, hsRho, hqX, hsX, hwX, hgraphOwner,
    hdoubleQX, hdoubleSX, hownerGap, hsquareX, hinverseX,
    hloss1, hloss2, hratioA, hratioT, hratioN⟩
  have hL : 1 ≤ L := by
    by_contra hh
    have hz : L = 0 := by omega
    subst L
    norm_num [s] at hrung
  have hA : (3 / 5 : ℝ) * (1 - 2 / (s L : ℝ)) -
      (q₁ L : ℝ) * (ρ L : ℝ) > 9 / 16 := by
    have hc := (Rat.cast_lt (K := ℝ)).mpr hratioA
    simpa only [Rat.cast_sub, Rat.cast_mul, Rat.cast_div,
      Rat.cast_natCast, Rat.cast_ofNat, Rat.cast_one] using hc
  have hT : (3 / 5 : ℝ) - (q₂ L : ℝ) * (x L : ℝ) > 9 / 16 := by
    have hc := (Rat.cast_lt (K := ℝ)).mpr hratioT
    simpa only [Rat.cast_sub, Rat.cast_mul, Rat.cast_div,
      Rat.cast_natCast, Rat.cast_ofNat, Rat.cast_one] using hc
  have hN : ∀ j : Fin 3, (2 : ℝ)^j.val *
      (((3 / 5 : ℝ) * (1 / 2 : ℝ)^j.val - (1 - (255 / 256 : ℝ))) /
        (255 / 256 : ℝ)) - (s L : ℝ) * (x L : ℝ) > 9 / 16 := by
    intro j
    have hc := (Rat.cast_lt (K := ℝ)).mpr (hratioN j)
    simpa only [Rat.cast_sub, Rat.cast_mul, Rat.cast_div,
      Rat.cast_natCast, Rat.cast_ofNat, Rat.cast_one, Rat.cast_pow] using hc
  refine ⟨hn, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, rational_moment_implies_rounded hL hmoment,
    ?_, ?_, hgraphWidth, hrowWidth, hrung, hsquareRho, hsRho,
    hqX, hsX, hwX, hgraphOwner, hdoubleQX, hdoubleSX, hownerGap,
    hsquareX, hinverseX, hloss1, hloss2, hA, hT, hN⟩
  · simpa only [exX_eq_source L] using hexX
  · simpa only [exTheta_eq_source L] using hexTheta
  · simpa only [exThetaQuarter_eq_source L] using hexQuarter
  · simpa only [exRho_eq_source L Δ γ hΔ hγ] using hexRho
  · simpa only [ownerExact_eq_source L Δ γ hΔ hγ] using hownerReserve
  · simpa only [ownerExact_eq_source L Δ γ hΔ hγ] using hownerMass

theorem literalTest_to_Admissible
    (L n m Δ : ℕ) (γ : ℚ) (hΔ : 0 < Δ) (hγ : 0 < γ)
    (h : literalTest L n m Δ γ = true) :
    n ≤ N L ∧ Admissible L Δ n m sourceC128Ceil γ :=
  literalTests_to_Admissible L n m Δ γ hΔ hγ
    ((literalTest_iff L n m Δ γ).mp h)

#print axioms moment_target_exact
#print axioms rational_moment_implies_rounded
#print axioms literalTests_to_Admissible
#print axioms literalTest_to_Admissible

end FiniteV35Continuation
