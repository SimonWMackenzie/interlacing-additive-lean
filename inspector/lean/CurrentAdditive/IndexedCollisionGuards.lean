import CurrentAdditive.IndexedProfileSchedule

/-! Scalar binding for the extra-position clause of Appendix I `det:profiles`.
The collision proof itself is the separate exact eight-wise selected-source
theorem; this file supplies all its schedule-dependent guards. -/

namespace CurrentAdditive.DeterministicIndexedMatrix

open CurrentAdditive.DeterministicParameters

theorem profile_extra_guards (L : ℕ) (hL : 2004 ≤ L) :
    8 ≤ 8192 ∧
    s L = 2^((L+3)/4) ∧
    q₁ L + 3 = s L + 1 ∧
    2 * (s L : ℝ) * (ρ L : ℝ) ≤ 1 := by
  have hs := s_ge_64 L (by omega)
  have hq : q₁ L + 3 = s L + 1 := by
    dsimp [q₁]
    omega
  have hr : (s L : ℝ) * (ρ L : ℝ) ≤ 1/1000 := by
    have hh : ((((s L : ℚ) * ρ L : ℚ)) : ℝ) ≤ ((1/1000 : ℚ) : ℝ) := by
      exact_mod_cast s_rho_small L hL
    simpa only [Rat.cast_mul, Rat.cast_natCast, Rat.cast_div,
      Rat.cast_one, Rat.cast_ofNat] using hh
  refine ⟨by decide, rfl, hq, ?_⟩
  nlinarith

end CurrentAdditive.DeterministicIndexedMatrix
