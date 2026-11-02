import CurrentAdditive.GeneratedOwnerIncomingBoundCorrectedClean

/-! The source's owner conditioning uses τ=η/2. The displayed R=1024
epsilon threshold automatically meets both singleton and pair caps. -/

namespace CurrentAdditive.DeterministicIndexedMatrix.Sources

theorem owner_conditioning_epsilon_le_eta_half (v η : ℝ) :
    CurrentAdditive.conditioningEpsilonR 1024 v (η/2) ≤ η/2 := by
  unfold CurrentAdditive.conditioningEpsilonR
  exact min_le_left _ _

theorem owner_conditioning_epsilon_le_point01 (v η : ℝ)
    (hv : 0 ≤ v) (hv1 : v ≤ 1) :
    CurrentAdditive.conditioningEpsilonR 1024 v (η/2) ≤ 1/100 := by
  have hpow : v ^ ((4 : ℝ) / 1024) ≤ 1 :=
    Real.rpow_le_one hv hv1 (by norm_num)
  have hconst : (0 : ℝ) ≤ (2 : ℝ)^(-(20 : ℝ)) / 1024 := by positivity
  have hmul := mul_le_mul_of_nonneg_left hpow hconst
  have hnum : (2 : ℝ)^(-(20 : ℝ)) / 1024 ≤ 1/100 := by norm_num
  unfold CurrentAdditive.conditioningEpsilonR
  have hmin := min_le_right (η/2)
    ((2 : ℝ)^(-(20 : ℝ)) / 1024 * v ^ ((4 : ℝ) / 1024))
  nlinarith

#print axioms owner_conditioning_epsilon_le_eta_half
#print axioms owner_conditioning_epsilon_le_point01

end CurrentAdditive.DeterministicIndexedMatrix.Sources
