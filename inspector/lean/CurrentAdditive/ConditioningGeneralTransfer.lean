import CurrentAdditive.ConditioningGeneralCore

/-! Exact moment transfer for the selected bad-set indicators at arbitrary
even order. The independent-proxy moment bound is stated in precisely the
form proved by the analytic module. -/

namespace CurrentAdditive

open Paper2 Paper2.FiniteLaw

theorem selectedBadSum_evenMoment_R_of_proxy
    {Ω Z : Type*} [Fintype Ω] [Fintype Z] {q R : ℕ}
    (hEven : Even R)
    (ν ρ : FiniteLaw Ω) (μ : FiniteLaw Z)
    (draw : Ω → Fin q → Z) (ε : ℝ)
    (hwise : IsDWise (8 * R) ν draw μ)
    (F : Finset (Finset (Fin q)))
    (hF : F ⊆ badCoordinateSets ρ μ draw ε)
    (hpair : (F : Set (Finset (Fin q))).Pairwise Disjoint)
    (hProxy : expectation (ν.iid F.card) (fun ws =>
      |∑ i : Fin F.card,
        ((if selectedBadTest ρ μ draw ε F i (ws i) then (1 : ℝ) else 0) -
          ν.prob (fun ω => selectedBadTest ρ μ draw ε F i ω))| ^ R) ≤
      2 * ((R : ℝ) * F.card / 4) ^ (R / 2)) :
    expectation ν (fun ω =>
      |centeredBadSum ν ρ μ draw ε F ω| ^ (R : ℝ)) ≤
      2 * ((R : ℝ) * F.card / 4) ^ ((R : ℝ) / 2) := by
  classical
  let test : Fin F.card → Ω → Bool := selectedBadTest ρ μ draw ε F
  have hjoint : IndicatorJointAgreement ν test R :=
    selectedBadTest_jointAgreement_R ν ρ μ draw ε hwise F hF hpair
  have htransfer := centered_indicator_even_moment_eq_proxy
    ν test R hEven hjoint
  have hbound : expectation ν (fun ω =>
      |∑ i : Fin F.card,
        ((if test i ω then (1 : ℝ) else 0) -
          ν.prob (fun ω' => test i ω'))| ^ R) ≤
      2 * ((R : ℝ) * F.card / 4) ^ (R / 2) := by
    rw [htransfer]
    exact hProxy
  have hexp : ((R / 2 : ℕ) : ℝ) = (R : ℝ) / 2 :=
    Nat.cast_div_charZero hEven.two_dvd
  have hpow (x : ℝ) : x ^ (R : ℝ) = x ^ R := Real.rpow_natCast x R
  rw [← hexp]
  simpa only [centeredBadSum, test, expectation_indicator_eq_prob,
    hpow, Real.rpow_natCast] using hbound

#print axioms selectedBadSum_evenMoment_R_of_proxy

end CurrentAdditive
