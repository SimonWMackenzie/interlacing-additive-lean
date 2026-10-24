import CurrentAdditive.ConditioningGeneralTransfer
import CurrentAdditive.EvenMomentGeneral

/-!
The full arbitrary-even-order instance of v27 Appendix H `det:conditioning`.
The only source hypothesis is genuine `8R`-wise independence of the indexed
law; the moment estimate is proved via disjoint-block joint agreement,
exact finite moment transfer, and the independent-product bound.
-/

namespace CurrentAdditive

open Paper2 Paper2.FiniteLaw

/-- The actual selected bad-test sum obeys the manuscript's moment estimate
for every even `R ≥ 8`. -/
theorem selectedBadSum_evenMoment_R
    {Ω Z : Type*} [Fintype Ω] [Fintype Z] {q R : ℕ}
    (hEven : Even R) (hR : 8 ≤ R)
    (ν ρ : FiniteLaw Ω) (μ : FiniteLaw Z)
    (draw : Ω → Fin q → Z) (ε : ℝ)
    (hwise : IsDWise (8 * R) ν draw μ)
    (F : Finset (Finset (Fin q)))
    (hF : F ⊆ badCoordinateSets ρ μ draw ε)
    (hpair : (F : Set (Finset (Fin q))).Pairwise Disjoint) :
    expectation ν (fun ω =>
      |centeredBadSum ν ρ μ draw ε F ω| ^ (R : ℝ)) ≤
      2 * ((R : ℝ) * F.card / 4) ^ ((R : ℝ) / 2) := by
  classical
  let test : Fin F.card → Ω → Bool := selectedBadTest ρ μ draw ε F
  have hiid := EvenMomentGeneral.iid_centered_indicator_moment_even
    ν F.card R hEven hR test
  have hProxy : expectation (ν.iid F.card) (fun ws =>
      |∑ i : Fin F.card,
        ((if selectedBadTest ρ μ draw ε F i (ws i) then (1 : ℝ) else 0) -
          ν.prob (fun ω => selectedBadTest ρ μ draw ε F i ω))| ^ R) ≤
      2 * ((R : ℝ) * F.card / 4) ^ (R / 2) := by
    simpa only [expectation, EvenMoment.ex, test] using hiid
  exact selectedBadSum_evenMoment_R_of_proxy hEven ν ρ μ draw ε
    hwise F hF hpair hProxy

/-- The manuscript's `det:conditioning` conclusion for every even `R ≥ 8`,
with `D=8R`, its exact threshold, and its exact exceptional-set allowance. -/
theorem conditioning_exceptional_coordinates_R
    {Ω Z : Type*} [Fintype Ω] [Fintype Z] {q R : ℕ}
    (hEven : Even R) (hR : 8 ≤ R)
    (ν : FiniteLaw Ω) (μ : FiniteLaw Z)
    (draw : Ω → Fin q → Z) (Y : Ω → Prop)
    (v τ : ℝ) (hv : 0 < v) (hvY : v ≤ ν.prob Y) (hτ : 0 < τ)
    (hwise : IsDWise (8 * R) ν draw μ) :
    ∃ E : Finset (Fin q), E.card ≤ conditioningExceptionCountR R v τ ∧
      ∀ J : Finset (Fin q),
        J ⊆ (Finset.univ : Finset (Fin q)) \ E → J.card ≤ 8 →
          projectionTV (condition ν Y (lt_of_lt_of_le hv hvY)) μ draw J ≤
            conditioningEpsilonR R v τ := by
  have hind : ExactlyKWiseIndependent ν μ draw (8 * R) :=
    exactlyKWiseIndependent_of_isDWise ν μ draw hwise
  apply conditioning_exceptional_coordinates_R_of_even_moment
    hR ν μ draw Y v τ hv hvY hτ hind
  intro F hF hpair _
  exact selectedBadSum_evenMoment_R hEven hR ν
    (condition ν Y (lt_of_lt_of_le hv hvY)) μ draw
    (conditioningEpsilonR R v τ) hwise F hF hpair

#print axioms selectedBadSum_evenMoment_R
#print axioms conditioning_exceptional_coordinates_R

end CurrentAdditive
