import CurrentAdditive.ConditioningIsDWiseBridge
import CurrentAdditive.BlockJointBridge
import CurrentAdditive.MomentTransfer

/-!
The arbitrary-even-order form of v27 Appendix H, `det:conditioning`.
This file keeps the generic finite-TV and counting assembly separate from the
independent-product moment estimate. The latter is supplied in a subsequent
file; the intermediate theorem here exposes only that exact analytic premise.
-/

namespace CurrentAdditive

open Paper2 Paper2.FiniteLaw

/-- The manuscript's threshold with an explicit even order `R`. -/
noncomputable def conditioningEpsilonR (R : ℕ) (v τ : ℝ) : ℝ :=
  min τ (((2 : ℝ) ^ (-(20 : ℝ))) / R * v ^ ((4 : ℝ) / R))

theorem conditioningEpsilonR_pos {R : ℕ} {v τ : ℝ}
    (hR : 8 ≤ R) (hv : 0 < v) (hτ : 0 < τ) :
    0 < conditioningEpsilonR R v τ := by
  have hRreal : (0 : ℝ) < R := by exact_mod_cast (show 0 < R by omega)
  unfold conditioningEpsilonR
  exact lt_min hτ (mul_pos
    (div_pos (Real.rpow_pos_of_pos (by norm_num) _) hRreal)
    (Real.rpow_pos_of_pos hv _))

/-- The exact natural-number exceptional-coordinate allowance in the paper. -/
noncomputable def conditioningExceptionCountR (R : ℕ) (v τ : ℝ) : ℕ :=
  8 * ⌈(R : ℝ) * (conditioningEpsilonR R v τ) ^ (-(2 : ℝ)) *
    v ^ (-(2 / (R : ℝ)))⌉₊

/-- A selected TV witness has the required conditional expectation gap when
the original indexed source is `8R`-wise independent. -/
theorem selectedBadTest_discrepancy_R
    {Ω Z : Type*} [Fintype Ω] [Fintype Z] {q R : ℕ}
    (hR : 8 ≤ R) (ν : FiniteLaw Ω) (Y : Ω → Prop)
    (hY : 0 < ν.prob Y) (μ : FiniteLaw Z)
    (draw : Ω → Fin q → Z) (ε : ℝ)
    (hind : ExactlyKWiseIndependent ν μ draw (8 * R))
    (F : Finset (Finset (Fin q)))
    (hF : F ⊆ badCoordinateSets (condition ν Y hY) μ draw ε)
    (i : Fin F.card) :
    ε < expectation (condition ν Y hY)
        (fun ω => if selectedBadTest (condition ν Y hY) μ draw ε F i ω
          then (1 : ℝ) else 0) -
      expectation ν
        (fun ω => if selectedBadTest (condition ν Y hY) μ draw ε F i ω
          then (1 : ℝ) else 0) := by
  classical
  let J : Finset (Fin q) := ((F.equivFin).symm i).1
  have hJF : J ∈ F := ((F.equivFin).symm i).2
  have hJbad := hF hJF
  have hJsize : J.card ≤ 8 :=
    ((mem_badCoordinateSets_iff (condition ν Y hY) μ draw ε J).mp hJbad).1
  have hJwide : J.card ≤ 8 * R := by omega
  have hW := chosenBadEvent_witness (condition ν Y hY) μ draw ε J hJbad
  have hindJ := hind J hJwide (chosenBadEvent (condition ν Y hY) μ draw ε J)
  have hρ : expectation (condition ν Y hY)
      (fun ω => if selectedBadTest (condition ν Y hY) μ draw ε F i ω
        then (1 : ℝ) else 0) =
      (condition ν Y hY).prob (fun ω =>
        projection draw J ω ∈ chosenBadEvent (condition ν Y hY) μ draw ε J) := by
    rw [expectation_indicator_eq_prob]
    simp [selectedBadTest, J]
  have hν : expectation ν
      (fun ω => if selectedBadTest (condition ν Y hY) μ draw ε F i ω
        then (1 : ℝ) else 0) =
      ν.prob (fun ω =>
        projection draw J ω ∈ chosenBadEvent (condition ν Y hY) μ draw ε J) := by
    rw [expectation_indicator_eq_prob]
    simp [selectedBadTest, J]
  change ε < _ - _
  rw [hρ, hν]
  rw [hindJ]
  exact hW

/-- Every selected disjoint family of bad projections gives `R`-wise joint
agreement of its indicator tests with independent proxy draws. -/
theorem selectedBadTest_jointAgreement_R
    {Ω Z : Type*} [Fintype Ω] [Fintype Z] {q R : ℕ}
    (ν ρ : FiniteLaw Ω) (μ : FiniteLaw Z)
    (draw : Ω → Fin q → Z) (ε : ℝ)
    (hwise : IsDWise (8 * R) ν draw μ)
    (F : Finset (Finset (Fin q)))
    (hF : F ⊆ badCoordinateSets ρ μ draw ε)
    (hpair : (F : Set (Finset (Fin q))).Pairwise Disjoint) :
    IndicatorJointAgreement ν (selectedBadTest ρ μ draw ε F) R := by
  classical
  let blocks : Fin F.card → Finset (Fin q) :=
    fun i => ((F.equivFin).symm i).1
  let H : (i : Fin F.card) → (blocks i → Z) → Bool :=
    fun i x => decide (x ∈ chosenBadEvent ρ μ draw ε (blocks i))
  have hsize : ∀ i, (blocks i).card ≤ 8 := by
    intro i
    have hi : blocks i ∈ F := ((F.equivFin).symm i).2
    exact ((mem_badCoordinateSets_iff ρ μ draw ε (blocks i)).mp (hF hi)).1
  have hdisj : Pairwise (fun i j => Disjoint (blocks i) (blocks j)) := by
    intro i j hij
    have hi : blocks i ∈ F := ((F.equivFin).symm i).2
    have hj : blocks j ∈ F := ((F.equivFin).symm j).2
    have hneq : blocks i ≠ blocks j := by
      intro heq
      apply hij
      apply (F.equivFin).symm.injective
      exact Subtype.ext heq
    exact hpair hi hj hneq
  intro s hs E
  have hjoint := disjoint_blocks_indicator_joint_agreement
    ν μ draw (R := R) hwise blocks hsize hdisj H s hs E
  simpa only [selectedBadTest, blocks, H, projection] using hjoint

/-- Generic finite-TV conditioning conclusion, with the precise selected-sum
moment bound exposed. The final theorem removes this premise using the proved
independent-product bound and exact moment transfer. -/
theorem conditioning_exceptional_coordinates_R_of_even_moment
    {Ω Z : Type*} [Fintype Ω] [Fintype Z] {q R : ℕ}
    (hR : 8 ≤ R) (ν : FiniteLaw Ω) (μ : FiniteLaw Z)
    (draw : Ω → Fin q → Z) (Y : Ω → Prop)
    (v τ : ℝ) (hv : 0 < v) (hvY : v ≤ ν.prob Y) (hτ : 0 < τ)
    (hind : ExactlyKWiseIndependent ν μ draw (8 * R))
    (hEvenMoment : ∀ F : Finset (Finset (Fin q)),
      F ⊆ badCoordinateSets (condition ν Y (lt_of_lt_of_le hv hvY)) μ draw
        (conditioningEpsilonR R v τ) →
      (F : Set (Finset (Fin q))).Pairwise Disjoint → 0 < F.card →
      expectation ν (fun ω =>
        |centeredBadSum ν (condition ν Y (lt_of_lt_of_le hv hvY)) μ draw
          (conditioningEpsilonR R v τ) F ω| ^ (R : ℝ)) ≤
        2 * ((R : ℝ) * F.card / 4) ^ ((R : ℝ) / 2)) :
    ∃ E : Finset (Fin q), E.card ≤ conditioningExceptionCountR R v τ ∧
      ∀ J : Finset (Fin q),
        J ⊆ (Finset.univ : Finset (Fin q)) \ E → J.card ≤ 8 →
          projectionTV (condition ν Y (lt_of_lt_of_le hv hvY)) μ draw J ≤
            conditioningEpsilonR R v τ := by
  classical
  let hY : 0 < ν.prob Y := lt_of_lt_of_le hv hvY
  let ρ := condition ν Y hY
  let ε := conditioningEpsilonR R v τ
  let bad := badCoordinateSets ρ μ draw ε
  have hε : 0 < ε := conditioningEpsilonR_pos hR hv hτ
  have hnonempty : ∀ J ∈ bad, J.Nonempty :=
    badCoordinateSets_nonempty ρ μ draw ε hε.le
  have hsize : ∀ J ∈ bad, J.card ≤ 8 := by
    intro J hJ
    exact ((mem_badCoordinateSets_iff ρ μ draw ε J).mp hJ).1
  let B : ℝ := (R : ℝ) * ε ^ (-(2 : ℝ)) * v ^ (-(2 / (R : ℝ)))
  have hpacking : ∀ F : Finset (Finset (Fin q)), F ⊆ bad →
      (F : Set (Finset (Fin q))).Pairwise Disjoint → (F.card : ℝ) ≤ B := by
    intro F hF hpair
    by_cases hm : 0 < F.card
    · let test : Fin F.card → Ω → Bool := selectedBadTest ρ μ draw ε F
      have hdisc : ∀ i : Fin F.card,
          ε < expectation ρ (fun ω => if test i ω then (1 : ℝ) else 0) -
            expectation ν (fun ω => if test i ω then (1 : ℝ) else 0) := by
        intro i
        exact selectedBadTest_discrepancy_R hR ν Y hY μ draw ε hind F hF i
      have hmean : (F.card : ℝ) * ε <
          expectation ρ (centeredBadSum ν ρ μ draw ε F) := by
        exact centered_indicator_sum_large_mean ν Y hY F.card hm test ε hdisc
      have hM := hEvenMoment F hF hpair hm
      have hRreal : 2 ≤ (R : ℝ) := by exact_mod_cast (show 2 ≤ R by omega)
      have hcount := witness_count_lt_mass_lower_bound ν Y v hv hvY
        (centeredBadSum ν ρ μ draw ε F) (R : ℝ) hRreal
        F.card hm ε hε hmean hM
      exact hcount.le
    · have hzero : F.card = 0 := by omega
      have hB : 0 ≤ B := by
        dsimp [B]
        positivity
      simpa [hzero] using hB
  obtain ⟨E, hEcard, hcover⟩ :=
    finite_exceptional_cover_ceiling bad B hnonempty hsize hpacking
  refine ⟨E, ?_, ?_⟩
  · simpa [conditioningExceptionCountR, B, ε] using hEcard
  · intro J hJremaining hJsize
    by_contra hgood
    have hJbad : J ∈ bad :=
      (mem_badCoordinateSets_iff ρ μ draw ε J).mpr
        ⟨hJsize, lt_of_not_ge hgood⟩
    exact (no_bad_subset_complement hcover hJremaining) hJbad

#print axioms conditioningEpsilonR_pos
#print axioms selectedBadTest_discrepancy_R
#print axioms selectedBadTest_jointAgreement_R
#print axioms conditioning_exceptional_coordinates_R_of_even_moment

end CurrentAdditive
