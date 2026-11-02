import Paper2.ProductProjections

/-!
# Covers of deficient coordinate projections

Source: frozen Paper 2 v12, Section 5, `res:projection-cover` (T19).

The first lemmas isolate the elementary finite maximality argument.  A
hypothesis ruling out a disjoint subfamily is explicitly combinatorial,
not a certificate of a probability inequality.  The full projection theorem
below invokes the proved inequality for actual images in an independent
product law. The retained event itself may be arbitrarily correlated.
-/

namespace Paper2.ProductProjections

open scoped BigOperators

variable {ι : Type*} [DecidableEq ι]

/-- A maximum-cardinality disjoint subfamily covers every nonempty member
of the original family by its union. -/
theorem exists_maximal_disjoint_cover (P : Finset (Finset ι))
    (hne : ∀ A ∈ P, A.Nonempty) :
    ∃ Q : Finset (Finset ι), Q ⊆ P ∧
      (Q : Set (Finset ι)).Pairwise Disjoint ∧
      ∀ A ∈ P, ¬ Disjoint A (Q.biUnion id) := by
  classical
  let candidates : Finset (Finset (Finset ι)) := P.powerset.filter
    (fun (Q : Finset (Finset ι)) => (Q : Set (Finset ι)).Pairwise Disjoint)
  have hempty : (∅ : Finset (Finset ι)) ∈ candidates := by
    simp [candidates, Set.Pairwise]
  obtain ⟨Q, hQ, hmax⟩ := candidates.exists_max_image Finset.card ⟨∅, hempty⟩
  obtain ⟨hQP, hdisj⟩ := Finset.mem_filter.mp hQ
  have hsub : Q ⊆ P := Finset.mem_powerset.mp hQP
  refine ⟨Q, hsub, hdisj, ?_⟩
  intro A hA hd
  have hAQ : A ∉ Q := by
    intro hmem
    obtain ⟨i, hi⟩ := hne A hA
    have hiunion : i ∈ Q.biUnion id := Finset.mem_biUnion.mpr ⟨A, hmem, hi⟩
    exact (Finset.disjoint_left.mp hd hi hiunion)
  have hnew : (insert A Q : Set (Finset ι)).Pairwise Disjoint := by
    apply Set.Pairwise.insert hdisj
    intro A' hA' _
    have hAA' : Disjoint A A' := by
      apply Finset.disjoint_left.mpr
      intro i hi hi'
      exact Finset.disjoint_left.mp hd hi
        (Finset.mem_biUnion.mpr ⟨A', hA', hi'⟩)
    exact ⟨hAA', hAA'.symm⟩
  have hins : insert A Q ∈ candidates := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_powerset.mpr ?_, ?_⟩
    · exact Finset.insert_subset hA hsub
    · simpa only [Finset.coe_insert] using hnew
  have hc := hmax (insert A Q) hins
  rw [Finset.card_insert_of_notMem hAQ] at hc
  omega

omit [DecidableEq ι] in
/-- Pure finite combinatorial form of the projection-cover argument.
Nonemptiness cannot be omitted: the empty set has no hitting set. -/
theorem exists_cover_of_disjoint_card_lt (P : Finset (Finset ι))
    (u B : ℕ) (hB : 1 ≤ B)
    (hcard : ∀ A ∈ P, A.card = u)
    (hne : ∀ A ∈ P, A.Nonempty)
    (hno : ∀ Q : Finset (Finset ι), Q ⊆ P →
      (Q : Set (Finset ι)).Pairwise Disjoint → Q.card < B) :
    ∃ C : Finset ι, C.card ≤ u * (B - 1) ∧
      ∀ A ∈ P, ¬ Disjoint A C := by
  classical
  obtain ⟨Q, hsub, hdisj, hcover⟩ := exists_maximal_disjoint_cover P hne
  refine ⟨Q.biUnion id, ?_, hcover⟩
  have hQB : Q.card ≤ B - 1 := by have := hno Q hsub hdisj; omega
  calc
    (Q.biUnion id).card ≤ ∑ A ∈ Q, A.card := Finset.card_biUnion_le
    _ = Q.card * u := by
      calc
        (∑ A ∈ Q, A.card) = ∑ _A ∈ Q, u := by
          apply Finset.sum_congr rfl
          intro A hA
          exact hcard A (hsub hA)
        _ = Q.card * u := by simp
    _ ≤ (B - 1) * u := Nat.mul_le_mul_right u hQB
    _ = u * (B - 1) := Nat.mul_comm _ _

omit [DecidableEq ι] in
/-- A formulation excluding only subfamilies of exactly `B` members. -/
theorem exists_cover_of_no_disjoint_subfamily (P : Finset (Finset ι))
    (u B : ℕ) (hB : 1 ≤ B)
    (hcard : ∀ A ∈ P, A.card = u)
    (hne : ∀ A ∈ P, A.Nonempty)
    (hno : ∀ Q : Finset (Finset ι), Q ⊆ P →
      (Q : Set (Finset ι)).Pairwise Disjoint → Q.card ≠ B) :
    ∃ C : Finset ι, C.card ≤ u * (B - 1) ∧
      ∀ A ∈ P, ¬ Disjoint A C := by
  apply exists_cover_of_disjoint_card_lt P u B hB hcard hne
  intro Q hQP hdisj
  by_contra! hlarge
  obtain ⟨Q', hQ'Q, hQ'card⟩ := Finset.exists_subset_card_eq hlarge
  exact hno Q' (hQ'Q.trans hQP) (hdisj.mono hQ'Q) hQ'card

variable {α : Type*} [Fintype ι] [Fintype α]

/-- Frozen v12 `res:projection-cover`, for actual coordinate projections.

No independence is required of `Z`. The coordinates of the ambient law are
independent. The empty-coordinate case `u = 0` and arbitrary real thresholds
are included. In particular, no positivity assumption on `ρ` is hidden in
the statement: if `ρ < 0`, there are no poor projections. -/
theorem projection_cover (μ : ι → FiniteLaw α) (Z : (ι → α) → Prop)
    (u B : ℕ) (hB : 1 ≤ B) (θ ρ : ℝ)
    (hθ : θ ≤ (FiniteLaw.pi μ).prob Z) (hgap : ρ ^ B < θ) :
    ∃ C : Finset ι, C.card ≤ u * (B - 1) ∧
      ∀ S : Finset ι, S.card = u → projectionMass μ Z S < ρ →
        ¬ Disjoint S C := by
  classical
  by_cases hρ : 0 ≤ ρ
  · have hpos : 0 < (FiniteLaw.pi μ).prob Z :=
      lt_of_lt_of_le (lt_of_le_of_lt (pow_nonneg hρ B) hgap) hθ
    have hZ : ∃ x, Z x := by
      by_contra h
      have hnone : ∀ x, ¬ Z x := not_exists.mp h
      have hz : (FiniteLaw.pi μ).prob Z = 0 := by
        simp [FiniteLaw.prob, hnone]
      linarith
    have hρone : ρ < 1 := by
      by_contra! h
      have hp : (1 : ℝ) ≤ ρ ^ B := one_le_pow₀ h
      have hupper := (FiniteLaw.pi μ).prob_le_one Z
      linarith
    let P : Finset (Finset ι) := Finset.univ.filter
      (fun S => S.card = u ∧ projectionMass μ Z S < ρ)
    have hmem (S : Finset ι) : S ∈ P ↔
        S.card = u ∧ projectionMass μ Z S < ρ := by simp [P]
    have hcard : ∀ S ∈ P, S.card = u := fun S hS => ((hmem S).mp hS).1
    have hnonempty : ∀ S ∈ P, S.Nonempty := by
      intro S hS
      by_contra hempty
      have heq : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hempty
      have hpoor := ((hmem S).mp hS).2
      rw [heq, projectionMass_empty_of_nonempty μ Z hZ] at hpoor
      linarith
    have hno : ∀ Q : Finset (Finset ι), Q ⊆ P →
        (Q : Set (Finset ι)).Pairwise Disjoint → Q.card ≠ B := by
      intro Q hQP hdisj hQB
      have hprod : (∏ S ∈ Q, projectionMass μ Z S) ≤ ρ ^ B := by
        calc
          (∏ S ∈ Q, projectionMass μ Z S) ≤ ∏ _S ∈ Q, ρ := by
            apply Finset.prod_le_prod
            · intro S _
              exact projectionMass_nonneg μ Z S
            · intro S hS
              exact ((hmem S).mp (hQP hS)).2.le
          _ = ρ ^ B := by simp [hQB]
      have hprojection := prob_le_prod_projectionMass μ Z Q hdisj
      linarith
    obtain ⟨C, hC, hcover⟩ :=
      exists_cover_of_no_disjoint_subfamily P u B hB hcard hnonempty hno
    exact ⟨C, hC, fun S hSu hpoor => hcover S ((hmem S).mpr ⟨hSu, hpoor⟩)⟩
  · refine ⟨∅, by simp, ?_⟩
    intro S _ hpoor
    have hnonneg := projectionMass_nonneg μ Z S
    linarith

#print axioms exists_maximal_disjoint_cover
#print axioms exists_cover_of_disjoint_card_lt
#print axioms exists_cover_of_no_disjoint_subfamily
#print axioms projection_cover

end Paper2.ProductProjections
