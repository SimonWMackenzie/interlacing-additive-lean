import Paper2.ProjectionCover

/-!
# Simultaneous exceptional-coordinate covers for restoration

Frozen v12, Section 5, lines 219--248. The retained event is the same
arbitrary subset of the full iid product in every application. The three
strict power gaps are intermediate inputs; deriving them from the public
schedule is a separate arithmetic obligation.
-/

namespace Paper2.RestorationCovers

open scoped BigOperators

variable {K : Type*} [Fintype K]

/-- The constant finite product law is exactly the existing iid law, even
at zero coordinates. -/
theorem pi_const_prob (κ : FiniteLaw K) (w : ℕ)
    (Z : (Fin w → K) → Prop) :
    (FiniteLaw.pi (fun _ : Fin w => κ)).prob Z = (κ.iid w).prob Z := by
  rfl

/-- The small dyadic capacities contribute one pair and one larger
coordinate set at each dyadic level below `2^m`. -/
def smallSize (j : ℕ) : ℕ := 2 ^ (j + 1) + 1

theorem small_sizes_sum_plus_two (n : ℕ) :
    (∑ j ∈ Finset.range n, smallSize j) + 2 = 2 ^ (n + 1) + n := by
  induction n with
  | zero => simp [smallSize]
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have hp : 2 ^ (n + 1 + 1) = 2 * 2 ^ (n + 1) := by
      rw [pow_succ]
      omega
    simp only [smallSize] at *
    rw [hp]
    omega

theorem small_sizes_sum (m : ℕ) (hm : 2 ≤ m) :
    2 + ∑ j : Fin (m - 2), smallSize j.val = 2 ^ (m - 1) + m - 2 := by
  have h : (∑ j : Fin (m - 2), smallSize j.val) + 2 =
      2 ^ (m - 2 + 1) + (m - 2) := by
    simpa only [Fin.sum_univ_eq_sum_range] using small_sizes_sum_plus_two (m - 2)
  have hindex : m - 2 + 1 = m - 1 := by omega
  rw [hindex] at h
  omega

/-- The exact `e₀` of frozen v12, with `t* = 2^m`. -/
def exceptionBudget (B₀ B₁ B₂ m : ℕ) : ℕ :=
  (B₀ - 1) * (2 ^ (m - 1) + m - 2) + (B₁ - 1) + 2 * (B₂ - 1)

private theorem disjoint_of_subset_right {w : ℕ}
    {A B C : Finset (Fin w)} (hBC : B ⊆ C) (hAC : Disjoint A C) :
    Disjoint A B := by
  apply Finset.disjoint_left.mpr
  intro x hxA hxB
  exact (Finset.disjoint_left.mp hAC) hxA (hBC hxB)

/-- One actual exceptional set simultaneously protects singleton, pair,
and all dyadic-small projections of the *same* correlated retained event.
The power gaps are arithmetic inputs, not desired-cover certificates. -/
theorem cover_three_families (κ : FiniteLaw K) (w m B₀ B₁ B₂ : ℕ)
    (hm : 2 ≤ m) (hB₀ : 1 ≤ B₀) (hB₁ : 1 ≤ B₁) (hB₂ : 1 ≤ B₂)
    (Y' : Set (Fin w → K)) (θ η : ℝ)
    (hY : θ ≤ (κ.iid w).prob (· ∈ Y'))
    (hgap₀ : (18 / 25 : ℝ) ^ B₀ < θ)
    (hgap₁ : (1 - η) ^ B₁ < θ)
    (hgap₂ : (99 / 100 : ℝ) ^ B₂ < θ) :
    ∃ E₀ : Finset (Fin w),
      E₀.card ≤ exceptionBudget B₀ B₁ B₂ m ∧
      (∀ S : Finset (Fin w), S.card = 1 → Disjoint S E₀ →
        1 - η ≤ ProductProjections.projectionMass (fun _ => κ) (· ∈ Y') S) ∧
      (∀ S : Finset (Fin w), S.card = 2 → Disjoint S E₀ →
        (99 / 100 : ℝ) ≤ ProductProjections.projectionMass (fun _ => κ) (· ∈ Y') S) ∧
      (∀ S : Finset (Fin w), S.card = 2 → Disjoint S E₀ →
        (18 / 25 : ℝ) ≤ ProductProjections.projectionMass (fun _ => κ) (· ∈ Y') S) ∧
      (∀ j : Fin (m - 2), ∀ S : Finset (Fin w),
        S.card = smallSize j.val → Disjoint S E₀ →
          (18 / 25 : ℝ) ≤ ProductProjections.projectionMass
            (fun _ => κ) (· ∈ Y') S) := by
  classical
  have hYpi : θ ≤ (FiniteLaw.pi (fun _ : Fin w => κ)).prob (· ∈ Y') := by
    rwa [pi_const_prob]
  obtain ⟨C₁, hC₁, hcov₁⟩ := ProductProjections.projection_cover
    (fun _ : Fin w => κ) (· ∈ Y') 1 B₁ hB₁ θ (1 - η) hYpi hgap₁
  obtain ⟨C₂, hC₂, hcov₂⟩ := ProductProjections.projection_cover
    (fun _ : Fin w => κ) (· ∈ Y') 2 B₂ hB₂ θ (99 / 100) hYpi hgap₂
  obtain ⟨C₀₂, hC₀₂, hcov₀₂⟩ := ProductProjections.projection_cover
    (fun _ : Fin w => κ) (· ∈ Y') 2 B₀ hB₀ θ (18 / 25) hYpi hgap₀
  let witness (j : Fin (m - 2)) := ProductProjections.projection_cover
    (fun _ : Fin w => κ) (· ∈ Y') (smallSize j.val) B₀ hB₀ θ
    (18 / 25) hYpi hgap₀
  let Csmall (j : Fin (m - 2)) : Finset (Fin w) := Classical.choose (witness j)
  have hCsmall (j : Fin (m - 2)) :
      (Csmall j).card ≤ smallSize j.val * (B₀ - 1) :=
    (Classical.choose_spec (witness j)).1
  have hcovsmall (j : Fin (m - 2)) (S : Finset (Fin w))
      (hS : S.card = smallSize j.val)
      (hpoor : ProductProjections.projectionMass (fun _ => κ) (· ∈ Y') S < 18 / 25) :
      ¬ Disjoint S (Csmall j) :=
    (Classical.choose_spec (witness j)).2 S hS hpoor
  let U : Finset (Fin w) := Finset.univ.biUnion Csmall
  let E₀ : Finset (Fin w) := C₁ ∪ C₂ ∪ C₀₂ ∪ U
  have hU : U.card ≤ ∑ j : Fin (m - 2), (Csmall j).card := by
    exact Finset.card_biUnion_le
  have hUsum : U.card ≤ (∑ j : Fin (m - 2), smallSize j.val) * (B₀ - 1) := by
    calc
      U.card ≤ ∑ j : Fin (m - 2), (Csmall j).card := hU
      _ ≤ ∑ j : Fin (m - 2), smallSize j.val * (B₀ - 1) := by
        apply Finset.sum_le_sum
        intro j _
        exact hCsmall j
      _ = _ := by rw [Finset.sum_mul]
  have hEcard : E₀.card ≤ exceptionBudget B₀ B₁ B₂ m := by
    have hUnion : E₀.card ≤ C₁.card + C₂.card + C₀₂.card + U.card := by
      dsimp [E₀]
      have h1 := Finset.card_union_le C₁ C₂
      have h2 := Finset.card_union_le (C₁ ∪ C₂) C₀₂
      have h3 := Finset.card_union_le (C₁ ∪ C₂ ∪ C₀₂) U
      omega
    have hgeo := small_sizes_sum m hm
    calc
      E₀.card ≤ C₁.card + C₂.card + C₀₂.card + U.card := hUnion
      _ ≤ (B₁ - 1) + 2 * (B₂ - 1) + 2 * (B₀ - 1) +
          (∑ j : Fin (m - 2), smallSize j.val) * (B₀ - 1) := by omega
      _ = exceptionBudget B₀ B₁ B₂ m := by
        unfold exceptionBudget
        rw [← hgeo]
        ring
  refine ⟨E₀, hEcard, ?_, ?_, ?_, ?_⟩
  · intro S hS hdisj
    have hsub : C₁ ⊆ E₀ := by intro x hx; simp [E₀, hx]
    have hd := disjoint_of_subset_right hsub hdisj
    by_contra hn
    exact (hcov₁ S hS (lt_of_not_ge hn)) hd
  · intro S hS hdisj
    have hsub : C₂ ⊆ E₀ := by intro x hx; simp [E₀, hx]
    have hd := disjoint_of_subset_right hsub hdisj
    by_contra hn
    exact (hcov₂ S hS (lt_of_not_ge hn)) hd
  · intro S hS hdisj
    have hsub : C₀₂ ⊆ E₀ := by intro x hx; simp [E₀, hx]
    have hd := disjoint_of_subset_right hsub hdisj
    by_contra hn
    exact (hcov₀₂ S hS (lt_of_not_ge hn)) hd
  · intro j S hS hdisj
    have hsub : Csmall j ⊆ E₀ := by
      intro x hx
      have hu : x ∈ U := Finset.mem_biUnion.mpr
        ⟨j, Finset.mem_univ j, hx⟩
      simp [E₀, hu]
    have hd := disjoint_of_subset_right hsub hdisj
    by_contra hn
    exact (hcovsmall j S hS (lt_of_not_ge hn)) hd

end Paper2.RestorationCovers

#print axioms Paper2.RestorationCovers.pi_const_prob
#print axioms Paper2.RestorationCovers.small_sizes_sum
#print axioms Paper2.RestorationCovers.cover_three_families
