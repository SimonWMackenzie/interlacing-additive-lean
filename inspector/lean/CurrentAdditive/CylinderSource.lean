import CurrentAdditive.SupportReductionExistence
import Paper2.SourceLaws
import CurrentAdditive.IndependentStreams

/-!
Proof-only rational cylinder source for v27 Appendix H, `det:code`.
The full product appears only to prove finite existence. This is not a
polynomial-time construction or a bit-complexity theorem.
-/

namespace CurrentAdditive

open Finset Paper2

/-- One cylinder feature consists of a small coordinate set and one word on it. -/
abbrev Cylinder (q D : ℕ) (Y : Type*) :=
  Σ J : {J : Finset (Fin q) // J.card ≤ D}, J.1 → Y

private def emptyCylinder (q D : ℕ) (Y : Type*) : Cylinder q D Y := by
  let J : {J : Finset (Fin q) // J.card ≤ D} := ⟨∅, by simp⟩
  refine ⟨J, ?_⟩
  intro i
  rcases i with ⟨i, hi⟩
  change i ∈ J.1 at hi
  dsimp [J] at hi
  simp at hi

/-- The zero-one indicator of a cylinder event in one decoded word. -/
def cylinderFeature {q D : ℕ} {Y : Type*} [DecidableEq Y]
    (v : Fin q → Y) (c : Cylinder q D Y) : ℚ :=
  if ∀ i : c.1.1, v i.1 = c.2 i then 1 else 0

theorem cylinder_card_as_subsets {Y : Type*} [Fintype Y] (q D : ℕ) :
    Fintype.card (Cylinder q D Y) =
      ∑ J : {J : Finset (Fin q) // J.card ≤ D},
        (Fintype.card Y) ^ J.1.card := by
  classical
  simp [Cylinder]

/-- The feature dimension is exactly the manuscript's binomial sum. -/
theorem cylinder_card_eq_moment_count {Y : Type*} [Fintype Y]
    (q D : ℕ) :
    Fintype.card (Cylinder q D Y) =
      ∑ j ∈ Finset.range (min D q + 1),
        Nat.choose q j * (Fintype.card Y) ^ j := by
  classical
  let S : Finset (Finset (Fin q)) :=
    Finset.univ.filter (fun J => J.card ≤ D)
  let m := Fintype.card Y
  have hsub :
      (∑ J : {J : Finset (Fin q) // J.card ≤ D}, m ^ J.1.card) =
        ∑ J ∈ S, m ^ J.card := by
    exact (Finset.sum_subtype S (fun J => by simp [S])
      (fun J => m ^ J.card)).symm
  have hmap : ∀ J ∈ S, J.card ∈ Finset.range (min D q + 1) := by
    intro J hJ
    have hD : J.card ≤ D := (Finset.mem_filter.mp hJ).2
    have hq : J.card ≤ q := by
      have h := Finset.card_le_card (Finset.subset_univ J)
      simpa using h
    simp only [Finset.mem_range]
    omega
  rw [cylinder_card_as_subsets, hsub]
  calc
    ∑ J ∈ S, m ^ J.card =
        ∑ j ∈ Finset.range (min D q + 1),
          ∑ J ∈ S.filter (fun J => J.card = j), m ^ J.card :=
            (Finset.sum_fiberwise_of_maps_to hmap (fun J => m ^ J.card)).symm
    _ = ∑ j ∈ Finset.range (min D q + 1), Nat.choose q j * m ^ j := by
      apply Finset.sum_congr rfl
      intro j hj
      have hjD : j ≤ D := by
        simp only [Finset.mem_range] at hj
        omega
      have hfilter : S.filter (fun J => J.card = j) =
          (Finset.univ : Finset (Fin q)).powersetCard j := by
        ext J
        simp only [S, Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.mem_powersetCard, Finset.subset_univ, true_and]
        constructor
        · exact fun ⟨_, hcard⟩ => hcard
        · exact fun hcard => ⟨hcard ▸ hjD, hcard⟩
      calc
        ∑ J ∈ S.filter (fun J => J.card = j), m ^ J.card =
            ∑ J ∈ S.filter (fun J => J.card = j), m ^ j := by
              apply Finset.sum_congr rfl
              intro J hJ
              rw [(Finset.mem_filter.mp hJ).2]
        _ = Nat.choose q j * m ^ j := by
          rw [Finset.sum_const, nsmul_eq_mul, hfilter,
            Finset.card_powersetCard]
          simp

private theorem emptyCylinder_feature {q D : ℕ} {Y : Type*} [DecidableEq Y]
    (v : Fin q → Y) :
    cylinderFeature v (emptyCylinder q D Y) = 1 := by
  simp [cylinderFeature, emptyCylinder]

/-- A compressed positive rational indexed source whose cylinder weights
equal those of the full independent product, for every cylinder of order at
most `D`. The seed is the subtype of retained words, so indices are explicit. -/
theorem exists_rational_cylinder_source
    {Y : Type*} [Fintype Y] [DecidableEq Y]
    (q D : ℕ) (μ : PositiveRationalLaw Y) :
    ∃ (t : Finset (Fin q → Y)) (ν : PositiveRationalLaw t),
      t.card ≤ ∑ j ∈ Finset.range (min D q + 1),
          Nat.choose q j * (Fintype.card Y) ^ j ∧
      ∀ c : Cylinder q D Y,
        (∑ x : t, if ∀ i : c.1.1, x.1 i.1 = c.2 i then ν.weight x else 0) =
          ∑ v : Fin q → Y,
            if ∀ i : c.1.1, v i.1 = c.2 i then (μ.iid q).weight v else 0 := by
  classical
  let φ : (Fin q → Y) → Cylinder q D Y → ℚ := cylinderFeature
  let w : (Fin q → Y) → ℚ := (μ.iid q).weight
  have hconst : ∀ v : Fin q → Y, φ v (emptyCylinder q D Y) = 1 := by
    intro v
    exact emptyCylinder_feature v
  obtain ⟨t, u, hsubset, hbound, hu, htotal, hmom⟩ :=
    exists_compressed_positive_weights φ (emptyCylinder q D Y) hconst
      Finset.univ w (fun v _ => (μ.iid q).positive v)
  have htotal_one : ∑ v ∈ t, u v = 1 := by
    rw [htotal]
    exact (μ.iid q).total
  let ν : PositiveRationalLaw t := {
    weight := fun x => u x.1
    positive := fun x => hu x.1 x.2
    total := by simpa only [Finset.sum_coe_sort] using htotal_one
  }
  refine ⟨t, ν, ?_, ?_⟩
  · simpa only [← cylinder_card_eq_moment_count q D] using hbound
  intro c
  have h := hmom c
  have hrat :
      (∑ v ∈ t, if ∀ i : c.1.1, v i.1 = c.2 i then u v else 0) =
        ∑ v : Fin q → Y,
          if ∀ i : c.1.1, v i.1 = c.2 i then (μ.iid q).weight v else 0 := by
    simpa only [φ, w, cylinderFeature, mul_ite, mul_one, mul_zero] using h
  change (∑ x : t, if ∀ i : c.1.1, x.1 i.1 = c.2 i then u x.1 else 0) = _
  exact (Finset.sum_coe_sort t
    (fun v => if ∀ i : c.1.1, v i.1 = c.2 i then u v else 0)).trans hrat

#print axioms exists_rational_cylinder_source

private theorem rational_cylinder_prob_eq_iid
    {Y : Type*} [Fintype Y] [DecidableEq Y]
    (q D : ℕ) (μ : PositiveRationalLaw Y)
    (t : Finset (Fin q → Y)) (ν : PositiveRationalLaw t)
    (hfeatures : ∀ c : Cylinder q D Y,
      (∑ x : t, if ∀ i : c.1.1, x.1 i.1 = c.2 i then ν.weight x else 0) =
        ∑ v : Fin q → Y,
          if ∀ i : c.1.1, v i.1 = c.2 i then (μ.iid q).weight v else 0)
    (c : Cylinder q D Y) :
    ν.toFiniteLaw.prob (fun x => ∀ i : c.1.1, x.1 i.1 = c.2 i) =
      (μ.toFiniteLaw.iid q).prob (fun v => ∀ i : c.1.1, v i.1 = c.2 i) := by
  rw [← PositiveRationalLaw.toFiniteLaw_iid μ q]
  have hreal := congrArg (fun r : ℚ => (r : ℝ)) (hfeatures c)
  have hcast (P : Prop) [Decidable P] (a : ℚ) :
      ((if P then a else 0 : ℚ) : ℝ) = if P then (a : ℝ) else 0 := by
    split_ifs <;> simp
  push_cast at hreal
  simp_rw [hcast] at hreal
  simpa [Paper2.FiniteLaw.prob, PositiveRationalLaw.toFiniteLaw] using hreal

private theorem iid_eq_pi_const {Y : Type*} [Fintype Y]
    (μ : Paper2.FiniteLaw Y) (q : ℕ) :
    μ.iid q = Paper2.FiniteLaw.pi (fun _ : Fin q => μ) := by
  rfl

/-- The compressed rational indexed list has exactly the same law on every
set of at most `D` decoded coordinates as the independent product marginal.
Distinct seed indices are retained, even if their decoded words coincide. -/
theorem exists_rational_dwise_source
    {Y : Type*} [Fintype Y] [DecidableEq Y]
    (q D : ℕ) (μ : PositiveRationalLaw Y) :
    ∃ (t : Finset (Fin q → Y)) (ν : PositiveRationalLaw t),
      t.card ≤ ∑ j ∈ Finset.range (min D q + 1),
          Nat.choose q j * (Fintype.card Y) ^ j ∧
      IsDWise D ν.toFiniteLaw (fun x : t => x.1) μ.toFiniteLaw := by
  classical
  obtain ⟨t, ν, hbound, hfeatures⟩ := exists_rational_cylinder_source q D μ
  refine ⟨t, ν, hbound, ?_⟩
  intro s hs E
  apply Paper2.FiniteLaw.prob_preimage_eq_of_fibres ν.toFiniteLaw
    (Paper2.FiniteLaw.pi (fun _ : s => μ.toFiniteLaw))
    (fun x i => x.1 i.1)
  intro y
  let c : Cylinder q D Y := ⟨⟨s, hs⟩, y⟩
  have hc := rational_cylinder_prob_eq_iid q D μ t ν hfeatures c
  have hrestrict := Paper2.FiniteLaw.pi_prob_restrict
    (fun _ : Fin q => μ.toFiniteLaw) (fun i : s => i.1)
      Subtype.val_injective (fun z => z = y)
  rw [← iid_eq_pi_const μ.toFiniteLaw q] at hrestrict
  rw [Paper2.FiniteLaw.prob_singleton] at hrestrict
  have hc' :
      ν.toFiniteLaw.prob (fun x => (fun i : s => x.1 i.1) = y) =
        (μ.toFiniteLaw.iid q).prob (fun v => (fun i : s => v i.1) = y) := by
    simpa only [c, funext_iff] using hc
  exact hc'.trans hrestrict

#print axioms exists_rational_dwise_source

end CurrentAdditive
