import Paper2.SourceProjectionProtected

/-!
# Deficient items and diagonal coordinates of retained source inputs

Frozen v12 Section 4, `src:near-full`, the protected deletion estimates in
the surviving-collisions paragraph. The deficient sets are defined from
the actual retained source inputs and their original base laws. Their
cardinal bounds follow from the constructed protected mixture, not from
a supplied population-count certificate. Strict bounds require positive
deletion allowance, including when the deficient population is empty.
-/

namespace Paper2.SourceDeficiency

open scoped BigOperators
open SourceMatrix SourceLawBinding SourceProjectionRetention

variable {I X V Y : Type*} {q₁ q₂ s : ℕ}

/-- Strict finite Markov counting on the deficit `1 - p i`. No lower
bound on `p` is needed; the nonnegative deficits follow from `p i ≤ 1`. -/
theorem deficient_card_mul_lt [Fintype I] [Nonempty I]
    (p : I → ℝ) (t ε : ℝ) (hε : 0 < ε)
    (hp : ∀ i, p i ≤ 1)
    (havg : 1 - ε ≤ (Fintype.card I : ℝ)⁻¹ * ∑ i, p i) :
    ((Finset.univ.filter fun i => p i < t).card : ℝ) * (1 - t) <
      ε * Fintype.card I := by
  classical
  let B := Finset.univ.filter fun i => p i < t
  have hN : (0 : ℝ) < Fintype.card I := Nat.cast_pos.mpr Fintype.card_pos
  have hsum : (∑ i, (1 - p i)) ≤ ε * Fintype.card I := by
    have hmul := mul_le_mul_of_nonneg_left havg hN.le
    have hid : (Fintype.card I : ℝ) *
        ((Fintype.card I : ℝ)⁻¹ * ∑ i, p i) = ∑ i, p i := by
      rw [← mul_assoc, mul_inv_cancel₀ hN.ne', one_mul]
    rw [hid] at hmul
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, mul_one]
    nlinarith
  by_cases hB : B.Nonempty
  · have hstrict : (B.card : ℝ) * (1 - t) < ∑ i ∈ B, (1 - p i) := by
      have hh := Finset.sum_lt_sum_of_nonempty hB (fun i hi =>
        sub_lt_sub_left (Finset.mem_filter.mp hi).2 1)
      simpa only [Finset.sum_const, nsmul_eq_mul] using hh
    have hsub : (∑ i ∈ B, (1 - p i)) ≤ ∑ i, (1 - p i) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ B)
        (fun i _ _ => sub_nonneg.mpr (hp i))
    exact hstrict.trans_le (hsub.trans hsum)
  · have he : B = ∅ := Finset.not_nonempty_iff_eq_empty.mp hB
    change (B.card : ℝ) * (1 - t) < _
    simp only [he, Finset.card_empty, Nat.cast_zero, zero_mul]
    exact mul_pos hε hN

/-- The conditional item law is exactly an average over its actual labels. -/
theorem item_average [Fintype I] [Nonempty I] [Fintype X]
    (μ : PositiveRationalLaw X) (K : I × X → Prop) :
    (SourceLaws.itemRowLaw μ I).toFiniteLaw.prob K =
      (Fintype.card I : ℝ)⁻¹ * ∑ i, μ.toFiniteLaw.prob (fun x => K (i, x)) := by
  rw [SourceLaws.itemRowLaw, PositiveRationalLaw.toFiniteLaw_prod,
    FiniteLaw.prod_prob _ _ (fun i x => K (i, x))]
  simp only [PositiveRationalLaw.toFiniteLaw, PositiveRationalLaw.uniform,
    Rat.cast_inv, Rat.cast_natCast]
  rw [Finset.mul_sum]

section Items

variable [Fintype V] [Nonempty V] [Fintype X] [NeZero q₁]

noncomputable def vertexDeficient (μ : PositiveRationalLaw X)
    (W : Set (RawRow q₁ q₂ s X (SourceConstruction.Items s V))) :
    Finset (Fin (4 * s) × V) := by
  classical
  exact Finset.univ.filter fun i =>
    μ.toFiniteLaw.prob (fun x => Sum.inr ((i.1, Sum.inl i.2), x) ∈ W) < 1 / 2

noncomputable def auxiliaryDeficient (μ : PositiveRationalLaw X)
    (W : Set (RawRow q₁ q₂ s X (SourceConstruction.Items s V))) :
    Finset (Fin (4 * s) × Fin (s - 3)) := by
  classical
  exact Finset.univ.filter fun i =>
    μ.toFiniteLaw.prob (fun x => Sum.inr ((i.1, Sum.inr i.2), x) ∈ W) < 1 / 2

@[simp] theorem mem_vertexDeficient (μ : PositiveRationalLaw X)
    (W : Set (RawRow q₁ q₂ s X (SourceConstruction.Items s V))) (i : Fin (4 * s) × V) :
    i ∈ vertexDeficient μ W ↔
      μ.toFiniteLaw.prob (fun x => Sum.inr ((i.1, Sum.inl i.2), x) ∈ W) < 1 / 2 := by
  classical
  simp [vertexDeficient]

@[simp] theorem mem_auxiliaryDeficient (μ : PositiveRationalLaw X)
    (W : Set (RawRow q₁ q₂ s X (SourceConstruction.Items s V)))
    (i : Fin (4 * s) × Fin (s - 3)) :
    i ∈ auxiliaryDeficient μ W ↔
      μ.toFiniteLaw.prob (fun x => Sum.inr ((i.1, Sum.inr i.2), x) ∈ W) < 1 / 2 := by
  classical
  simp [auxiliaryDeficient]

/-- This single keep predicate can be passed to the source item-witness
theorem. It depends only on the original retained set, not on a coordinate. -/
def itemKept (μ : PositiveRationalLaw X)
    (W : Set (RawRow q₁ q₂ s X (SourceConstruction.Items s V)))
    (i : SourceConstruction.Items s V) : Prop :=
  1 / 2 ≤ μ.toFiniteLaw.prob (fun x => Sum.inr (i, x) ∈ W)

@[simp] theorem vertex_itemKept (μ : PositiveRationalLaw X)
    (W : Set (RawRow q₁ q₂ s X (SourceConstruction.Items s V))) (i : Fin (4 * s) × V) :
    itemKept μ W (i.1, Sum.inl i.2) ↔ i ∉ vertexDeficient μ W := by
  simp [itemKept]

@[simp] theorem auxiliary_itemKept (μ : PositiveRationalLaw X)
    (W : Set (RawRow q₁ q₂ s X (SourceConstruction.Items s V)))
    (i : Fin (4 * s) × Fin (s - 3)) :
    itemKept μ W (i.1, Sum.inr i.2) ↔ i ∉ auxiliaryDeficient μ W := by
  simp [itemKept]

/-- Fewer than `4096 η s |V|` actual vertex items lose over half their base mass. -/
theorem vertexDeficient_card_lt (μ : PositiveRationalLaw X) (hs : 4 ≤ s)
    (W : Set (RawRow q₁ q₂ s X (SourceConstruction.Items s V)))
    (η : ℝ) (hη : 0 < η)
    (hW : 1 - η ≤ (matrixColumnLaw μ q₁ q₂ s hs).toFiniteLaw.prob (· ∈ W)) :
    ((vertexDeficient μ W).card : ℝ) < 4096 * η * s * Fintype.card V := by
  classical
  letI : Nonempty (Fin (4 * s)) := ⟨⟨0, by omega⟩⟩
  have havg := vertex_columns_retained μ hs (· ∈ W) η hW
  change 1 - 512 * η ≤ (SourceLaws.itemRowLaw μ (Fin (4 * s) × V)).toFiniteLaw.prob
    (fun k => Sum.inr ((k.1.1, Sum.inl k.1.2), k.2) ∈ W) at havg
  rw [item_average] at havg
  have h := deficient_card_mul_lt
    (fun i : Fin (4 * s) × V =>
      μ.toFiniteLaw.prob (fun x => Sum.inr ((i.1, Sum.inl i.2), x) ∈ W))
    (1 / 2) (512 * η) (by positivity) (fun _ => μ.toFiniteLaw.prob_le_one _) havg
  change ((vertexDeficient μ W).card : ℝ) * (1 - 1 / 2) < _ at h
  simp only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul, Nat.cast_ofNat] at h
  nlinarith

/-- The auxiliary population has its own protected mass, independently of the vertex count. -/
theorem auxiliaryDeficient_card_lt (μ : PositiveRationalLaw X) (hs : 4 ≤ s)
    (W : Set (RawRow q₁ q₂ s X (SourceConstruction.Items s V)))
    (η : ℝ) (hη : 0 < η)
    (hW : 1 - η ≤ (matrixColumnLaw μ q₁ q₂ s hs).toFiniteLaw.prob (· ∈ W)) :
    ((auxiliaryDeficient μ W).card : ℝ) < 4096 * η * s * (s - 3 : ℕ) := by
  classical
  letI : Nonempty (Fin (4 * s)) := ⟨⟨0, by omega⟩⟩
  letI : Nonempty (Fin (s - 3)) := ⟨⟨0, by omega⟩⟩
  have havg := auxiliary_columns_retained μ hs (· ∈ W) η hW
  change 1 - 512 * η ≤
    (SourceLaws.itemRowLaw μ (Fin (4 * s) × Fin (s - 3))).toFiniteLaw.prob
      (fun k => Sum.inr ((k.1.1, Sum.inr k.1.2), k.2) ∈ W) at havg
  rw [item_average] at havg
  have h := deficient_card_mul_lt
    (fun i : Fin (4 * s) × Fin (s - 3) =>
      μ.toFiniteLaw.prob (fun x => Sum.inr ((i.1, Sum.inr i.2), x) ∈ W))
    (1 / 2) (512 * η) (by positivity) (fun _ => μ.toFiniteLaw.prob_le_one _) havg
  change ((auxiliaryDeficient μ W).card : ℝ) * (1 - 1 / 2) < _ at h
  simp only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul, Nat.cast_ofNat] at h
  nlinarith

end Items

section Diagonal

variable [Fintype Y] [NeZero q₂]

noncomputable def diagonalDeficient (ν : PositiveRationalLaw Y)
    (U : Set (TaggedColumn q₁ q₂ s Y)) : Finset (Fin q₂) := by
  classical
  exact Finset.univ.filter fun α =>
    (ν.iid (q₁ + s + 1)).toFiniteLaw.prob
      (fun γ => TaggedColumn.diagonal (α, γ) ∈ U) < 3 / 4

@[simp] theorem mem_diagonalDeficient (ν : PositiveRationalLaw Y)
    (U : Set (TaggedColumn q₁ q₂ s Y)) (α : Fin q₂) :
    α ∈ diagonalDeficient ν U ↔
      (ν.iid (q₁ + s + 1)).toFiniteLaw.prob
        (fun γ => TaggedColumn.diagonal (α, γ) ∈ U) < 3 / 4 := by
  classical
  simp [diagonalDeficient]

theorem diagonal_retained_of_not_deficient (ν : PositiveRationalLaw Y)
    (U : Set (TaggedColumn q₁ q₂ s Y)) (α : Fin q₂)
    (hα : α ∉ diagonalDeficient ν U) :
    3 / 4 ≤ (ν.iid (q₁ + s + 1)).toFiniteLaw.prob
      (fun γ => TaggedColumn.diagonal (α, γ) ∈ U) := by
  simpa only [mem_diagonalDeficient, not_lt] using hα

/-- The diagonal tag has mass `1/256`, so the manuscript's
`4 η q₂ / μ` bound is exactly `1024 η q₂`. -/
theorem diagonalDeficient_card_lt (ν : PositiveRationalLaw Y)
    (U : Set (TaggedColumn q₁ q₂ s Y)) (η : ℝ) (hη : 0 < η)
    (hU : 1 - η ≤ (matrixRowLaw ν q₁ q₂ s).toFiniteLaw.prob (· ∈ U)) :
    ((diagonalDeficient ν U).card : ℝ) < 1024 * η * q₂ := by
  classical
  have havg := SourceProjectionProtected.diagonal_average_retained ν U η hU
  have h := deficient_card_mul_lt
    (fun α : Fin q₂ => (ν.iid (q₁ + s + 1)).toFiniteLaw.prob
      (fun γ => TaggedColumn.diagonal (α, γ) ∈ U))
    (3 / 4) (256 * η) (by positivity)
    (fun _ => (ν.iid (q₁ + s + 1)).toFiniteLaw.prob_le_one _)
    (by simpa only [Fintype.card_fin] using havg)
  change ((diagonalDeficient ν U).card : ℝ) * (1 - 3 / 4) < _ at h
  simp only [Fintype.card_fin] at h
  nlinarith

end Diagonal

end Paper2.SourceDeficiency

#print axioms Paper2.SourceDeficiency.deficient_card_mul_lt
#print axioms Paper2.SourceDeficiency.vertexDeficient_card_lt
#print axioms Paper2.SourceDeficiency.auxiliaryDeficient_card_lt
#print axioms Paper2.SourceDeficiency.diagonalDeficient_card_lt
