import CurrentAdditive.DeterministicIndexedProfileEntries

/-! Profile preparation: exact retained-mass identities for the actual
indexed row and tagged column laws. No complexity lower bound is assumed. -/

namespace CurrentAdditive.DeterministicIndexedMatrix

open Paper2

variable {G V A X Y : Type*} [Fintype G] [Fintype V] [Fintype A]
  [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
  {D q₁ q₂ s : ℕ} [NeZero s] [NeZero q₁] [NeZero q₂]
  {μX : PositiveRationalLaw X} {μY : PositiveRationalLaw Y}
  (src : Sources (D := D) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY)

namespace Sources

theorem row_prob_split (μI : PositiveRationalLaw (G × (V ⊕ A)))
    (U : Set (Row (I := G × (V ⊕ A)) src)) :
    (rowLaw src μI).toFiniteLaw.prob (· ∈ U) =
      (255 / 256 : ℝ) *
        (templateRowLaw src).toFiniteLaw.prob (fun pz => Sum.inl pz ∈ U) +
      (1 / 256 : ℝ) *
        (sourceRowLaw (μX := μX) μI).toFiniteLaw.prob
          (fun iu => Sum.inr iu ∈ U) := by
  classical
  simp only [Paper2.FiniteLaw.prob, Paper2.PositiveRationalLaw.toFiniteLaw,
    rowLaw]
  rw [Fintype.sum_sum_type]
  simp only [Finset.mul_sum, mul_ite, mul_zero]
  push_cast
  rfl

theorem template_retained (μI : PositiveRationalLaw (G × (V ⊕ A)))
    (U : Set (Row (I := G × (V ⊕ A)) src)) (β : ℝ)
    (hβ : β ≤ (rowLaw src μI).toFiniteLaw.prob (· ∈ U)) :
    (β - (1 - 255 / 256)) / (255 / 256 : ℝ) ≤
      (templateRowLaw src).toFiniteLaw.prob
        (fun pz => Sum.inl pz ∈ U) := by
  rw [row_prob_split] at hβ
  have hsource := (sourceRowLaw (μX := μX) μI).toFiniteLaw.prob_le_one
    (fun iu => Sum.inr iu ∈ U)
  linarith

theorem column_prob_split (U : Set (Column src)) :
    (columnLaw src).toFiniteLaw.prob (· ∈ U) =
      (127 / 128 : ℝ) * (ordinaryLaw src).toFiniteLaw.prob
        (fun z => Column.ordinary z ∈ U) +
      (1 / 256 : ℝ) * src.outer.law.toFiniteLaw.prob
        (fun z => Column.fixedTail z ∈ U) +
      (1 / 256 : ℝ) * (diagonalLaw src).toFiniteLaw.prob
        (fun z => Column.diagonal z ∈ U) := by
  classical
  simp only [Paper2.FiniteLaw.prob, Paper2.PositiveRationalLaw.toFiniteLaw,
    columnLaw]
  rw [column_sum]
  simp only [Finset.mul_sum, mul_ite, mul_zero]
  push_cast
  rfl

theorem ordinary_retained (U : Set (Column src)) (β : ℝ)
    (hβ : β ≤ (columnLaw src).toFiniteLaw.prob (· ∈ U)) :
    (β - (1 - 127 / 128)) / (127 / 128 : ℝ) ≤
      (ordinaryLaw src).toFiniteLaw.prob
        (fun z => Column.ordinary z ∈ U) := by
  rw [column_prob_split] at hβ
  have hf := src.outer.law.toFiniteLaw.prob_le_one
    (fun z => Column.fixedTail z ∈ U)
  have hd := (diagonalLaw src).toFiniteLaw.prob_le_one
    (fun z => Column.diagonal z ∈ U)
  linarith

end Sources

end CurrentAdditive.DeterministicIndexedMatrix
