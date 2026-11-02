import CurrentAdditive.DeterministicIndexedLaws

/-! Appendix I, `det:construction`: the three positive rational tagged
column populations on indexed labels. This file does not condition a source. -/

namespace CurrentAdditive.DeterministicIndexedMatrix

open Paper2 Paper2.SourceMatrix

variable {X Y : Type*} [Fintype X] [Fintype Y]
  [DecidableEq X] [DecidableEq Y]
  {D q₁ q₂ s : ℕ} [NeZero s] [NeZero q₁] [NeZero q₂]
  {μX : PositiveRationalLaw X} {μY : PositiveRationalLaw Y}
  (src : Sources (D := D) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY)

namespace Sources

def columnEquiv : Column src ≃
    (src.outer.Label × src.gamma.Label) ⊕
      (src.outer.Label ⊕ (Fin q₂ × src.gamma.Label)) where
  toFun
    | .ordinary x => .inl x
    | .fixedTail x => .inr (.inl x)
    | .diagonal x => .inr (.inr x)
  invFun
    | .inl x => .ordinary x
    | .inr (.inl x) => .fixedTail x
    | .inr (.inr x) => .diagonal x
  left_inv x := by cases x <;> rfl
  right_inv x := by rcases x with x | (x | x) <;> rfl

theorem column_sum {A : Type*} [AddCommMonoid A]
    (f : Column src → A) :
    (∑ Z, f Z) = (∑ Z, f (.ordinary Z)) +
      (∑ Z, f (.fixedTail Z)) + ∑ Z, f (.diagonal Z) := by
  rw [← (columnEquiv src).symm.sum_comp]
  simp only [Fintype.sum_sum_type, columnEquiv, Equiv.coe_fn_symm_mk]
  exact (add_assoc _ _ _).symm

noncomputable def ordinaryLaw :
    PositiveRationalLaw (src.outer.Label × src.gamma.Label) :=
  src.outer.law.prod src.gamma.law

noncomputable def diagonalLaw :
    PositiveRationalLaw (Fin q₂ × src.gamma.Label) :=
  (PositiveRationalLaw.uniform (Fin q₂)).prod src.gamma.law

/-- The ordinary, fixed-tail and diagonal families have exactly the manuscript
masses 127/128, 1/256 and 1/256. Every index has positive mass. -/
noncomputable def columnLaw : PositiveRationalLaw (Column src) where
  weight
    | .ordinary Z => (127 / 128) * (ordinaryLaw src).weight Z
    | .fixedTail Z => (1 / 256) * src.outer.law.weight Z
    | .diagonal Z => (1 / 256) * (diagonalLaw src).weight Z
  positive Z := by
    cases Z with
    | ordinary Z => exact mul_pos (by norm_num) ((ordinaryLaw src).positive Z)
    | fixedTail Z => exact mul_pos (by norm_num) (src.outer.law.positive Z)
    | diagonal Z => exact mul_pos (by norm_num) ((diagonalLaw src).positive Z)
  total := by
    rw [column_sum]
    simp only [← Finset.mul_sum, (ordinaryLaw src).total,
      src.outer.law.total, (diagonalLaw src).total, mul_one]
    norm_num

end Sources

end CurrentAdditive.DeterministicIndexedMatrix
