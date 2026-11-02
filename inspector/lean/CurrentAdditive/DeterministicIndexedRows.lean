import CurrentAdditive.DeterministicIndexedMass

/-! Appendix I, `det:construction`: rational template/source row masses. -/

namespace CurrentAdditive.DeterministicIndexedMatrix

open Paper2

variable {G V A X Y : Type*} [Fintype G] [Fintype V] [Fintype A]
  [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
  {D q₁ q₂ s : ℕ} [NeZero s] [NeZero q₁] [NeZero q₂]

/-- Two disjoint item classes, each carrying half the item mass. -/
noncomputable def halfSumLaw (μV : PositiveRationalLaw V)
    (μA : PositiveRationalLaw A) : PositiveRationalLaw (V ⊕ A) where
  weight
    | .inl v => (1 / 2) * μV.weight v
    | .inr a => (1 / 2) * μA.weight a
  positive x := by
    cases x with
    | inl v => exact mul_pos (by norm_num) (μV.positive v)
    | inr a => exact mul_pos (by norm_num) (μA.positive a)
  total := by
    rw [Fintype.sum_sum_type]
    simp only [← Finset.mul_sum, μV.total, μA.total, mul_one]
    norm_num

/-- The v27 public item law: uniform group, and equal vertex/auxiliary
class masses. The graph incidence relation does not enter this law. -/
noncomputable def itemLaw [Nonempty G] [Nonempty V] [Nonempty A] :
    PositiveRationalLaw (G × (V ⊕ A)) :=
  (PositiveRationalLaw.uniform G).prod
    (halfSumLaw (PositiveRationalLaw.uniform V) (PositiveRationalLaw.uniform A))

namespace Sources

variable {μX : PositiveRationalLaw X} {μY : PositiveRationalLaw Y}
  (src : Sources (D := D) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY)

noncomputable def templateRowLaw :
    PositiveRationalLaw (Fin s × src.inner.Label) :=
  (PositiveRationalLaw.uniform (Fin s)).prod src.inner.law

noncomputable def sourceRowLaw (μI : PositiveRationalLaw (G × (V ⊕ A))) :
    PositiveRationalLaw ((G × (V ⊕ A)) × X) :=
  μI.prod μX

/-- Template mass 255/256; vertex and auxiliary rows each receive 1/512
when μI is `itemLaw`. -/
noncomputable def rowLaw (μI : PositiveRationalLaw (G × (V ⊕ A))) :
    PositiveRationalLaw (Row (I := G × (V ⊕ A)) src) where
  weight
    | .inl pz => (255 / 256) * (templateRowLaw src).weight pz
    | .inr iu => (1 / 256) * (sourceRowLaw (μX := μX) μI).weight iu
  positive x := by
    cases x with
    | inl pz => exact mul_pos (by norm_num) ((templateRowLaw src).positive pz)
    | inr iu => exact mul_pos (by norm_num) ((sourceRowLaw (μX := μX) μI).positive iu)
  total := by
    rw [Fintype.sum_sum_type]
    simp only [← Finset.mul_sum, (templateRowLaw src).total,
      (sourceRowLaw (μX := μX) μI).total, mul_one]
    norm_num

end Sources

end CurrentAdditive.DeterministicIndexedMatrix
