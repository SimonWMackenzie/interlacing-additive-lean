import CurrentAdditive.DeterministicIndexedUpper

/-! The finite support bound inherited from the checked rational cylinder
existence theorem. This is a cardinality bound, not an algorithmic runtime. -/

namespace CurrentAdditive.DeterministicIndexedMatrix

open Paper2

theorem chosenCodeSource_card_le {Y : Type*} [Fintype Y] [DecidableEq Y]
    (D q : ℕ) (μ : PositiveRationalLaw Y) :
    Fintype.card (chooseCodeSource D q μ).Label ≤
      ∑ j ∈ Finset.range (min D q + 1),
        Nat.choose q j * (Fintype.card Y) ^ j := by
  classical
  let h := exists_rational_dwise_source q D μ
  have hb := (Classical.choose_spec (Classical.choose_spec h)).1
  simpa only [chooseCodeSource, Fintype.card_coe] using hb

#print axioms chosenCodeSource_card_le

end CurrentAdditive.DeterministicIndexedMatrix
