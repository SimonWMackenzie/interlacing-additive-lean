import CurrentAdditive.DeterministicIndexedBounds

/-! Private finite carrier bounds for the actual chosen CodeSource calls.
These are mathematical support cardinalities, not a runtime theorem for
computing or writing the lists. -/

namespace CurrentAdditive.DeterministicIndexedMatrix

open Paper2

def codeSupportBound (D q n : ℕ) : ℕ :=
  ∑ j ∈ Finset.range (min D q + 1), Nat.choose q j * n ^ j

theorem chosenCodeSource_card_le_support
    {Y : Type*} [Fintype Y] [DecidableEq Y]
    (D q : ℕ) (μ : PositiveRationalLaw Y) :
    Fintype.card (chooseCodeSource D q μ).Label ≤
      codeSupportBound D q (Fintype.card Y) := by
  exact chosenCodeSource_card_le D q μ

variable {X Y I : Type*} [Fintype X] [Fintype Y] [Fintype I]
  [DecidableEq X] [DecidableEq Y] [DecidableEq I]
  {D q₁ q₂ s : ℕ} [NeZero s] [NeZero q₁] [NeZero q₂]

theorem chosenSources_gamma_card_le
    (μX : PositiveRationalLaw X) (μY : PositiveRationalLaw Y) :
    Fintype.card (chosenSources (D := D) (q₁ := q₁) (q₂ := q₂)
      (s := s) μX μY).gamma.Label ≤
      codeSupportBound D (q₁ + s + 1) (Fintype.card Y) := by
  exact chosenCodeSource_card_le_support D (q₁ + s + 1) μY

theorem chosenSources_inner_card_le
    (μX : PositiveRationalLaw X) (μY : PositiveRationalLaw Y) :
    Fintype.card (chosenSources (D := D) (q₁ := q₁) (q₂ := q₂)
      (s := s) μX μY).inner.Label ≤
      codeSupportBound D q₂ (q₁ * Fintype.card X) := by
  simpa only [Fintype.card_prod, Fintype.card_fin] using
    (chosenCodeSource_card_le_support D q₂
      ((PositiveRationalLaw.uniform (Fin q₁)).prod μX))

theorem chosenSources_outer_card_le
    (μX : PositiveRationalLaw X) (μY : PositiveRationalLaw Y) :
    let src := chosenSources (D := D) (q₁ := q₁) (q₂ := q₂)
      (s := s) μX μY
    Fintype.card src.outer.Label ≤
      codeSupportBound D s (q₂ * Fintype.card src.gamma.Label) := by
  dsimp only
  simpa only [Fintype.card_prod, Fintype.card_fin] using
    (chosenCodeSource_card_le_support D s
      ((PositiveRationalLaw.uniform (Fin q₂)).prod
        (chosenSources (D := D) (q₁ := q₁) (q₂ := q₂)
          (s := s) μX μY).gamma.law))

namespace Sources

variable {μX : PositiveRationalLaw X} {μY : PositiveRationalLaw Y}
  (src : Sources (D := D) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY)

/-- Dimensions of the final actual indexed matrix after all source calls.
The bounds are from the concrete chosen finite supports. -/
theorem chosen_successor_carriers_card_le
    (μI : PositiveRationalLaw I) (w Q : ℕ) [NeZero w] :
    let streams := chosenInternal src μI w
    let final := chosenFinal src w Q
    Fintype.card final.Label ≤
      codeSupportBound D Q (w * Fintype.card (Column src)) ∧
    Fintype.card (Fin Q ×
      (streams.metadataStream.Label ×
        (streams.baseStream.Label × streams.selectorStream.Label))) ≤
      Q * codeSupportBound D w (s + Fintype.card I) *
        codeSupportBound D w (Fintype.card X) *
        codeSupportBound D w (Fintype.card src.inner.Label) := by
  constructor
  · simpa only [Fintype.card_prod, Fintype.card_fin] using
      (chosenCodeSource_card_le_support D Q
        ((PositiveRationalLaw.uniform (Fin w)).prod (columnLaw src)))
  · have hm := chosenCodeSource_card_le_support D w (metadataLaw (s := s) μI)
    have hb := chosenCodeSource_card_le_support D w μX
    have hs := chosenCodeSource_card_le_support D w src.inner.law
    have hmeta : Fintype.card (Fin s ⊕ I) = s + Fintype.card I := by
      simp
    rw [hmeta] at hm
    change Fintype.card (Fin Q ×
      ((chooseCodeSource D w (metadataLaw (s := s) μI)).Label ×
        ((chooseCodeSource D w μX).Label ×
          (chooseCodeSource D w src.inner.law).Label))) ≤ _
    simpa only [Fintype.card_prod, Fintype.card_fin, mul_assoc] using
      (Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul_left Q hm) hb) hs)

#print axioms chosenSources_gamma_card_le
#print axioms chosenSources_inner_card_le
#print axioms chosenSources_outer_card_le
#print axioms chosen_successor_carriers_card_le

end Sources
end CurrentAdditive.DeterministicIndexedMatrix
