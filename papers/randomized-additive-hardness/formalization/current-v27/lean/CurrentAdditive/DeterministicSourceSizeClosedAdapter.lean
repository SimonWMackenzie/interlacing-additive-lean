import CurrentAdditive.DeterministicSourceSize

namespace CurrentAdditive.DeterministicIndexedMatrix

open Paper2

theorem codeSupportBound_mono (D q : ℕ) {n m : ℕ} (hnm : n ≤ m) :
    codeSupportBound D q n ≤ codeSupportBound D q m := by
  unfold codeSupportBound
  apply Finset.sum_le_sum
  intro j _
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hnm j)

namespace Sources

variable {X Y I : Type*} [Fintype X] [Fintype Y] [Fintype I]
  [DecidableEq X] [DecidableEq Y] [DecidableEq I]
  {D q₁ q₂ s : ℕ} [NeZero s] [NeZero q₁] [NeZero q₂]
  {μX : PositiveRationalLaw X} {μY : PositiveRationalLaw Y}
  (src : Sources (D := D) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY)

theorem column_card_eq :
    Fintype.card (Column src) =
      Fintype.card src.outer.Label * Fintype.card src.gamma.Label +
      Fintype.card src.outer.Label + q₂ * Fintype.card src.gamma.Label := by
  classical
  simpa only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin,
    add_assoc] using Fintype.card_congr (columnEquiv src)

theorem successor_carriers_card_le_closed (μI : PositiveRationalLaw I)
    (w Q G S J : ℕ) [NeZero w]
    (hgamma : Fintype.card src.gamma.Label ≤ G)
    (hinner : Fintype.card src.inner.Label ≤ S)
    (houter : Fintype.card src.outer.Label ≤ J) :
    let streams := chosenInternal src μI w
    let final := chosenFinal src w Q
    Fintype.card final.Label ≤
      codeSupportBound D Q (w * (J * G + J + q₂ * G)) ∧
    Fintype.card (Fin Q ×
      (streams.metadataStream.Label ×
        (streams.baseStream.Label × streams.selectorStream.Label))) ≤
      Q * codeSupportBound D w (s + Fintype.card I) *
        codeSupportBound D w (Fintype.card X) * codeSupportBound D w S := by
  have hcol : Fintype.card (Column src) ≤ J * G + J + q₂ * G := by
    rw [column_card_eq]
    gcongr
  have hsrc := chosen_successor_carriers_card_le src μI w Q
  constructor
  · exact hsrc.1.trans
      (codeSupportBound_mono D Q (Nat.mul_le_mul_left w hcol))
  · exact hsrc.2.trans
      (Nat.mul_le_mul_left
        (Q * codeSupportBound D w (s + Fintype.card I) *
          codeSupportBound D w (Fintype.card X))
        (codeSupportBound_mono D w hinner))

/-- A closed finite bound for the actual source choices, with no intermediate
generated carrier cardinality on the right-hand side. -/
theorem chosen_successor_carriers_card_le_explicit
    (μI : PositiveRationalLaw I) (w Q : ℕ) [NeZero w] :
    let src := chosenSources (D := D) (q₁ := q₁) (q₂ := q₂)
      (s := s) μX μY
    let G := codeSupportBound D (q₁ + s + 1) (Fintype.card Y)
    let S := codeSupportBound D q₂ (q₁ * Fintype.card X)
    let J := codeSupportBound D s (q₂ * G)
    let streams := chosenInternal src μI w
    let final := chosenFinal src w Q
    Fintype.card final.Label ≤
      codeSupportBound D Q (w * (J * G + J + q₂ * G)) ∧
    Fintype.card (Fin Q ×
      (streams.metadataStream.Label ×
        (streams.baseStream.Label × streams.selectorStream.Label))) ≤
      Q * codeSupportBound D w (s + Fintype.card I) *
        codeSupportBound D w (Fintype.card X) * codeSupportBound D w S := by
  let src := chosenSources (D := D) (q₁ := q₁) (q₂ := q₂)
    (s := s) μX μY
  let G := codeSupportBound D (q₁ + s + 1) (Fintype.card Y)
  let S := codeSupportBound D q₂ (q₁ * Fintype.card X)
  let J := codeSupportBound D s (q₂ * G)
  have hG : Fintype.card src.gamma.Label ≤ G := by
    exact chosenSources_gamma_card_le μX μY
  have hS : Fintype.card src.inner.Label ≤ S := by
    exact chosenSources_inner_card_le μX μY
  have hJ : Fintype.card src.outer.Label ≤ J := by
    exact (chosenSources_outer_card_le μX μY).trans
      (codeSupportBound_mono D s (Nat.mul_le_mul_left q₂ hG))
  exact successor_carriers_card_le_closed src μI w Q G S J hG hS hJ

#print axioms codeSupportBound_mono
#print axioms column_card_eq
#print axioms successor_carriers_card_le_closed
#print axioms chosen_successor_carriers_card_le_explicit

end Sources
end CurrentAdditive.DeterministicIndexedMatrix
