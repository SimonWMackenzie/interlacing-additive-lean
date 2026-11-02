import Paper2.SourceItems
import Paper2.SourceProfileParameters

/-!
Scratch bridge from the literal v12 coordinate admissibility check to the
actual padded-and-repeated coordinate type. The factor is a computable quotient
of public widths, not an existentially selected repetition parameter.
-/

namespace Paper2.SourceRepetitionScratch

open Paper2.SourceItems Paper2.SourcePadding Paper2.SourceProfileParameters

/-- The original grouped coordinate count is `12*s*|E|`, before dyadic padding. -/
theorem sourceQ0_schedule (L : ℕ) (E : Type*) [Fintype E] :
    sourceQ0 (Fin (4 * width L)) E =
      powTwoCeil (12 * width L * Fintype.card E) := by
  have hc : Fintype.card (Coord (Fin (4 * width L)) E) =
      12 * width L * Fintype.card E := by
    rw [card_coord, Fintype.card_fin]
    ring
  simp only [sourceQ0, hc]

/-- Publicly computed repetition factor, determined by the actual source
coordinate count and the scheduled outer width. -/
def sourceRep (L : ℕ) (E : Type*) [Fintype E] : ℕ :=
  outerWidth L / sourceQ0 (Fin (4 * width L)) E

/-- The literal first admissibility inequality from v12 Appendix C. -/
def coordinateAdmissible (L : ℕ) (E : Type*) [Fintype E] : Prop :=
  powTwoCeil (12 * width L * Fintype.card E) ≤ outerWidth L

theorem sourceQ0_le_outerWidth (L : ℕ) (E : Type*) [Fintype E]
    (h : coordinateAdmissible L E) :
    sourceQ0 (Fin (4 * width L)) E ≤ outerWidth L := by
  rw [sourceQ0_schedule]
  exact h

theorem sourceQ0_dvd_outerWidth (L : ℕ) (E : Type*) [Fintype E]
    (h : coordinateAdmissible L E) :
    sourceQ0 (Fin (4 * width L)) E ∣ outerWidth L := by
  let n := 12 * width L * Fintype.card E
  have hn : n ≤ outerWidth L :=
    (le_powTwoCeil n).trans h
  have hexp : Nat.clog 2 n ≤ outerExponent L := by
    apply Nat.clog_le_of_le_pow
    simpa only [outerWidth] using hn
  rw [sourceQ0_schedule]
  change 2 ^ Nat.clog 2 n ∣ 2 ^ outerExponent L
  exact pow_dvd_pow 2 hexp

/-- Exact factorization for the public quotient, including empty edge types. -/
theorem outerWidth_eq_sourceQ0_mul_rep (L : ℕ) (E : Type*) [Fintype E]
    (h : coordinateAdmissible L E) :
    outerWidth L = sourceQ0 (Fin (4 * width L)) E * sourceRep L E := by
  unfold sourceRep
  exact (Nat.mul_div_cancel' (sourceQ0_dvd_outerWidth L E h)).symm

theorem sourceRep_pos (L : ℕ) (E : Type*) [Fintype E]
    (h : coordinateAdmissible L E) : 0 < sourceRep L E := by
  have hp : 0 < outerWidth L := by unfold outerWidth; positivity
  rw [outerWidth_eq_sourceQ0_mul_rep L E h] at hp
  by_contra hn
  have hz : sourceRep L E = 0 := by omega
  simp [hz] at hp

/-- The coordinate carrier used downstream has exactly the scheduled width. -/
theorem sourceCoord_schedule_card (L : ℕ) (E : Type*) [Fintype E]
    (h : coordinateAdmissible L E) :
    Fintype.card (SourceCoord (Fin (4 * width L)) E (sourceRep L E)) =
      outerWidth L := by
  rw [card_sourceCoord]
  exact (outerWidth_eq_sourceQ0_mul_rep L E h).symm

/-- The empty source has one padded coordinate and a public repetition factor
equal to the full outer width; it needs no nonempty-edge guard. -/
theorem sourceRep_empty (L : ℕ) : sourceRep L (Fin 0) = outerWidth L := by
  simp [sourceRep, sourceQ0_schedule, powTwoCeil]

theorem coordinateAdmissible_empty (L : ℕ) : coordinateAdmissible L (Fin 0) := by
  simp [coordinateAdmissible, powTwoCeil]
  unfold outerWidth
  have hp : 0 < 2 ^ outerExponent L := pow_pos (by decide) _
  omega

#print axioms sourceQ0_schedule
#print axioms sourceQ0_dvd_outerWidth
#print axioms outerWidth_eq_sourceQ0_mul_rep
#print axioms sourceRep_pos
#print axioms sourceCoord_schedule_card
#print axioms sourceRep_empty
#print axioms coordinateAdmissible_empty

end Paper2.SourceRepetitionScratch
