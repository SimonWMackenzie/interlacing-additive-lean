import CurrentAdditive.GeneratedDeficientCap
import CurrentAdditive.DeterministicIndexedProfileMass
import Paper2.SourceDeficiency

/-!
The actual generated diagonal-column deficit in v27 `det:near-full`.
The diagonal family has protected mass 1/256 in the original tagged law;
each of its coordinates retains an entire gamma *index* fibre.
-/

namespace CurrentAdditive.DeterministicIndexedMatrix.Sources

open Paper2 Paper2.SourceMatrix

variable {X Y I : Type*} [Fintype X] [Fintype Y] [Fintype I]
  [DecidableEq X] [DecidableEq Y]
  {D q₁ q₂ s : ℕ} [NeZero s] [NeZero q₁] [NeZero q₂]
  {μX : PositiveRationalLaw X} {μY : PositiveRationalLaw Y}
  (src : Sources (D := D) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY)

/-- Original tagged-column retention forces the original diagonal family
to retain at least `1-256η`; no conditioned product law is asserted. -/
theorem diagonal_retained (U : Set (Column src)) (η : ℝ)
    (hU : 1 - η ≤ (columnLaw src).toFiniteLaw.prob (· ∈ U)) :
    1 - 256 * η ≤ (diagonalLaw src).toFiniteLaw.prob
      (fun z => Column.diagonal z ∈ U) := by
  rw [column_prob_split] at hU
  have ho := (ordinaryLaw src).toFiniteLaw.prob_le_one
    (fun z => Column.ordinary z ∈ U)
  have hf := src.outer.law.toFiniteLaw.prob_le_one
    (fun z => Column.fixedTail z ∈ U)
  linarith

/-- A diagonal fibre is deficient when less than three quarters of its
original gamma-label mass survives in the actual retained column set. -/
noncomputable def diagonalBad (U : Set (Column src)) : Finset (Fin q₂) := by
  classical
  exact Finset.univ.filter fun α =>
    src.gamma.law.toFiniteLaw.prob
      (fun γ => Column.diagonal (α, γ) ∈ U) < 3 / 4

@[simp] theorem mem_diagonalBad (U : Set (Column src)) (α : Fin q₂) :
    α ∈ diagonalBad src U ↔
      src.gamma.law.toFiniteLaw.prob
        (fun γ => Column.diagonal (α, γ) ∈ U) < 3 / 4 := by
  classical
  simp [diagonalBad]

/-- The actual diagonal law is uniform over original coordinates and then
uses the independent original gamma-index law. -/
theorem diagonal_average (U : Set (Column src)) :
    (diagonalLaw src).toFiniteLaw.prob
      (fun z => Column.diagonal z ∈ U) =
      (q₂ : ℝ)⁻¹ * ∑ α : Fin q₂,
        src.gamma.law.toFiniteLaw.prob
          (fun γ => Column.diagonal (α, γ) ∈ U) := by
  rw [diagonalLaw, PositiveRationalLaw.toFiniteLaw_prod]
  change (((PositiveRationalLaw.uniform (Fin q₂)).toFiniteLaw.prod
      src.gamma.law.toFiniteLaw).prob
        (fun z => Column.diagonal (z.1, z.2) ∈ U)) = _
  have hprod := Paper2.FiniteLaw.prod_prob
    (PositiveRationalLaw.uniform (Fin q₂)).toFiniteLaw
    src.gamma.law.toFiniteLaw
    (fun α γ => Column.diagonal (α, γ) ∈ U)
  rw [hprod]
  simp only [PositiveRationalLaw.toFiniteLaw, PositiveRationalLaw.uniform,
    Fintype.card_fin, Rat.cast_inv, Rat.cast_natCast]
  rw [← Finset.mul_sum]

/-- Fewer than `1024ηq₂` diagonal coordinates have gamma-index retention
below three quarters. This is the exact source's `4ηq₂/μ` with μ=1/256. -/
theorem diagonalBad_card_lt (U : Set (Column src)) (η : ℝ)
    (hη : 0 < η)
    (hU : 1 - η ≤ (columnLaw src).toFiniteLaw.prob (· ∈ U)) :
    ((diagonalBad src U).card : ℝ) < 1024 * η * q₂ := by
  classical
  have havg := diagonal_retained src U η hU
  rw [diagonal_average] at havg
  have h := Paper2.SourceDeficiency.deficient_card_mul_lt
    (fun α : Fin q₂ => src.gamma.law.toFiniteLaw.prob
      (fun γ => Column.diagonal (α, γ) ∈ U))
    (3 / 4) (256 * η) (by positivity)
    (fun _ => src.gamma.law.toFiniteLaw.prob_le_one _)
    (by simpa only [Fintype.card_fin] using havg)
  change ((diagonalBad src U).card : ℝ) * (1 - 3 / 4) < _ at h
  simp only [Fintype.card_fin] at h
  nlinarith

end CurrentAdditive.DeterministicIndexedMatrix.Sources

#print axioms CurrentAdditive.DeterministicIndexedMatrix.Sources.diagonal_retained
#print axioms CurrentAdditive.DeterministicIndexedMatrix.Sources.diagonal_average
#print axioms CurrentAdditive.DeterministicIndexedMatrix.Sources.diagonalBad_card_lt
