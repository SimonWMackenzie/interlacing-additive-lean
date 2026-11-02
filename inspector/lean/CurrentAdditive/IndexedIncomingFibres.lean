import CurrentAdditive.IndexedIncomingImageFixed

/-! Appendix I `det:incoming`: heavy inner fibres of the literal `J₂`
product law.  The labels in this file are the original indexed gamma labels. -/

namespace CurrentAdditive.DeterministicIndexedMatrix.Sources

open Paper2
open scoped BigOperators

variable {X Y : Type*} [Fintype X] [Fintype Y]
  [DecidableEq X] [DecidableEq Y]
  {D q₁ q₂ s : ℕ} [NeZero s] [NeZero q₁] [NeZero q₂]
  {μX : PositiveRationalLaw X} {μY : PositiveRationalLaw Y}
  (src : Sources (D := D) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY)

/-- The actual gamma-index fibre of a protected image. -/
noncomputable def protectedFibre (w : ℕ) (R : Set (Fin w × Column src))
    (b : Bool) (i : Fin w) (p : Fin s) (α : Fin q₂) : Set src.gamma.Label :=
  fun γ => (α, γ) ∈ protectedImage src w R b i p

/-- Its heavy bins use the manuscript's inclusive `δ/4` threshold. -/
noncomputable def heavyProtectedBins (w : ℕ) (R : Set (Fin w × Column src))
    (b : Bool) (i : Fin w) (p : Fin s) (δ : ℝ) : Finset (Fin q₂) := by
  classical
  exact Finset.univ.filter (fun α => δ / 4 ≤
    src.gamma.law.toFiniteLaw.prob (fun γ => γ ∈ protectedFibre src w R b i p α))

theorem mem_heavyProtectedBins (w : ℕ) (R : Set (Fin w × Column src))
    (b : Bool) (i : Fin w) (p : Fin s) (δ : ℝ) (α : Fin q₂) :
    α ∈ heavyProtectedBins src w R b i p δ ↔
      δ / 4 ≤ src.gamma.law.toFiniteLaw.prob
        (fun γ => γ ∈ protectedFibre src w R b i p α) := by
  simp [heavyProtectedBins]

private theorem fibre_mass_le_heavy_card
    {q : ℕ} [NeZero q] {G : Type*} [Fintype G]
    (ν : FiniteLaw G) (E : Set (Fin q × G)) (δ : ℝ) (hδ : 0 ≤ δ) :
    let V := Finset.univ.filter (fun α : Fin q =>
      δ / 4 ≤ ν.prob (fun γ => (α, γ) ∈ E))
    ((PositiveRationalLaw.uniform (Fin q)).toFiniteLaw.prod ν).prob (· ∈ E) ≤
      (V.card : ℝ) / q + δ / 4 := by
  classical
  let μ := (PositiveRationalLaw.uniform (Fin q)).toFiniteLaw
  let V : Finset (Fin q) := Finset.univ.filter (fun α : Fin q =>
    δ / 4 ≤ ν.prob (fun γ => (α, γ) ∈ E))
  have hpoint (α : Fin q) :
      ν.prob (fun γ => (α, γ) ∈ E) ≤
        (if α ∈ V then (1 : ℝ) else 0) + δ / 4 := by
    by_cases ha : α ∈ V
    · simp only [ha, ite_true]
      linarith [ν.prob_le_one (fun γ => (α, γ) ∈ E)]
    · have hn : ¬ δ / 4 ≤ ν.prob (fun γ => (α, γ) ∈ E) := by
        simpa [V] using ha
      simp only [ha, ite_false, zero_add]
      exact le_of_lt (lt_of_not_ge hn)
  have hsum : (μ.prod ν).prob (· ∈ E) ≤
      μ.prob (· ∈ V) + δ / 4 := by
    have hprod : (μ.prod ν).prob (· ∈ E) =
        ∑ α : Fin q, μ.weight α * ν.prob (fun γ => (α, γ) ∈ E) := by
      simpa using (FiniteLaw.prod_prob μ ν (fun α γ => (α, γ) ∈ E))
    rw [hprod]
    have hprobV : μ.prob (· ∈ V) =
        ∑ α : Fin q, if α ∈ V then μ.weight α else 0 := by
      unfold FiniteLaw.prob
      congr 1
      funext α
      by_cases ha : α ∈ V <;> simp [ha]
    rw [hprobV]
    have hle : (∑ α : Fin q, μ.weight α * ν.prob (fun γ => (α, γ) ∈ E)) ≤
        ∑ α : Fin q, μ.weight α *
          ((if α ∈ V then (1 : ℝ) else 0) + δ / 4) := by
      apply Finset.sum_le_sum
      intro α _
      exact mul_le_mul_of_nonneg_left (hpoint α) (μ.nonneg α)
    have hright : (∑ α : Fin q, μ.weight α *
          ((if α ∈ V then (1 : ℝ) else 0) + δ / 4)) =
        (∑ α : Fin q, if α ∈ V then μ.weight α else 0) + δ / 4 := by
      simp only [mul_add, Finset.sum_add_distrib, mul_ite, mul_one, mul_zero]
      rw [← Finset.sum_mul, μ.total, one_mul]
    rw [hright] at hle
    exact hle
  have hcard : μ.prob (· ∈ V) = (V.card : ℝ) / q := by
    change (PositiveRationalLaw.uniform (Fin q)).toFiniteLaw.prob (· ∈ V) = _
    simp [FiniteLaw.prob, PositiveRationalLaw.toFiniteLaw,
      PositiveRationalLaw.uniform, ← Finset.sum_filter]
    ring
  exact hsum.trans_eq (by rw [hcard])

/-- A set of product mass greater than `δ/2` has more than `δ q/4`
distinct inner bins whose gamma-index fibres each have mass at least
`δ/4`. -/
theorem heavy_fibre_card_gt
    {q : ℕ} [NeZero q] {G : Type*} [Fintype G]
    (ν : FiniteLaw G) (E : Set (Fin q × G)) (δ : ℝ)
    (hδ : 0 ≤ δ)
    (himage : δ / 2 <
      ((PositiveRationalLaw.uniform (Fin q)).toFiniteLaw.prod ν).prob (· ∈ E)) :
    δ * q / 4 <
      ((Finset.univ.filter (fun α : Fin q =>
        δ / 4 ≤ ν.prob (fun γ => (α, γ) ∈ E))).card : ℝ) := by
  classical
  have hbound := fibre_mass_le_heavy_card ν E δ hδ
  dsimp at hbound
  have hq : (0 : ℝ) < q := Nat.cast_pos.mpr (NeZero.pos q)
  have htmp : δ / 4 <
      ((Finset.univ.filter (fun α : Fin q =>
        δ / 4 ≤ ν.prob (fun γ => (α, γ) ∈ E))).card : ℝ) / q := by
    linarith
  have hmul := (lt_div_iff₀ hq).1 htmp
  nlinarith

/-- The protected image is the literal `Fin q₂ × gamma.Label` law, so its
heavy fibres count original selector addresses rather than decoded words. -/
theorem protected_heavy_fibres (w : ℕ)
    (R : Set (Fin w × Column src)) (b : Bool) (i : Fin w)
    (p : Fin s) (δ : ℝ) (hδ : 0 ≤ δ)
    (himage : δ / 2 < (diagonalLaw src).toFiniteLaw.prob
      (fun j => j ∈ protectedImage src w R b i p)) :
    δ * q₂ / 4 < (heavyProtectedBins src w R b i p δ).card := by
  classical
  have h := heavy_fibre_card_gt src.gamma.law.toFiniteLaw
    (protectedImage src w R b i p) δ hδ
  have himage' : δ / 2 <
      ((PositiveRationalLaw.uniform (Fin q₂)).toFiniteLaw.prod
        src.gamma.law.toFiniteLaw).prob
          (fun j => j ∈ protectedImage src w R b i p) := by
    simpa [diagonalLaw, PositiveRationalLaw.toFiniteLaw_prod] using himage
  have h' := h himage'
  simpa [heavyProtectedBins, protectedFibre] using h'

#print axioms heavy_fibre_card_gt
#print axioms protected_heavy_fibres

end CurrentAdditive.DeterministicIndexedMatrix.Sources
