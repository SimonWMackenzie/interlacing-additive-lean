import CurrentAdditive.V42IncomingWeightedSection

/-! v42 `res:incoming`: count heavy original diagonal fibers directly,
without selecting a dyadic density group. -/

namespace CurrentAdditive.V42IncomingHeavyFibres

open Paper2
open CurrentAdditive.DeterministicIndexedMatrix
open CurrentAdditive.DeterministicIndexedMatrix.Sources
open scoped BigOperators

theorem sum_le_heavy_card {B : Type*} [Fintype B]
    (f : B → ℝ) (t : ℝ) (ht : 0 ≤ t) (hf : ∀ b, f b ≤ 1) :
    ∑ b, f b ≤ ((Finset.univ.filter (fun b => t ≤ f b)).card : ℝ) +
      Fintype.card B * t := by
  classical
  calc
    ∑ b, f b ≤ ∑ b, ((if t ≤ f b then (1 : ℝ) else 0) + t) := by
      apply Finset.sum_le_sum
      intro b _
      by_cases h : t ≤ f b
      · simp only [h, ite_true]
        linarith [hf b]
      · simp only [h, ite_false, zero_add]
        exact (lt_of_not_ge h).le
    _ = _ := by simp [Finset.sum_add_distrib, ← Finset.sum_ite]

variable {I X Y : Type*} [Fintype I] [Fintype X] [Fintype Y]
  [DecidableEq I] [DecidableEq X] [DecidableEq Y]
  {q₁ q₂ s : ℕ} [NeZero s] [NeZero q₁] [NeZero q₂]
  {μX : PositiveRationalLaw X} {μY : PositiveRationalLaw Y}
  (src : Sources (D := 8192) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY)
  {μI : PositiveRationalLaw I} {w : ℕ}
  (streams : InternalStreams src μI w)

noncomputable def fibreMass (R : Set (Fin w × V38IndexedTwoTag.Column src))
    (i : Fin w) (α : Fin q₂) : ℝ :=
  src.gamma.law.toFiniteLaw.prob (fun γ => (i,Sum.inr (α,γ)) ∈ R)

theorem sum_fibreMass (R : Set (Fin w × V38IndexedTwoTag.Column src))
    (i : Fin w) :
    ∑ α, fibreMass src R i α = (q₂ : ℝ) *
      (diagonalLaw src).toFiniteLaw.prob (fun z => (i,Sum.inr z) ∈ R) := by
  classical
  rw [diagonalLaw, PositiveRationalLaw.toFiniteLaw_prod]
  rw [FiniteLaw.prod_prob _ _ (fun α γ => (i,Sum.inr (α,γ)) ∈ R)]
  simp only [fibreMass, PositiveRationalLaw.toFiniteLaw,
    PositiveRationalLaw.uniform, Fintype.card_fin, Rat.cast_inv,
    Rat.cast_natCast]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro α _
  have hq : (q₂ : ℝ) ≠ 0 := by exact_mod_cast (NeZero.ne q₂)
  field_simp

noncomputable def retainedFibreMass
    (R : Set (Fin w × V38IndexedTwoTag.Column src)) (I₀ : Finset (Fin w))
    (md : streams.metadataStream.Label) (z : Fin w × Fin q₂) : ℝ := by
  classical
  exact if z.1 ∈ I₀ ∧ isTemplateFlag (streams.metadataStream.decode md z.1)
    then fibreMass src R z.1 z.2 else 0

theorem sum_retainedFibreMass
    (R : Set (Fin w × V38IndexedTwoTag.Column src)) (I₀ : Finset (Fin w))
    (md : streams.metadataStream.Label) :
    ∑ z, retainedFibreMass src streams R I₀ md z =
      (q₂ : ℝ) * V42IncomingWeightedSection.templateMass src streams
        (V39IncomingDensity.density (diagonalLaw src).toFiniteLaw w R I₀) md := by
  classical
  rw [Fintype.sum_prod_type, V42IncomingWeightedSection.templateMass, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i ∈ I₀ <;>
    by_cases hflag : isTemplateFlag (streams.metadataStream.decode md i)
  · simp only [retainedFibreMass, hi, hflag, Bool.true_eq, and_self, ite_true,
      V39IncomingDensity.density,
      mul_one]
    exact sum_fibreMass src R i
  · simp [retainedFibreMass, hi, hflag, V39IncomingDensity.density]
  · simp [retainedFibreMass, hi, V39IncomingDensity.density]
  · simp [retainedFibreMass, hi, V39IncomingDensity.density]

/-- More than `2sκq₂` fibers have the exact source threshold
`2sκq₂*x`. We use the same elementary count as the manuscript; the loss
estimate here is weakened from `K₀/w` to `K₀`, still far below the margin. -/
theorem many_heavy_fibres
    (κ : ℕ) (x : ℝ) (R : Set (Fin w × V38IndexedTwoTag.Column src))
    (I₀ : Finset (Fin w)) (md : streams.metadataStream.Label)
    (hκ : 1 ≤ κ) (hw : 1 ≤ w) (hx : 0 < x)
    (hwidth : (w : ℝ)^2*q₂*x ≤ 1)
    (hlarge : 512*(s : ℝ)*κ ≤
      ∑ i, V39IncomingDensity.density (diagonalLaw src).toFiniteLaw w R I₀ i)
    (hweighted : (∑ i,
        V39IncomingDensity.density (diagonalLaw src).toFiniteLaw w R I₀ i)/2 ≤
      V42IncomingWeightedSection.templateMass src streams
        (V39IncomingDensity.density (diagonalLaw src).toFiniteLaw w R I₀) md) :
    2*s*κ*q₂ <
      (Finset.univ.filter (fun z : Fin w × Fin q₂ =>
        2*(s : ℝ)*κ*q₂*x ≤ retainedFibreMass src streams R I₀ md z)).card := by
  classical
  let f := retainedFibreMass src streams R I₀ md
  let t : ℝ := 2*(s : ℝ)*κ*q₂*x
  let H := Finset.univ.filter (fun z : Fin w × Fin q₂ => t ≤ f z)
  have hf : ∀ z, f z ≤ 1 := by
    intro z
    dsimp [f, retainedFibreMass]
    split_ifs
    · exact src.gamma.law.toFiniteLaw.prob_le_one _
    · norm_num
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hbound := sum_le_heavy_card f t ht hf
  have hsum := sum_retainedFibreMass src streams R I₀ md
  have hq : (1 : ℝ) ≤ q₂ := by exact_mod_cast (NeZero.pos q₂)
  have hs : (0 : ℝ) < s := by exact_mod_cast (NeZero.pos s)
  have hk : (0 : ℝ) < κ := by exact_mod_cast (by omega : 0 < κ)
  have hw' : (1 : ℝ) ≤ w := by exact_mod_cast hw
  have hwq : (w : ℝ)*q₂*x ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_right hw'
      (show 0 ≤ (w : ℝ)*q₂*x by positivity)
    nlinarith [hwidth]
  have hloss : (w : ℝ)*q₂*t ≤ 2*(s : ℝ)*κ*q₂ := by
    have hh := mul_le_mul_of_nonneg_left hwq
      (show 0 ≤ 2*(s : ℝ)*κ*q₂ by positivity)
    dsimp [t]
    nlinarith
  have htotal : 256*(s : ℝ)*κ*q₂ ≤ ∑ z, f z := by
    have hh := mul_le_mul_of_nonneg_left hweighted (show 0 ≤ (q₂ : ℝ) by positivity)
    have hl := mul_le_mul_of_nonneg_right hlarge (show 0 ≤ (q₂ : ℝ) by positivity)
    change ∑ z, f z = _ at hsum
    rw [hsum]
    nlinarith
  have hcount : (2*(s : ℝ)*κ*q₂) < H.card := by
    simp only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul] at hbound
    change ∑ z, f z ≤ (H.card : ℝ) + (w : ℝ)*q₂*t at hbound
    have hpos : 0 < (s : ℝ)*κ*q₂ := by positivity
    linarith
  change 2*s*κ*q₂ < H.card
  exact_mod_cast hcount

end CurrentAdditive.V42IncomingHeavyFibres

#print axioms CurrentAdditive.V42IncomingHeavyFibres.many_heavy_fibres
