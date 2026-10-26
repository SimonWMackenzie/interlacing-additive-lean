import Mathlib

/-!
An exact one-step rational support reduction for the finite-feature argument
in v27 Appendix H, `det:code`. This file treats an already supplied rational
affine dependence; finding it from the feature matrix is a separate task.
-/

namespace CurrentAdditive

open Finset

variable {ι κ : Type*}

/-- A nonzero zero-sum dependence on a finite set has coefficients of both signs. -/
theorem dependence_has_both_signs (s : Finset ι) (a : ι → ℚ)
    (hsum : ∑ i ∈ s, a i = 0)
    (hnonzero : ∃ i ∈ s, a i ≠ 0) :
    (∃ i ∈ s, 0 < a i) ∧ (∃ i ∈ s, a i < 0) := by
  constructor
  · exact exists_pos_of_sum_zero_of_exists_nonzero a hsum hnonzero
  · have hsum_neg : ∑ i ∈ s, -a i = 0 := by
      simp only [Finset.sum_neg_distrib, hsum, neg_zero]
    obtain ⟨i, hi, hpos⟩ :=
      exists_pos_of_sum_zero_of_exists_nonzero (fun i => -a i) hsum_neg
        ⟨hnonzero.choose, hnonzero.choose_spec.1,
          neg_ne_zero.mpr hnonzero.choose_spec.2⟩
    exact ⟨i, hi, by simpa using hpos⟩

/-- Eliminate at least one positive weight while preserving total mass and every
listed feature moment. All data and the output remain rational. -/
theorem rational_support_reduction_step
    (s : Finset ι) (w a : ι → ℚ) (φ : ι → κ → ℚ)
    (hw : ∀ i ∈ s, 0 < w i)
    (hsum : ∑ i ∈ s, a i = 0)
    (hmom : ∀ j : κ, ∑ i ∈ s, a i * φ i j = 0)
    (hnonzero : ∃ i ∈ s, a i ≠ 0) :
    ∃ (t : ℚ) (w' : ι → ℚ) (i₀ : ι),
      0 < t ∧ i₀ ∈ s ∧ w' i₀ = 0 ∧
      (∀ i ∈ s, 0 ≤ w' i) ∧
      (∀ i ∈ s, w' i = w i - t * a i) ∧
      (∀ i ∉ s, w' i = w i) ∧
      (∑ i ∈ s, w' i = ∑ i ∈ s, w i) ∧
      (∀ j : κ, ∑ i ∈ s, w' i * φ i j = ∑ i ∈ s, w i * φ i j) ∧
      (s.filter fun i => 0 < w' i).card < s.card := by
  classical
  obtain ⟨ipos, hipos, hapos⟩ := (dependence_has_both_signs s a hsum hnonzero).1
  let p : Finset ι := s.filter (fun i => 0 < a i)
  have hpne : p.Nonempty := ⟨ipos, mem_filter.mpr ⟨hipos, hapos⟩⟩
  obtain ⟨i₀, hi₀p, hmin⟩ := p.exists_min_image (fun i => w i / a i) hpne
  have hi₀ : i₀ ∈ s := (mem_filter.mp hi₀p).1
  have ha₀ : 0 < a i₀ := (mem_filter.mp hi₀p).2
  let t : ℚ := w i₀ / a i₀
  let w' : ι → ℚ := fun i => if i ∈ s then w i - t * a i else w i
  have ht : 0 < t := div_pos (hw i₀ hi₀) ha₀
  have hzero : w' i₀ = 0 := by
    simp [w', hi₀, t, div_mul_cancel₀ _ ha₀.ne']
  have hnonneg : ∀ i ∈ s, 0 ≤ w' i := by
    intro i hi
    simp only [w', hi, ↓reduceIte]
    by_cases hai : 0 < a i
    · have hip : i ∈ p := mem_filter.mpr ⟨hi, hai⟩
      have hratio : t ≤ w i / a i := hmin i hip
      have hmul : t * a i ≤ w i := by
        calc
          t * a i ≤ (w i / a i) * a i := mul_le_mul_of_nonneg_right hratio hai.le
          _ = w i := div_mul_cancel₀ _ hai.ne'
      exact sub_nonneg.mpr hmul
    · have ha_nonpos : a i ≤ 0 := le_of_not_gt hai
      have hprod : t * a i ≤ 0 := mul_nonpos_of_nonneg_of_nonpos ht.le ha_nonpos
      linarith [hw i hi]
  have hsum' : ∑ i ∈ s, w' i = ∑ i ∈ s, w i := by
    calc
      ∑ i ∈ s, w' i = ∑ i ∈ s, (w i - t * a i) := by
        apply Finset.sum_congr rfl
        intro i hi
        simp [w', hi]
      _ = ∑ i ∈ s, w i := by
        rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hsum, mul_zero, sub_zero]
  have hmom' (j : κ) :
      ∑ i ∈ s, w' i * φ i j = ∑ i ∈ s, w i * φ i j := by
    calc
      ∑ i ∈ s, w' i * φ i j =
          ∑ i ∈ s, (w i * φ i j - t * (a i * φ i j)) := by
            apply Finset.sum_congr rfl
            intro i hi
            simp only [w', hi, ↓reduceIte]
            ring
      _ = ∑ i ∈ s, w i * φ i j := by
        rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hmom j, mul_zero, sub_zero]
  have hstrict : (s.filter fun i => 0 < w' i).card < s.card := by
    apply Finset.card_lt_card
    refine (Finset.filter_ssubset.mpr ?_)
    exact ⟨i₀, hi₀, by simp [hzero]⟩
  exact ⟨t, w', i₀, ht, hi₀, hzero, hnonneg,
    (by intro i hi; simp [w', hi]),
    (by intro i hi; simp [w', hi]), hsum', hmom', hstrict⟩

/-- The same elimination step when exact matrix arithmetic gives integer
dependence coefficients, as in the manuscript's `0`-`1` feature matrix. -/
theorem integer_support_reduction_step
    (s : Finset ι) (w : ι → ℚ) (a : ι → ℤ) (φ : ι → κ → ℚ)
    (hw : ∀ i ∈ s, 0 < w i)
    (hsum : ∑ i ∈ s, a i = 0)
    (hmom : ∀ j : κ, ∑ i ∈ s, (a i : ℚ) * φ i j = 0)
    (hnonzero : ∃ i ∈ s, a i ≠ 0) :
    ∃ (t : ℚ) (w' : ι → ℚ) (i₀ : ι),
      0 < t ∧ i₀ ∈ s ∧ w' i₀ = 0 ∧
      (∀ i ∈ s, 0 ≤ w' i) ∧
      (∀ i ∈ s, w' i = w i - t * (a i : ℚ)) ∧
      (∀ i ∉ s, w' i = w i) ∧
      (∑ i ∈ s, w' i = ∑ i ∈ s, w i) ∧
      (∀ j : κ, ∑ i ∈ s, w' i * φ i j = ∑ i ∈ s, w i * φ i j) ∧
      (s.filter fun i => 0 < w' i).card < s.card := by
  have hsumQ : ∑ i ∈ s, (a i : ℚ) = 0 := by exact_mod_cast hsum
  have hnonzeroQ : ∃ i ∈ s, (a i : ℚ) ≠ 0 := by
    obtain ⟨i, hi, hai⟩ := hnonzero
    exact ⟨i, hi, by exact_mod_cast hai⟩
  exact rational_support_reduction_step s w (fun i => (a i : ℚ)) φ
    hw hsumQ hmom hnonzeroQ

#print axioms dependence_has_both_signs
#print axioms rational_support_reduction_step
#print axioms integer_support_reduction_step

end CurrentAdditive
