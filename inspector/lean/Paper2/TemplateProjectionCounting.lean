import Paper2.TemplateProjectionFibres

/-!
# Averaging exact alphabet-membership fibres

Frozen v12 T41. The exceptional fibres have fewer than `k` distinguished
coordinates. Each other fibre factors over any chosen `k` of its distinguished
coordinates. Summing these exact fibre bounds proves the sharp projection
inequality before any estimate on the exceptional fraction is applied.
-/

namespace Paper2.TemplateProjection

open scoped BigOperators

variable {ι Z : Type*} [Fintype ι] [DecidableEq ι] [Fintype Z] [DecidableEq Z]

def badWords (T : Finset Z) (k : ℕ) : Finset (ι → Z) :=
  Finset.univ.filter (fun w => (pattern T w).card < k)

theorem card_patternWord_filter (T : Finset Z) (I : Finset ι) :
    Fintype.card (PatternWord T I) =
      (Finset.univ.filter (fun w : ι → Z => pattern T w = I)).card := by
  classical
  exact Fintype.card_subtype _

theorem sum_retained_fibres (P : Finset (ι → Z)) (T : Finset Z) :
    (∑ I : Finset ι, (P.filter (fun w => pattern T w = I)).card) = P.card := by
  classical
  symm
  exact Finset.card_eq_sum_card_fiberwise (t := Finset.univ) (by simp)

theorem sum_pattern_fibres (T : Finset Z) :
    (∑ I : Finset ι, Fintype.card (PatternWord T I)) = Fintype.card (ι → Z) := by
  simp_rw [card_patternWord_filter]
  simpa using sum_retained_fibres (Finset.univ : Finset (ι → Z)) T

theorem sum_bad_fibres (T : Finset Z) (k : ℕ) :
    (∑ I : Finset ι, if I.card < k then Fintype.card (PatternWord T I) else 0) =
      (badWords (ι := ι) T k).card := by
  classical
  simp_rw [card_patternWord_filter]
  rw [← Finset.sum_filter]
  rw [Finset.sum_card_fiberwise_eq_card_filter]
  congr 1
  ext w
  simp [badWords]

theorem projectionDensity_nonneg (P : Finset (ι → Z)) (T : Finset Z) (J : Finset ι) :
    0 ≤ projectionDensity P T J := by unfold projectionDensity; positivity

theorem projectionDensity_le_one (P : Finset (ι → Z)) (T : Finset Z)
    (hT : T.Nonempty) (J : Finset ι) : projectionDensity P T J ≤ 1 := by
  have hpos : (0 : ℝ) < (T.card : ℝ) ^ J.card := by
    exact pow_pos (Nat.cast_pos.mpr (Finset.card_pos.mpr hT)) _
  unfold projectionDensity
  apply (div_le_one hpos).mpr
  have hc := Finset.card_le_univ (projectionSet P T J)
  simp only [Fintype.card_fun, Fintype.card_coe] at hc
  exact_mod_cast hc

/-- Exact counting form of the conditional-pattern argument. The displayed
projection bounds are used only here; the next theorem obtains their common
bound by a finite maximum, not by assuming any density-transfer result. -/
theorem cardinal_bound (P : Finset (ι → Z)) (T : Finset Z) (hT : T.Nonempty)
    (k : ℕ) (α : ℝ)
    (hmax : ∀ J : Finset ι, J.card = k → projectionDensity P T J ≤ α) :
    (P.card : ℝ) ≤ (badWords (ι := ι) T k).card +
      ((Fintype.card (ι → Z) : ℝ) - (badWords (ι := ι) T k).card) * α := by
  classical
  let C (I : Finset ι) : ℝ := Fintype.card (PatternWord T I)
  have hlocal (I : Finset ι) : ((P.filter (fun w => pattern T w = I)).card : ℝ) ≤
      (if I.card < k then C I else 0) + (if I.card < k then 0 else C I) * α := by
    by_cases hi : I.card < k
    · simp only [hi, ↓reduceIte, zero_mul, add_zero]
      have hc : (P.filter (fun w => pattern T w = I)).card ≤
          Fintype.card (PatternWord T I) := by
        rw [card_patternWord_filter]
        exact Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_univ _))
      dsimp only [C]
      exact_mod_cast hc
    · simp only [hi, ↓reduceIte, zero_add]
      obtain ⟨J, hJI, hJ⟩ := Finset.exists_subset_card_eq (show k ≤ I.card by omega)
      have hm := mul_le_mul_of_nonneg_right (hmax J hJ)
        (Nat.cast_nonneg (Fintype.card (PatternWord T I)) : (0 : ℝ) ≤ _)
      exact (retained_fibre_density_le P T hT I J hJI).trans (by simpa [C, mul_comm] using hm)
  have hsum := Finset.sum_le_sum (fun I (_ : I ∈ (Finset.univ : Finset (Finset ι))) => hlocal I)
  have hsP : (∑ I : Finset ι, ((P.filter (fun w => pattern T w = I)).card : ℝ)) = P.card := by
    exact_mod_cast sum_retained_fibres P T
  have hsBad : (∑ I : Finset ι, if I.card < k then C I else 0) =
      (badWords (ι := ι) T k).card := by
    have h := congrArg (fun n : ℕ => (n : ℝ)) (sum_bad_fibres (ι := ι) T k)
    push_cast at h
    exact h
  have hsAll : (∑ I : Finset ι, C I) = Fintype.card (ι → Z) := by
    dsimp only [C]
    exact_mod_cast sum_pattern_fibres (ι := ι) T
  have hsGood : (∑ I : Finset ι, if I.card < k then 0 else C I) =
      (Fintype.card (ι → Z) : ℝ) - (badWords (ι := ι) T k).card := by
    have hadd : (∑ I : Finset ι, if I.card < k then C I else 0) +
        (∑ I : Finset ι, if I.card < k then 0 else C I) = ∑ I : Finset ι, C I := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro I _
      split_ifs <;> simp
    rw [hsBad, hsAll] at hadd
    linarith
  rw [hsP, Finset.sum_add_distrib, ← Finset.sum_mul, hsBad, hsGood] at hsum
  exact hsum

/-- A maximizing projection exists, and its density bounds the retained
ambient mass after the exact exceptional-pattern mass is removed. -/
theorem exists_maximizing_projection (P : Finset (ι → Z)) (T : Finset Z) (hT : T.Nonempty)
    (k : ℕ) (hk : k ≤ Fintype.card ι) :
    ∃ J : Finset ι, J.card = k ∧ 0 ≤ projectionDensity P T J ∧
      (P.card : ℝ) ≤ (badWords (ι := ι) T k).card +
        ((Fintype.card (ι → Z) : ℝ) - (badWords (ι := ι) T k).card) * projectionDensity P T J := by
  classical
  let S := (Finset.univ : Finset (Finset ι)).filter (fun J => J.card = k)
  have hS : S.Nonempty := by
    obtain ⟨J, _, hJ⟩ := Finset.exists_subset_card_eq
      (show k ≤ (Finset.univ : Finset ι).card by simpa using hk)
    exact ⟨J, by simp [S, hJ]⟩
  obtain ⟨J, hJ, hmax⟩ := Finset.exists_max_image S (projectionDensity P T) hS
  have hc : J.card = k := (Finset.mem_filter.mp hJ).2
  refine ⟨J, hc, projectionDensity_nonneg P T J,
    cardinal_bound P T hT k (projectionDensity P T J) ?_⟩
  intro J' hJ'
  exact hmax J' (by simp [S, hJ'])

end Paper2.TemplateProjection
