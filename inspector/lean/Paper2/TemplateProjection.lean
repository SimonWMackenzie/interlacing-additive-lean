import Paper2.TemplateProjectionCounting
import Paper2.TemplateProjectionBinomial
import Paper2.TemplateProjectionRepresentatives

/-!
# Projection into a dense alphabet subset

Frozen v12, Appendix A, `cl:template-projection` (T41), lines 608--676.
The output is an actual coordinate subset and actual projected retained
words. The retained set may correlate all coordinates; only the complete
ambient product has independent uniform coordinates.
-/

namespace Paper2.TemplateProjection

open scoped BigOperators

variable {Z : Type*} [Fintype Z] [DecidableEq Z] [Nonempty Z]

noncomputable def retainedDensity {u : ℕ} (P : Finset (Fin u → Z)) : ℝ :=
  (P.card : ℝ) / (Fintype.card Z : ℝ) ^ u

theorem beta_eq_card (T : Finset Z) (u k : ℕ) :
    beta T u k = (badWords (ι := Fin u) T k).card / (Fintype.card Z : ℝ) ^ u := by
  have h := wordLaw_prob_finset u (badWords (ι := Fin u) T k)
  simpa only [beta, badWords, Finset.mem_filter, Finset.mem_univ, true_and,
    coordinateCount, pattern] using h

theorem retainedDensity_nonneg {u : ℕ} (P : Finset (Fin u → Z)) : 0 ≤ retainedDensity P := by
  unfold retainedDensity
  positivity

theorem retainedDensity_le_one {u : ℕ} (P : Finset (Fin u → Z)) : retainedDensity P ≤ 1 := by
  rw [show retainedDensity P = (wordLaw u).prob (fun w => w ∈ P) from
    (wordLaw_prob_finset u P).symm]
  exact FiniteLaw.prob_le_one _ _

/-- The sharp conditional-binomial-tail conclusion, with no evenness needed. -/
theorem exists_projection_sharp {u : ℕ} (P : Finset (Fin u → Z)) (T : Finset Z)
    (hT : T.Nonempty) (k : ℕ) (hk : k ≤ u) :
    ∃ J : Finset (Fin u), J.card = k ∧
      max 0 ((retainedDensity P - beta T u k) / (1 - beta T u k)) ≤ projectionDensity P T J := by
  obtain ⟨J, hJ, hnonneg, hcount⟩ := exists_maximizing_projection P T hT k (by simpa using hk)
  have hM : (0 : ℝ) < (Fintype.card Z : ℝ) ^ u :=
    pow_pos (Nat.cast_pos.mpr Fintype.card_pos) _
  have hρ : retainedDensity P ≤ beta T u k +
      (1 - beta T u k) * projectionDensity P T J := by
    rw [beta_eq_card]
    unfold retainedDensity
    apply (div_le_iff₀ hM).mpr
    have hc : (P.card : ℝ) ≤ (badWords (ι := Fin u) T k).card +
        ((Fintype.card Z : ℝ) ^ u - (badWords (ι := Fin u) T k).card) *
          projectionDensity P T J := by
      simpa only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow] using hcount
    have he : (((badWords (ι := Fin u) T k).card : ℝ) / (Fintype.card Z : ℝ) ^ u +
        (1 - (badWords (ι := Fin u) T k).card / (Fintype.card Z : ℝ) ^ u) *
          projectionDensity P T J) * (Fintype.card Z : ℝ) ^ u =
        (badWords (ι := Fin u) T k).card +
          ((Fintype.card Z : ℝ) ^ u - (badWords (ι := Fin u) T k).card) *
            projectionDensity P T J := by
      field_simp
    rw [he]
    exact hc
  have hb : 0 < 1 - beta T u k := sub_pos.mpr (beta_lt_one T u k hT hk)
  refine ⟨J, hJ, max_le hnonneg ((div_le_iff₀ hb).mpr ?_)⟩
  nlinarith

theorem sharp_bound_ge_difference (ρ β : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β < 1) :
    ρ - β ≤ max 0 ((ρ - β) / (1 - β)) := by
  by_cases h : ρ ≤ β
  · exact (sub_nonpos.mpr h).trans (le_max_left _ _)
  · have hp : 0 ≤ ρ - β := by linarith
    apply le_trans _ (le_max_right _ _)
    apply (le_div_iff₀ (by linarith : 0 < 1 - β)).mpr
    nlinarith

/-- The manuscript's full conclusion for `u=2k>=2`, including both inequalities
and the exact tail event of the independently uniform complete word. -/
theorem dense_alphabet_projection (k : ℕ) (hk : 1 ≤ k)
    (P : Finset (Fin (2 * k) → Z)) (T : Finset Z) (hT : T.Nonempty) :
    ∃ J : Finset (Fin (2 * k)), J.card = k ∧
      max 0 ((retainedDensity P - beta T (2 * k) k) / (1 - beta T (2 * k) k)) ≤
        projectionDensity P T J ∧
      retainedDensity P - 2 * (1 - lambda T) ≤
        max 0 ((retainedDensity P - beta T (2 * k) k) / (1 - beta T (2 * k) k)) := by
  obtain ⟨J, hJ, hbound⟩ := exists_projection_sharp P T hT k (by omega)
  refine ⟨J, hJ, hbound, ?_⟩
  have htail := beta_two_mul_le T k
  have hd := sharp_bound_ge_difference (retainedDensity P) (beta T (2 * k) k)
    (beta_nonneg T (2 * k) k) (beta_lt_one T (2 * k) k hT (by omega))
  linarith

theorem dense_alphabet_three_quarters (k : ℕ) (hk : 1 ≤ k)
    (P : Finset (Fin (2 * k) → Z)) (T : Finset Z) (hT : T.Nonempty)
    (hlambda : 1 - lambda T ≤ retainedDensity P / 8) :
    ∃ J : Finset (Fin (2 * k)), J.card = k ∧
      3 * retainedDensity P / 4 ≤ projectionDensity P T J := by
  obtain ⟨J, hJ, hsharp, hcoarse⟩ := dense_alphabet_projection k hk P T hT
  refine ⟨J, hJ, ?_⟩
  linarith

/-- The same theorem with the exceptional probability written as the explicit
binomial tail, matching the notation in the manuscript. -/
theorem dense_alphabet_projection_binomial (k : ℕ) (hk : 1 ≤ k)
    (P : Finset (Fin (2 * k) → Z)) (T : Finset Z) (hT : T.Nonempty) :
    ∃ J : Finset (Fin (2 * k)), J.card = k ∧
      max 0 ((retainedDensity P - binomialTail (2 * k) (lambda T) k) /
        (1 - binomialTail (2 * k) (lambda T) k)) ≤ projectionDensity P T J ∧
      retainedDensity P - 2 * (1 - lambda T) ≤
        max 0 ((retainedDensity P - binomialTail (2 * k) (lambda T) k) /
          (1 - binomialTail (2 * k) (lambda T) k)) := by
  simpa only [beta_eq_binomialTail] using dense_alphabet_projection k hk P T hT

end Paper2.TemplateProjection

#print axioms Paper2.TemplateProjection.exists_projection_sharp
#print axioms Paper2.TemplateProjection.dense_alphabet_projection
#print axioms Paper2.TemplateProjection.dense_alphabet_three_quarters
#print axioms Paper2.TemplateProjection.dense_alphabet_projection_binomial
