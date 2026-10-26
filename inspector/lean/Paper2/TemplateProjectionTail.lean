import Paper2.ClassicalSeparation
import Paper2.ProductProjections

/-!
# Counting coordinates in a distinguished alphabet subset

Frozen v12 source: Appendix A, `cl:template-projection`, lines 608--676 (T41).
The word is sampled from the actual complete independent uniform product.
The tail event counts coordinates in a distinguished nonempty subset. Its
strict upper bound and first-moment estimate are proved directly from the
finite law; no tail estimate or independence conclusion is assumed.
-/

namespace Paper2.TemplateProjection

open scoped BigOperators

variable {Z : Type*} [Fintype Z] [DecidableEq Z] [Nonempty Z]

/-- Number of coordinates whose symbols belong to the distinguished subset. -/
def coordinateCount (T : Finset Z) {u : ℕ} (w : Fin u → Z) : ℕ :=
  (Finset.univ.filter (fun i => w i ∈ T)).card

/-- Number of coordinates outside the distinguished subset. -/
def missCount (T : Finset Z) {u : ℕ} (w : Fin u → Z) : ℕ :=
  (Finset.univ.filter (fun i => w i ∉ T)).card

/-- The distinguished subset's relative size in the alphabet. -/
noncomputable def lambda (T : Finset Z) : ℝ := (T.card : ℝ) / Fintype.card Z

/-- A word with independent uniformly distributed coordinates. -/
noncomputable def wordLaw (u : ℕ) : FiniteLaw (Fin u → Z) :=
  (FiniteLaw.uniform Z).iid u

/-- Probability that fewer than `k` coordinates belong to the subset. -/
noncomputable def beta (T : Finset Z) (u k : ℕ) : ℝ :=
  (wordLaw u).prob (fun w => coordinateCount T w < k)

theorem wordLaw_eq_uniform (u : ℕ) :
    wordLaw (Z := Z) u = FiniteLaw.uniform (Fin u → Z) := by
  cases h₁ : wordLaw (Z := Z) u with
  | mk w hw ht =>
    cases h₂ : FiniteLaw.uniform (Fin u → Z) with
    | mk v hv hs =>
      have hweight : w = v := by
        funext x
        have ha := congrArg (fun μ : FiniteLaw (Fin u → Z) => μ.weight x) h₁
        have hb := congrArg (fun μ : FiniteLaw (Fin u → Z) => μ.weight x) h₂
        simp [wordLaw, FiniteLaw.iid, FiniteLaw.uniform, Fintype.card_fun,
          Fintype.card_fin, ← inv_pow] at ha hb
        exact ha.symm.trans hb
      subst v
      rfl

theorem wordLaw_prob_finset (u : ℕ) (P : Finset (Fin u → Z)) :
    (wordLaw u).prob (fun w => w ∈ P) = (P.card : ℝ) / (Fintype.card Z : ℝ) ^ u := by
  rw [wordLaw_eq_uniform, FiniteLaw.uniform_prob_finset]
  simp

theorem lambda_nonneg (T : Finset Z) : 0 ≤ lambda T := by
  unfold lambda
  positivity

theorem lambda_le_one (T : Finset Z) : lambda T ≤ 1 := by
  rw [show lambda T = (FiniteLaw.uniform Z).prob (fun z => z ∈ T) from
    (FiniteLaw.uniform_prob_finset T).symm]
  exact FiniteLaw.prob_le_one _ _

theorem coordinateCount_add_missCount (T : Finset Z) {u : ℕ} (w : Fin u → Z) :
    coordinateCount T w + missCount T w = u := by
  simpa [coordinateCount, missCount] using
    Finset.card_filter_add_card_filter_not (s := Finset.univ) (fun i : Fin u => w i ∈ T)

theorem coordinateCount_const (T : Finset Z) {u : ℕ} {z : Z} (hz : z ∈ T) :
    coordinateCount T (fun _ : Fin u => z) = u := by
  simp [coordinateCount, hz]

theorem beta_nonneg (T : Finset Z) (u k : ℕ) : 0 ≤ beta T u k :=
  FiniteLaw.prob_nonneg _ _

theorem beta_le_one (T : Finset Z) (u k : ℕ) : beta T u k ≤ 1 :=
  FiniteLaw.prob_le_one _ _

private theorem prob_not (μ : FiniteLaw Z) (E : Z → Prop) :
    μ.prob (fun z => ¬ E z) = 1 - μ.prob E := by
  classical
  have hsum : μ.prob E + μ.prob (fun z => ¬ E z) = 1 := by
    unfold FiniteLaw.prob
    rw [← Finset.sum_add_distrib]
    calc
      _ = ∑ z, μ.weight z := by
        apply Finset.sum_congr rfl
        intro z _
        by_cases hz : E z <;> simp [hz]
      _ = 1 := μ.total
  linarith

theorem wordLaw_coordinate_prob (u : ℕ) (i : Fin u) (E : Z → Prop) :
    (wordLaw u).prob (fun w => E (w i)) = (FiniteLaw.uniform Z).prob E := by
  have he : Function.Injective (fun _ : Unit => i) := by
    intro a b _
    exact Subsingleton.elim a b
  have h := FiniteLaw.pi_prob_restrict (fun _ : Fin u => FiniteLaw.uniform Z)
    (fun _ : Unit => i) he (fun w => ∀ j : Unit, E (w j))
  have h' := FiniteLaw.pi_prob_coordinatewise (fun _ : Unit => FiniteLaw.uniform Z)
    (fun _ => E)
  rw [h'] at h
  simpa only [wordLaw, FiniteLaw.iid, FiniteLaw.pi, forall_const, Finset.prod_const,
    Finset.card_univ, Fintype.card_unit, pow_one] using h

theorem wordLaw_coordinate_miss (T : Finset Z) (u : ℕ) (i : Fin u) :
    (wordLaw u).prob (fun w => w i ∉ T) = 1 - lambda T := by
  rw [wordLaw_coordinate_prob u i (fun z => z ∉ T),
    prob_not (FiniteLaw.uniform Z) (fun z => z ∈ T), FiniteLaw.uniform_prob_finset]
  rfl

theorem missCount_cast (T : Finset Z) {u : ℕ} (w : Fin u → Z) :
    (missCount T w : ℝ) = ∑ i, if w i ∉ T then (1 : ℝ) else 0 := by
  rw [← Finset.sum_filter]
  simp [missCount]

/-- Exact first moment of the number of coordinates outside the subset. -/
theorem missCount_mean (T : Finset Z) (u : ℕ) :
    (∑ w, (wordLaw u).weight w * (missCount T w : ℝ)) =
      (u : ℝ) * (1 - lambda T) := by
  simp_rw [missCount_cast, Finset.mul_sum]
  rw [Finset.sum_comm]
  calc
    _ = ∑ i : Fin u, (wordLaw u).prob (fun w => w i ∉ T) := by
      apply Finset.sum_congr rfl
      intro i _
      unfold FiniteLaw.prob
      apply Finset.sum_congr rfl
      intro w _
      by_cases hw : w i ∈ T <;> simp [hw]
    _ = _ := by simp_rw [wordLaw_coordinate_miss]; simp; ring

/-- A nonempty subset supplies an all-inside word outside the bad event. -/
theorem beta_lt_one (T : Finset Z) (u k : ℕ) (hT : T.Nonempty) (hk : k ≤ u) :
    beta T u k < 1 := by
  classical
  obtain ⟨z, hz⟩ := hT
  let P : Finset (Fin u → Z) := Finset.univ.filter (fun w => coordinateCount T w < k)
  have hconst : (fun _ : Fin u => z) ∉ P := by
    simp [P, coordinateCount_const T hz, Nat.not_lt.mpr hk]
  have hproper : P ⊂ Finset.univ := by
    apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨Finset.subset_univ _, ?_⟩
    intro heq
    apply hconst
    rw [heq]
    exact Finset.mem_univ _
  have hcard := Finset.card_lt_card hproper
  have hb : beta T u k = (wordLaw u).prob (fun w => w ∈ P) := by
    unfold beta
    congr 1
    funext w
    simp [P]
  rw [hb, wordLaw_eq_uniform, FiniteLaw.uniform_prob_finset]
  apply (div_lt_one (by exact_mod_cast Fintype.card_pos)).mpr
  exact_mod_cast hcard

/-- Markov's bound, proved from the actual finite word distribution. -/
theorem beta_le_markov (T : Finset Z) (u k : ℕ) (hk : k ≤ u) :
    beta T u k ≤ (u : ℝ) * (1 - lambda T) / (u - k + 1 : ℕ) := by
  have hmoment : ((u - k + 1 : ℕ) : ℝ) * beta T u k ≤
      ∑ w, (wordLaw u).weight w * (missCount T w : ℝ) := by
    unfold beta FiniteLaw.prob
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro w _
    by_cases hw : coordinateCount T w < k
    · have hc := coordinateCount_add_missCount T w
      have hn : u - k + 1 ≤ missCount T w := by omega
      have hr : ((u - k + 1 : ℕ) : ℝ) ≤ missCount T w := by exact_mod_cast hn
      simpa only [hw, ↓reduceIte, mul_comm] using
        mul_le_mul_of_nonneg_left hr ((wordLaw u).nonneg w)
    · simp only [hw, ↓reduceIte, mul_zero]
      exact mul_nonneg ((wordLaw u).nonneg w) (Nat.cast_nonneg _)
  rw [missCount_mean] at hmoment
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < (u - k + 1 : ℕ))).mpr
  simpa only [mul_comm] using hmoment

/-- For twice as many coordinates as requested, the bad mass is at most
twice the relative size of the omitted alphabet. -/
theorem beta_two_mul_le (T : Finset Z) (k : ℕ) :
    beta T (2 * k) k ≤ 2 * (1 - lambda T) := by
  have h := beta_le_markov T (2 * k) k (by omega)
  apply h.trans
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < (2 * k - k + 1 : ℕ))).mpr
  have hn : 2 * k - k + 1 = k + 1 := by omega
  rw [hn]
  have hq : 0 ≤ 1 - lambda T := sub_nonneg.mpr (lambda_le_one T)
  push_cast
  nlinarith

end Paper2.TemplateProjection

#print axioms Paper2.TemplateProjection.beta_lt_one
#print axioms Paper2.TemplateProjection.missCount_mean
#print axioms Paper2.TemplateProjection.beta_le_markov
#print axioms Paper2.TemplateProjection.beta_two_mul_le
