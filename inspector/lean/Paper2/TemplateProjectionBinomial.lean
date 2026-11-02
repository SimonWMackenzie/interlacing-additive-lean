import Paper2.TemplateProjectionTail
import Paper2.TemplateProjectionFibres

/-!
# The exact binomial distribution of alphabet-membership counts

Frozen v12 source: Appendix A, `cl:template-projection` (T41).
This file identifies the concrete uniform-word event used in the projection
theorem with the binomial formula. The distribution is derived by counting
actual pattern fibres, rather than assumed as a sampling contract.
-/

namespace Paper2.TemplateProjection

open scoped BigOperators

variable {Z : Type*} [Fintype Z] [DecidableEq Z]

/-- After prescribing all inside coordinates, every remaining coordinate
is independently chosen outside the distinguished alphabet. -/
noncomputable def otherWordSelfEquiv {u : ℕ} (T : Finset Z) (I : Finset (Fin u)) :
    OtherWord T I I ≃ ({i : Fin u // i ∉ I} → {z : Z // z ∉ T}) := by
  classical
  apply Equiv.piCongrRight
  intro i
  refine
    { toFun := fun z => ⟨z.val, fun hz => i.property (z.property.mp hz)⟩
      invFun := fun z => ⟨z.val, iff_of_false z.property i.property⟩
      left_inv := fun z => by cases z; rfl
      right_inv := fun z => by cases z; rfl }

/-- Exact cardinality of a prescribed membership-pattern fibre. -/
theorem card_patternWord_exact {u : ℕ} (T : Finset Z) (I : Finset (Fin u)) :
    Fintype.card (PatternWord T I) =
      T.card ^ I.card * (Fintype.card Z - T.card) ^ (u - I.card) := by
  classical
  rw [card_patternWord T I I (Finset.Subset.refl I),
    Fintype.card_congr (otherWordSelfEquiv T I), Fintype.card_fun]
  simp only [Fintype.card_subtype_compl, Fintype.card_coe, Fintype.card_fin]

/-- Count words having exactly `j` coordinates in the distinguished subset. -/
theorem coordinateCount_card (T : Finset Z) (u j : ℕ) :
    (Finset.univ.filter (fun w : Fin u → Z => coordinateCount T w = j)).card =
      Nat.choose u j * T.card ^ j * (Fintype.card Z - T.card) ^ (u - j) := by
  classical
  have hsplit := Finset.sum_card_fiberwise_eq_card_filter
    (Finset.univ : Finset (Fin u → Z))
    (Finset.univ.powersetCard j : Finset (Finset (Fin u))) (pattern T)
  have hleft :
      (∑ I ∈ (Finset.univ.powersetCard j : Finset (Finset (Fin u))),
        (Finset.univ.filter (fun w : Fin u → Z => pattern T w = I)).card) =
      Nat.choose u j * T.card ^ j * (Fintype.card Z - T.card) ^ (u - j) := by
    calc
      _ = ∑ I ∈ (Finset.univ.powersetCard j : Finset (Finset (Fin u))),
          T.card ^ j * (Fintype.card Z - T.card) ^ (u - j) := by
        apply Finset.sum_congr rfl
        intro I hI
        have hcard : I.card = j := (Finset.mem_powersetCard.mp hI).2
        rw [← Fintype.card_subtype, card_patternWord_exact T I, hcard]
      _ = _ := by simp [Finset.card_powersetCard, mul_assoc]
  rw [hleft] at hsplit
  simpa [Finset.mem_powersetCard, coordinateCount, pattern] using hsplit.symm

/-- The usual binomial point mass, including zero beyond the trial count. -/
noncomputable def binomialMass (u : ℕ) (p : ℝ) (j : ℕ) : ℝ :=
  (Nat.choose u j : ℝ) * p ^ j * (1 - p) ^ (u - j)

/-- The strict lower binomial tail. -/
noncomputable def binomialTail (u : ℕ) (p : ℝ) (k : ℕ) : ℝ :=
  ∑ j ∈ Finset.range k, binomialMass u p j

variable [Nonempty Z]

/-- The concrete coordinate count has the binomial point probabilities. -/
theorem coordinateCount_prob_eq_binomialMass (T : Finset Z) (u j : ℕ) :
    (wordLaw u).prob (fun w => coordinateCount T w = j) =
      binomialMass u (lambda T) j := by
  classical
  have hprob : (wordLaw u).prob (fun w => coordinateCount T w = j) =
      ((Finset.univ.filter (fun w : Fin u → Z => coordinateCount T w = j)).card : ℝ) /
        (Fintype.card Z : ℝ) ^ u := by
    simpa using wordLaw_prob_finset u
      (Finset.univ.filter (fun w : Fin u → Z => coordinateCount T w = j))
  rw [hprob, coordinateCount_card]
  by_cases hj : j ≤ u
  · have hz : (Fintype.card Z : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_pos.ne'
    have ht : T.card ≤ Fintype.card Z := Finset.card_le_univ T
    have he : (1 : ℝ) - lambda T =
        ((Fintype.card Z - T.card : ℕ) : ℝ) / Fintype.card Z := by
      unfold lambda
      rw [Nat.cast_sub ht]
      field_simp
    rw [binomialMass, he, lambda]
    push_cast
    rw [div_pow, div_pow]
    have hp : (Fintype.card Z : ℝ) ^ u =
        (Fintype.card Z : ℝ) ^ j * (Fintype.card Z : ℝ) ^ (u - j) := by
      rw [← pow_add, Nat.add_sub_of_le hj]
    rw [hp]
    field_simp
  · have hj' : u < j := by omega
    simp [Nat.choose_eq_zero_of_lt hj', binomialMass]

/-- The explicit bad-word probability is precisely the binomial lower tail. -/
theorem beta_eq_binomialTail (T : Finset Z) (u k : ℕ) :
    beta T u k = binomialTail u (lambda T) k := by
  classical
  have hsplit : beta T u k =
      ∑ j ∈ Finset.range k, (wordLaw u).prob (fun w => coordinateCount T w = j) := by
    unfold beta FiniteLaw.prob
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro w _
    by_cases hw : coordinateCount T w < k
    · rw [if_pos hw]
      symm
      exact Finset.sum_eq_single_of_mem (coordinateCount T w) (Finset.mem_range.mpr hw)
        (fun j _ hj => by simp [Ne.symm hj]) |>.trans (by simp)
    · rw [if_neg hw]
      symm
      apply Finset.sum_eq_zero
      intro j hj
      have hne : coordinateCount T w ≠ j := by
        intro he
        exact hw (he ▸ Finset.mem_range.mp hj)
      simp [hne]
  rw [hsplit, binomialTail]
  apply Finset.sum_congr rfl
  intro j _
  exact coordinateCount_prob_eq_binomialMass T u j

end Paper2.TemplateProjection

#print axioms Paper2.TemplateProjection.card_patternWord_exact
#print axioms Paper2.TemplateProjection.coordinateCount_prob_eq_binomialMass
#print axioms Paper2.TemplateProjection.beta_eq_binomialTail
