import Paper2.SourceLawBinding

/-!
# Protected-family retention in the actual source matrix

Frozen v12 Section 4, `src:near-full`, the estimates preceding the common
assignment and surviving-collision arguments. The ambient events below are
events on the actual rows and columns of `SourceConstruction.matrix`.
Their protected conditional masses follow from the concrete mixture laws;
they are not hypotheses about a separately supplied family distribution.
-/

namespace Paper2

namespace SourceProjectionRetention

open SourceMatrix SourceLawBinding

variable {V X Y : Type*} {q₁ q₂ s : ℕ}

/-- Complementation for the finite law, including arbitrary event predicates. -/
theorem probability_complement {A : Type*} [Fintype A] (μ : FiniteLaw A)
    (E : A → Prop) : μ.prob (fun a => ¬ E a) = 1 - μ.prob E := by
  classical
  have h : μ.prob (fun a => ¬ E a) + μ.prob E = 1 := by
    rw [FiniteLaw.prob, FiniteLaw.prob, ← Finset.sum_add_distrib]
    calc
      _ = ∑ a, μ.weight a := by
        apply Finset.sum_congr rfl
        intro a _
        by_cases ha : E a <;> simp [ha]
      _ = 1 := μ.total
  linarith

/-- A protected mass converts an ambient deletion bound to a conditional
deletion bound. Positivity is the only division hypothesis. -/
theorem retained_of_scaled_defect {w p η : ℝ} (hw : 0 < w)
    (h : w * (1 - p) ≤ η) : 1 - η / w ≤ p := by
  have hd : 1 - p ≤ η / w := (le_div_iff₀ hw).mpr (by nlinarith [h])
  linarith

section Rows

variable [Fintype Y] [NeZero q₂]

/-- Every tagged conditional row family survives a near-full restriction,
with the exact reciprocal of its protected mixture weight. -/
theorem row_families_retained (ν : PositiveRationalLaw Y)
    (A : TaggedColumn q₁ q₂ s Y → Prop) (η : ℝ)
    (hA : 1 - η ≤ (matrixRowLaw ν q₁ q₂ s).toFiniteLaw.prob A) :
    1 - η / (127 / 128 : ℝ) ≤
        (SourceLaws.rawLaw ν q₁ q₂ s).toFiniteLaw.prob
          (fun Z => A (.unrestricted Z)) ∧
    1 - 256 * η ≤
        (SourceLaws.fixedTailLaw ν q₁ q₂ s).toFiniteLaw.prob
          (fun js => A (.fixedTail js)) ∧
    1 - 256 * η ≤
        (SourceLaws.outerLaw ν q₁ q₂ s).toFiniteLaw.prob
          (fun j => A (.diagonal j)) := by
  have hu := (SourceLaws.rawLaw ν q₁ q₂ s).toFiniteLaw.prob_le_one
    (fun Z => A (.unrestricted Z))
  have hf := (SourceLaws.fixedTailLaw ν q₁ q₂ s).toFiniteLaw.prob_le_one
    (fun js => A (.fixedTail js))
  have hd := (SourceLaws.outerLaw ν q₁ q₂ s).toFiniteLaw.prob_le_one
    (fun j => A (.diagonal j))
  change 1 - η ≤ (SourceLaws.taggedLaw ν q₁ q₂ s).toFiniteLaw.prob A at hA
  rw [SourceLaws.tagged_prob] at hA
  refine ⟨?_, ?_, ?_⟩
  · apply retained_of_scaled_defect (by norm_num : (0 : ℝ) < 127 / 128)
    linarith
  · linarith
  · linarith

theorem unrestricted_rows_retained (ν : PositiveRationalLaw Y)
    (A : TaggedColumn q₁ q₂ s Y → Prop) (η : ℝ)
    (hA : 1 - η ≤ (matrixRowLaw ν q₁ q₂ s).toFiniteLaw.prob A) :
    1 - η / (127 / 128 : ℝ) ≤
      (SourceLaws.rawLaw ν q₁ q₂ s).toFiniteLaw.prob
        (fun Z => A (.unrestricted Z)) :=
  (row_families_retained ν A η hA).1

theorem fixed_tail_rows_retained (ν : PositiveRationalLaw Y)
    (A : TaggedColumn q₁ q₂ s Y → Prop) (η : ℝ)
    (hA : 1 - η ≤ (matrixRowLaw ν q₁ q₂ s).toFiniteLaw.prob A) :
    1 - 256 * η ≤ (SourceLaws.fixedTailLaw ν q₁ q₂ s).toFiniteLaw.prob
      (fun js => A (.fixedTail js)) :=
  (row_families_retained ν A η hA).2.1

theorem diagonal_rows_retained (ν : PositiveRationalLaw Y)
    (A : TaggedColumn q₁ q₂ s Y → Prop) (η : ℝ)
    (hA : 1 - η ≤ (matrixRowLaw ν q₁ q₂ s).toFiniteLaw.prob A) :
    1 - 256 * η ≤ (SourceLaws.outerLaw ν q₁ q₂ s).toFiniteLaw.prob
      (fun j => A (.diagonal j)) :=
  (row_families_retained ν A η hA).2.2

end Rows

section Columns

variable [Fintype V] [Nonempty V] [Fintype X] [NeZero q₁]

/-- The actual template, vertex, and auxiliary column families retain
the mass forced by their concrete weights in the source matrix law. -/
theorem column_families_retained (μ : PositiveRationalLaw X) (hs : 4 ≤ s)
    (K : RawRow q₁ q₂ s X (SourceConstruction.Items s V) → Prop) (η : ℝ)
    (hK : 1 - η ≤ (matrixColumnLaw μ q₁ q₂ s hs).toFiniteLaw.prob K) :
    1 - η / (255 / 256 : ℝ) ≤
        (templateFamilyLaw μ q₁ q₂ s hs).toFiniteLaw.prob (fun k => K (.inl k)) ∧
    1 - 512 * η ≤ (vertexFamilyLaw μ s hs).toFiniteLaw.prob
        (fun k => K (.inr ((k.1.1, .inl k.1.2), k.2))) ∧
    1 - 512 * η ≤ (auxiliaryFamilyLaw μ s hs).toFiniteLaw.prob
        (fun k => K (.inr ((k.1.1, .inr k.1.2), k.2))) := by
  have ht := (templateFamilyLaw μ q₁ q₂ s hs).toFiniteLaw.prob_le_one
    (fun k => K (.inl k))
  have hv := (vertexFamilyLaw μ s hs).toFiniteLaw.prob_le_one
    (fun k => K (.inr ((k.1.1, .inl k.1.2), k.2)))
  have ha := (auxiliaryFamilyLaw μ s hs).toFiniteLaw.prob_le_one
    (fun k => K (.inr ((k.1.1, .inr k.1.2), k.2)))
  rw [column_prob] at hK
  refine ⟨?_, ?_, ?_⟩
  · apply retained_of_scaled_defect (by norm_num : (0 : ℝ) < 255 / 256)
    linarith
  · linarith
  · linarith

theorem vertex_columns_retained (μ : PositiveRationalLaw X) (hs : 4 ≤ s)
    (K : RawRow q₁ q₂ s X (SourceConstruction.Items s V) → Prop) (η : ℝ)
    (hK : 1 - η ≤ (matrixColumnLaw μ q₁ q₂ s hs).toFiniteLaw.prob K) :
    1 - 512 * η ≤ (vertexFamilyLaw μ s hs).toFiniteLaw.prob
      (fun k => K (.inr ((k.1.1, .inl k.1.2), k.2))) :=
  (column_families_retained μ hs K η hK).2.1

theorem auxiliary_columns_retained (μ : PositiveRationalLaw X) (hs : 4 ≤ s)
    (K : RawRow q₁ q₂ s X (SourceConstruction.Items s V) → Prop) (η : ℝ)
    (hK : 1 - η ≤ (matrixColumnLaw μ q₁ q₂ s hs).toFiniteLaw.prob K) :
    1 - 512 * η ≤ (auxiliaryFamilyLaw μ s hs).toFiniteLaw.prob
      (fun k => K (.inr ((k.1.1, .inr k.1.2), k.2))) :=
  (column_families_retained μ hs K η hK).2.2

/-- Every individual template bin survives. This is a statement about
its entire template labels, not merely an average over bins. -/
theorem template_bin_retained (μ : PositiveRationalLaw X) (hs : 4 ≤ s)
    (K : RawRow q₁ q₂ s X (SourceConstruction.Items s V) → Prop) (η : ℝ)
    (hK : 1 - η ≤ (matrixColumnLaw μ q₁ q₂ s hs).toFiniteLaw.prob K)
    (p : Fin s) :
    1 - η * (s : ℝ) / (255 / 256 : ℝ) ≤
      (SourceLaws.templateLaw μ q₁ q₂).toFiniteLaw.prob (fun t => K (.inl (p, t))) := by
  let χ := (matrixColumnLaw (V := V) μ q₁ q₂ s hs).toFiniteLaw
  have hsub : χ.prob (templateBinEvent p (fun t => ¬ K (.inl (p, t)))) ≤
      χ.prob (fun k => ¬ K k) := by
    apply χ.prob_mono
    intro k hk
    rcases k with ⟨p', t⟩ | k
    · rcases hk with ⟨hpp, ht⟩
      dsimp only at hpp ht
      subst p'
      exact ht
    · exact False.elim hk
  have hdel : χ.prob (fun k => ¬ K k) ≤ η := by
    rw [probability_complement]
    change 1 - (matrixColumnLaw μ q₁ q₂ s hs).toFiniteLaw.prob K ≤ η
    linarith
  have hscaled := hsub.trans hdel
  change (matrixColumnLaw μ q₁ q₂ s hs).toFiniteLaw.prob
    (templateBinEvent p (fun t => ¬ K (.inl (p, t)))) ≤ η at hscaled
  rw [column_template_bin_law, probability_complement] at hscaled
  have hspos : (0 : ℝ) < s := by exact_mod_cast (show 0 < s by omega)
  have hmul := mul_le_mul_of_nonneg_right hscaled hspos.le
  have heq : (255 / 256 : ℝ) * (s : ℝ)⁻¹ *
      (1 - (SourceLaws.templateLaw μ q₁ q₂).toFiniteLaw.prob
        (fun t => K (.inl (p, t)))) * (s : ℝ) =
      (255 / 256 : ℝ) * (1 - (SourceLaws.templateLaw μ q₁ q₂).toFiniteLaw.prob
        (fun t => K (.inl (p, t)))) := by
    field_simp
  rw [heq] at hmul
  exact retained_of_scaled_defect (by norm_num) hmul

end Columns

end SourceProjectionRetention
end Paper2

#print axioms Paper2.SourceProjectionRetention.row_families_retained
#print axioms Paper2.SourceProjectionRetention.column_families_retained
#print axioms Paper2.SourceProjectionRetention.template_bin_retained
