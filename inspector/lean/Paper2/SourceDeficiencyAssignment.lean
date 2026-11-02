import Paper2.SourceDeficiency

/-!
# A single branch assignment for the retained source items

Frozen v12 Section 4, `src:near-full`, immediately after the deficient-item
counts. Any total labelling of the actual retained raw rows by the common
prefix branches partitions each item's base-row mass. A nondeficient item
therefore has a branch retaining at least `1/(2s)` of that mass. The chosen
assignment is one function of the original retained rows and prefix labels;
it has no coordinate argument. The source-protocol prefix theorem supplies
the particular labelling used later, not a population-count hypothesis.
-/

namespace Paper2.SourceDeficiency

open scoped BigOperators
open SourceMatrix

variable {X B V : Type*} {q₁ q₂ s : ℕ}

/-- Actual fibres of a total finite labelling form a mass partition. -/
theorem prob_sum_label_fibres [Fintype X] [Fintype B]
    (μ : FiniteLaw X) (K : X → Prop) (label : X → B) :
    (∑ b, μ.prob (fun x => K x ∧ label x = b)) = μ.prob K := by
  classical
  unfold FiniteLaw.prob
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : K x <;> simp [hx]

/-- Half of an item's base mass cannot be split into `s` branches all
smaller than `1/(2s)`. This uses the actual fibre events, not chosen masses. -/
theorem exists_large_label_fibre [Fintype X] [NeZero s]
    (μ : FiniteLaw X) (K : X → Prop) (label : X → Fin s)
    (hK : 1 / 2 ≤ μ.prob K) :
    ∃ b, 1 / (2 * (s : ℝ)) ≤ μ.prob (fun x => K x ∧ label x = b) := by
  classical
  by_contra h
  push_neg at h
  have hs : (0 : ℝ) < s := Nat.cast_pos.mpr (NeZero.pos s)
  have hsum := Finset.sum_lt_sum_of_nonempty
    (Finset.univ_nonempty : (Finset.univ : Finset (Fin s)).Nonempty)
    (fun b _ => h b)
  rw [prob_sum_label_fibres] at hsum
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  have heq : (s : ℝ) * (1 / (2 * (s : ℝ))) = 1 / 2 := by field_simp
  rw [heq] at hsum
  linarith

/-- The branch mass is measured on the actual retained raw item rows. -/
noncomputable def itemBranchMass [Fintype X] (μ : PositiveRationalLaw X)
    (W : Set (RawRow q₁ q₂ s X (SourceConstruction.Items s V)))
    (rowCode : RawRow q₁ q₂ s X (SourceConstruction.Items s V) → Fin s)
    (i : SourceConstruction.Items s V) (b : Fin s) : ℝ :=
  μ.toFiniteLaw.prob (fun x => Sum.inr (i, x) ∈ W ∧ rowCode (Sum.inr (i, x)) = b)

theorem exists_itemBranch [Fintype X] [NeZero s] (μ : PositiveRationalLaw X)
    (W : Set (RawRow q₁ q₂ s X (SourceConstruction.Items s V)))
    (rowCode : RawRow q₁ q₂ s X (SourceConstruction.Items s V) → Fin s)
    (i : SourceConstruction.Items s V) (hi : itemKept μ W i) :
    ∃ b, 1 / (2 * (s : ℝ)) ≤ itemBranchMass μ W rowCode i b :=
  exists_large_label_fibre μ.toFiniteLaw (fun x => Sum.inr (i, x) ∈ W)
    (fun x => rowCode (Sum.inr (i, x))) hi

/-- The same item-to-branch function is used at every coordinate. Deficient
items are assigned an arbitrary default and are excluded by `itemKept`. -/
noncomputable def itemBranch [Fintype X] [NeZero s] (μ : PositiveRationalLaw X)
    (W : Set (RawRow q₁ q₂ s X (SourceConstruction.Items s V)))
    (rowCode : RawRow q₁ q₂ s X (SourceConstruction.Items s V) → Fin s)
    (i : SourceConstruction.Items s V) : Fin s := by
  classical
  exact if hi : itemKept μ W i then
    Classical.choose (exists_itemBranch μ W rowCode i hi) else ⟨0, NeZero.pos s⟩

theorem itemBranch_mass [Fintype X] [NeZero s] (μ : PositiveRationalLaw X)
    (W : Set (RawRow q₁ q₂ s X (SourceConstruction.Items s V)))
    (rowCode : RawRow q₁ q₂ s X (SourceConstruction.Items s V) → Fin s)
    (i : SourceConstruction.Items s V) (hi : itemKept μ W i) :
    1 / (2 * (s : ℝ)) ≤ itemBranchMass μ W rowCode i (itemBranch μ W rowCode i) := by
  classical
  simpa only [itemBranch, dif_pos hi] using
    Classical.choose_spec (exists_itemBranch μ W rowCode i hi)

theorem itemBranch_mass_ge_cap [Fintype X] [NeZero s] (μ : PositiveRationalLaw X)
    (W : Set (RawRow q₁ q₂ s X (SourceConstruction.Items s V)))
    (rowCode : RawRow q₁ q₂ s X (SourceConstruction.Items s V) → Fin s)
    (i : SourceConstruction.Items s V) (hi : itemKept μ W i)
    (xcap : ℝ) (hcap : xcap ≤ 1 / (2 * (s : ℝ))) :
    xcap ≤ itemBranchMass μ W rowCode i (itemBranch μ W rowCode i) :=
  hcap.trans (itemBranch_mass μ W rowCode i hi)

end Paper2.SourceDeficiency

#print axioms Paper2.SourceDeficiency.prob_sum_label_fibres
#print axioms Paper2.SourceDeficiency.exists_large_label_fibre
#print axioms Paper2.SourceDeficiency.itemBranch_mass
