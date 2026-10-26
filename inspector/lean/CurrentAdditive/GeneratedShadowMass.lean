import CurrentAdditive.GeneratedMassExtraction

/-! Exact comparison of the old graph-item law with the actual indexed
source-row law. Every old template row is retained by the shadow. -/

namespace CurrentAdditive.DeterministicIndexedMatrix.Sources

open Paper2 Paper2.SourceMatrix

variable {G X Y : Type*} [Fintype G] [Nonempty G]
  [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
  {D q₁ q₂ s : ℕ} [NeZero s] [NeZero q₁] [NeZero q₂]
  {μX : PositiveRationalLaw X} {μY : PositiveRationalLaw Y}
  (src : Sources (D := D) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY)

private theorem uniform_prod_weight {A B : Type*} [Fintype A] [Fintype B]
    [Nonempty A] [Nonempty B] (a : A) (b : B) :
    (PositiveRationalLaw.uniform (A × B)).weight (a,b) =
      (PositiveRationalLaw.uniform A).weight a *
        (PositiveRationalLaw.uniform B).weight b := by
  simp [PositiveRationalLaw.uniform, Fintype.card_prod, mul_inv_rev]
  ring

private theorem source_vertex_weight
    [Nonempty (Fin (4*s))] [Nonempty (Fin (s-3))]
    (hs4 : 4 ≤ s)
    (g : Fin (4*s)) (v : G) (x : X) :
    (sourceRowLaw (μX := μX)
      (itemLaw (G := Fin (4*s)) (V := G) (A := Fin (s-3)))).weight
        ((g, Sum.inl v), x) =
      (1/2 : ℚ) *
        (Paper2.SourceLawBinding.vertexFamilyLaw (V := G) μX s hs4).weight
          ((g,v),x) := by
  letI : Nonempty (Fin (4*s)) := ⟨⟨0, by omega⟩⟩
  letI : Nonempty (Fin (s-3)) := ⟨⟨0, by omega⟩⟩
  simp only [sourceRowLaw, itemLaw, halfSumLaw,
    PositiveRationalLaw.prod, Paper2.SourceLawBinding.vertexFamilyLaw,
    Paper2.SourceLaws.itemRowLaw]
  rw [uniform_prod_weight g v]
  ring

private theorem source_aux_weight
    [Nonempty (Fin (4*s))] [Nonempty (Fin (s-3))]
    (hs4 : 4 ≤ s)
    (g : Fin (4*s)) (a : Fin (s-3)) (x : X) :
    (sourceRowLaw (μX := μX)
      (itemLaw (G := Fin (4*s)) (V := G) (A := Fin (s-3)))).weight
        ((g, Sum.inr a), x) =
      (1/2 : ℚ) *
        (Paper2.SourceLawBinding.auxiliaryFamilyLaw μX s hs4).weight
          ((g,a),x) := by
  letI : Nonempty (Fin (4*s)) := ⟨⟨0, by omega⟩⟩
  letI : Nonempty (Fin (s-3)) := ⟨⟨0, by omega⟩⟩
  simp only [sourceRowLaw, itemLaw, halfSumLaw,
    PositiveRationalLaw.prod, Paper2.SourceLawBinding.auxiliaryFamilyLaw,
    Paper2.SourceLaws.itemRowLaw]
  rw [uniform_prod_weight g a]
  ring

private theorem old_new_item_weight
    [Nonempty (Fin (4*s))] [Nonempty (Fin (s-3))]
    (hs4 : 4 ≤ s)
    (i : Paper2.SourceConstruction.Items s G) (x : X) :
    (Paper2.SourceLawBinding.matrixColumnLaw μX q₁ q₂ s hs4).weight
      (Sum.inr (i,x)) =
    (1/256 : ℚ) *
      (sourceRowLaw (μX := μX)
        (itemLaw (G := Fin (4*s)) (V := G) (A := Fin (s-3)))).weight
          (i,x) := by
  letI : Nonempty (Fin (4*s)) := ⟨⟨0, by omega⟩⟩
  letI : Nonempty (Fin (s-3)) := ⟨⟨0, by omega⟩⟩
  rcases i with ⟨g, v | a⟩
  · rw [source_vertex_weight hs4 g v x]
    simp [Paper2.SourceLawBinding.matrixColumnLaw,
      Paper2.PositiveRationalLaw.relabel,
      Paper2.SourceLawBinding.rawRowEquiv,
      Paper2.SourceLawBinding.itemEquiv,
      Paper2.SourceLaws.rowLaw,
      Paper2.SourceLawBinding.vertexFamilyLaw]
    ring
  · rw [source_aux_weight hs4 g a x]
    simp [Paper2.SourceLawBinding.matrixColumnLaw,
      Paper2.PositiveRationalLaw.relabel,
      Paper2.SourceLawBinding.rawRowEquiv,
      Paper2.SourceLawBinding.itemEquiv,
      Paper2.SourceLaws.rowLaw,
      Paper2.SourceLawBinding.auxiliaryFamilyLaw]
    ring

theorem raw_item_shadow_mass_eq
    [Nonempty (Fin (4*s))] [Nonempty (Fin (s-3))]
    (hs4 : 4 ≤ s)
    (V : Set (Row (I := Paper2.SourceConstruction.Items s G) src)) :
    (Paper2.SourceLawBinding.matrixColumnLaw μX q₁ q₂ s hs4).toFiniteLaw.prob
      (· ∈ rawItemShadow src V) =
      (255/256 : ℝ) + (1/256 : ℝ) *
      (sourceRowLaw (μX := μX)
        (itemLaw (G := Fin (4*s)) (V := G) (A := Fin (s-3)))).toFiniteLaw.prob
          (fun iu => Sum.inr iu ∈ V) := by
  classical
  let old := Paper2.SourceLawBinding.matrixColumnLaw (V := G) μX q₁ q₂ s hs4
  let new := sourceRowLaw (μX := μX)
    (itemLaw (G := Fin (4*s)) (V := G) (A := Fin (s-3)))
  have htpl : (∑ k : Fin s × Template q₁ q₂ X,
      (old.weight (Sum.inl k) : ℝ)) = 255/256 := by
    have h := (Paper2.SourceLawBinding.column_family_masses
      (V := G) (q₁ := q₁) (q₂ := q₂) μX hs4).1
    change old.toFiniteLaw.prob
      (fun k => Paper2.SourceLawBinding.columnFamilyIndex k = 0) = 255/256 at h
    simp only [Paper2.FiniteLaw.prob, Paper2.PositiveRationalLaw.toFiniteLaw,
      Fintype.sum_sum_type] at h
    have hzero : (∑ iu : Paper2.SourceConstruction.Items s G × X,
      if Paper2.SourceLawBinding.columnFamilyIndex
          (q₁ := q₁) (q₂ := q₂) (s := s) (Sum.inr iu) = 0 then
        (old.weight (Sum.inr iu) : ℝ) else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro iu _
      rcases iu with ⟨⟨g, v | a⟩, x⟩ <;>
        simp [Paper2.SourceLawBinding.columnFamilyIndex]
    rw [hzero] at h
    simp only [Paper2.SourceLawBinding.columnFamilyIndex, ↓reduceIte,
      add_zero] at h
    simpa using h
  change old.toFiniteLaw.prob (· ∈ rawItemShadow src V) =
    (255/256 : ℝ) + (1/256 : ℝ) *
      new.toFiniteLaw.prob (fun iu => Sum.inr iu ∈ V)
  simp only [Paper2.FiniteLaw.prob, Paper2.PositiveRationalLaw.toFiniteLaw,
    Fintype.sum_sum_type]
  have hinl (k : Fin s × Template q₁ q₂ X) :
      Sum.inl k ∈ rawItemShadow src V := trivial
  have hinr (iu : Paper2.SourceConstruction.Items s G × X) :
      Sum.inr iu ∈ rawItemShadow src V ↔ Sum.inr iu ∈ V := Iff.rfl
  simp only [hinl, hinr, ↓reduceIte]
  rw [htpl]
  rw [Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro iu _
  by_cases hv : Sum.inr iu ∈ V
  · simp only [hv, ↓reduceIte]
    rw [old_new_item_weight hs4 iu.1 iu.2]
    push_cast
    ring
  · simp [hv]

theorem raw_item_shadow_ge_row_retained
    [Nonempty (Fin (4*s))] [Nonempty (Fin (s-3))]
    (hs4 : 4 ≤ s)
    (V : Set (Row (I := Paper2.SourceConstruction.Items s G) src)) :
    (rowLaw src
      (itemLaw (G := Fin (4*s)) (V := G) (A := Fin (s-3)))).toFiniteLaw.prob
        (· ∈ V) ≤
    (Paper2.SourceLawBinding.matrixColumnLaw μX q₁ q₂ s hs4).toFiniteLaw.prob
      (· ∈ rawItemShadow src V) := by
  rw [row_prob_split, raw_item_shadow_mass_eq src hs4 V]
  have htpl := (templateRowLaw src).toFiniteLaw.prob_le_one
    (fun pz => Sum.inl pz ∈ V)
  linarith

theorem raw_item_shadow_retained_of_total {E : Type*} [Fintype E]
    [Nonempty (Fin (4*s))] [Nonempty (Fin (s-3))]
    (hs4 : 4 ≤ s) (γ : ℝ) (Δ : ℕ)
    (V : Set (Row (I := Paper2.SourceConstruction.Items s G) src))
    (η : ℝ)
    (hV : 1 - η ≤
      (rowLaw src
        (itemLaw (G := Fin (4*s)) (V := G) (A := Fin (s-3)))).toFiniteLaw.prob
          (· ∈ V))
    (hη : η ≤ Paper2.SourceSurvivingCollisions.deletionAllowance
      (V := G) (E := E) γ Δ s) :
    1 - Paper2.SourceSurvivingCollisions.deletionAllowance
      (V := G) (E := E) γ Δ s ≤
    (Paper2.SourceLawBinding.matrixColumnLaw μX q₁ q₂ s hs4).toFiniteLaw.prob
      (· ∈ rawItemShadow src V) := by
  exact (sub_le_sub_left hη 1).trans
    (hV.trans (raw_item_shadow_ge_row_retained src hs4 V))

end CurrentAdditive.DeterministicIndexedMatrix.Sources
