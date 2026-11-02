import Paper2.ProtectedIncomingColumns
import Paper2.SourceLawBinding
import Paper2.ProductProjections
import Paper2.RationalSeparation

/-!
# Exact template-copy law and joint selector mass

Isolated implementation scratch for frozen v12 `res:incoming`. This file is
not part of the published Paper2 module inventory during the checkpoint.
-/

namespace Paper2.ProtectedIncomingTemplateLaw

open ProtectedIncomingColumns SourceMatrix SourceLawBinding

noncomputable def uniformSubtypeLaw {Z : Type*} [Fintype Z] [DecidableEq Z]
    (T : Finset Z) (hT : T.Nonempty) : FiniteLaw T := by
  letI : Nonempty T := ⟨⟨hT.choose, hT.choose_spec⟩⟩
  exact FiniteLaw.uniform T

/-- Normalizing the uniform law on a nonempty finite subset is exact on
every event, including predicates depending on subtype evidence. -/
theorem uniform_subtype_prob_mul {Z : Type*} [Fintype Z] [DecidableEq Z]
    [Nonempty Z] (T : Finset Z) (hT : T.Nonempty) (E : T → Prop) :
    (uniformSubtypeLaw T hT).prob E * (FiniteLaw.uniform Z).prob (· ∈ T) =
      (FiniteLaw.uniform Z).prob
        (fun z => ∃ hz : z ∈ T, E ⟨z, hz⟩) := by
  classical
  letI : Nonempty T := ⟨⟨hT.choose, hT.choose_spec⟩⟩
  let S : Finset T := Finset.univ.filter E
  let A : Finset Z := Finset.univ.filter (fun z => ∃ hz : z ∈ T, E ⟨z, hz⟩)
  have himage : S.image Subtype.val = A := by
    ext z
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
      true_and, S, A]
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ⟨t.property, ht⟩
    · rintro ⟨hz, hE⟩
      exact ⟨⟨z, hz⟩, hE, rfl⟩
  have hcard : S.card = A.card := by
    rw [← himage]
    exact (Finset.card_image_of_injective S Subtype.val_injective).symm
  have hTpos : (0 : ℝ) < T.card := by
    exact_mod_cast Finset.card_pos.mpr hT
  have hZpos : (0 : ℝ) < Fintype.card Z := by
    exact_mod_cast Fintype.card_pos
  change (FiniteLaw.uniform T).prob E *
      (FiniteLaw.uniform Z).prob (fun z => z ∈ T) =
      (FiniteLaw.uniform Z).prob (fun z => ∃ hz : z ∈ T, E ⟨z, hz⟩)
  have hSE : (fun t : T => t ∈ S) = E := by funext t; simp [S]
  have hAE : (fun z : Z => z ∈ A) =
      (fun z => ∃ hz : z ∈ T, E ⟨z, hz⟩) := by funext z; simp [A]
  rw [← hAE, ← hSE]
  rw [FiniteLaw.uniform_prob_finset, FiniteLaw.uniform_prob_finset,
    FiniteLaw.uniform_prob_finset]
  rw [← hcard]
  field_simp
  simp

variable {V X : Type*} [Fintype V] [Nonempty V] [Fintype X]
  {q₁ q₂ s : ℕ} [NeZero q₁]

private abbrev Column (V X : Type*) (q₁ q₂ s : ℕ) :=
  RawRow q₁ q₂ s X (SourceConstruction.Items s V)

noncomputable def sourceTemplateCopies (μ : PositiveRationalLaw X) (hs : 4 ≤ s) :
    Finset (SourceLawBinding.matrixColumnLaw (V := V) μ q₁ q₂ s hs).Copies :=
  copyFamily (SourceLawBinding.matrixColumnLaw (V := V) μ q₁ q₂ s hs)
    (fun a => columnFamilyIndex a = 0)

theorem sourceTemplateCopies_nonempty (μ : PositiveRationalLaw X) (hs : 4 ≤ s) :
    (sourceTemplateCopies (V := V) (q₁ := q₁) (q₂ := q₂) μ hs).Nonempty := by
  classical
  let χ := SourceLawBinding.matrixColumnLaw (V := V) μ q₁ q₂ s hs
  letI : Nonempty X := μ.nonempty
  letI : Nonempty (Fin q₁) := ⟨⟨0, NeZero.pos q₁⟩⟩
  letI : Nonempty (Fin s) := ⟨⟨0, by omega⟩⟩
  let a : Column V X q₁ q₂ s := .inl (Classical.choice inferInstance,
    fun _ => (Classical.choice inferInstance, Classical.choice inferInstance))
  obtain ⟨z, hz⟩ := χ.forget_surjective a
  refine ⟨z, ?_⟩
  simp only [sourceTemplateCopies, copyFamily, Finset.mem_filter,
    Finset.mem_univ, true_and]
  rw [hz]
  rfl

private theorem sourceTemplateCopies_inl (μ : PositiveRationalLaw X) (hs : 4 ≤ s)
    (t : sourceTemplateCopies (V := V) (q₁ := q₁) (q₂ := q₂) μ hs) :
    ∃ a : Fin s × Template q₁ q₂ X,
      (SourceLawBinding.matrixColumnLaw (V := V) μ q₁ q₂ s hs).forget t.val = .inl a := by
  have ht : columnFamilyIndex
      ((SourceLawBinding.matrixColumnLaw (V := V) μ q₁ q₂ s hs).forget t.val) = 0 := by
    simpa [sourceTemplateCopies, copyFamily] using t.property
  cases h : (SourceLawBinding.matrixColumnLaw (V := V) μ q₁ q₂ s hs).forget t.val with
  | inl a => exact ⟨a, rfl⟩
  | inr a =>
      rcases a with ⟨⟨g, v | a⟩, x⟩ <;>
        simp [columnFamilyIndex, h] at ht

noncomputable def templateCopyDecode (μ : PositiveRationalLaw X) (hs : 4 ≤ s)
    (t : sourceTemplateCopies (V := V) (q₁ := q₁) (q₂ := q₂) μ hs) :
    Fin s × Template q₁ q₂ X :=
  Classical.choose (sourceTemplateCopies_inl μ hs t)

theorem templateCopyDecode_spec (μ : PositiveRationalLaw X) (hs : 4 ≤ s)
    (t : sourceTemplateCopies (V := V) (q₁ := q₁) (q₂ := q₂) μ hs) :
    (SourceLawBinding.matrixColumnLaw (V := V) μ q₁ q₂ s hs).forget t.val =
      .inl (templateCopyDecode μ hs t) :=
  Classical.choose_spec (sourceTemplateCopies_inl μ hs t)

private theorem source_template_event_prob (μ : PositiveRationalLaw X) (hs : 4 ≤ s)
    (F : (Fin s × Template q₁ q₂ X) → Prop) :
    (SourceLawBinding.matrixColumnLaw (V := V) μ q₁ q₂ s hs).toFiniteLaw.prob
      (fun a => match a with | .inl b => F b | .inr _ => False) =
      (255 / 256 : ℝ) *
        (SourceLawBinding.templateFamilyLaw μ q₁ q₂ s hs).toFiniteLaw.prob F := by
  rw [SourceLawBinding.column_prob]
  simp

noncomputable def sourceTemplateCopyLaw (μ : PositiveRationalLaw X) (hs : 4 ≤ s) :
    FiniteLaw (sourceTemplateCopies (V := V) (q₁ := q₁) (q₂ := q₂) μ hs) := by
  classical
  exact uniformSubtypeLaw _ (sourceTemplateCopies_nonempty μ hs)

/-- Uniform duplicate labels restricted to the actual template family
push forward to the literal source template-family law on every event. -/
theorem template_copy_pushes (μ : PositiveRationalLaw X) (hs : 4 ≤ s) :
    (sourceTemplateCopyLaw (V := V) (q₁ := q₁) (q₂ := q₂) μ hs).PushesTo
      (templateFamilyLaw μ q₁ q₂ s hs).toFiniteLaw
      (templateCopyDecode μ hs) := by
  classical
  let χ := matrixColumnLaw (V := V) μ q₁ q₂ s hs
  let T := sourceTemplateCopies (V := V) (q₁ := q₁) (q₂ := q₂) μ hs
  let hT := sourceTemplateCopies_nonempty (V := V) (q₁ := q₁) (q₂ := q₂) μ hs
  intro F
  have hTmass : (FiniteLaw.uniform χ.Copies).prob (· ∈ T) = 255 / 256 := by
    rw [← RationalSeparation.copies_uniform_eq χ]
    simp only [T, sourceTemplateCopies, copyFamily, Finset.mem_filter,
      Finset.mem_univ, true_and]
    change χ.uniformCopies.prob (fun c => columnFamilyIndex (χ.forget c) = 0) = _
    exact (χ.uniformCopies_prob_preimage
      (fun a => columnFamilyIndex a = 0)).trans
        (column_family_masses (V := V) μ hs).1
  let sourceEvent : Column V X q₁ q₂ s → Prop :=
    fun a => match a with | .inl b => F b | .inr _ => False
  have hevent (c : χ.Copies) :
      (∃ hc : c ∈ T, F (templateCopyDecode μ hs ⟨c, hc⟩)) ↔
        sourceEvent (χ.forget c) := by
    constructor
    · rintro ⟨hc, hF⟩
      have hspec := templateCopyDecode_spec μ hs ⟨c, hc⟩
      rw [hspec]
      exact hF
    · intro hF
      cases h : χ.forget c with
      | inl b =>
          have hc : c ∈ T := by
            simp only [T, sourceTemplateCopies, copyFamily, Finset.mem_filter,
              Finset.mem_univ, true_and]
            rw [h]
            rfl
          refine ⟨hc, ?_⟩
          have hspec := templateCopyDecode_spec μ hs ⟨c, hc⟩
          rw [h] at hspec
          have hdec : templateCopyDecode μ hs ⟨c, hc⟩ = b :=
            Sum.inl.inj hspec.symm
          simpa [sourceEvent, h, hdec] using hF
      | inr b => simp [sourceEvent, h] at hF
  have heventmass :
      (FiniteLaw.uniform χ.Copies).prob
        (fun c => ∃ hc : c ∈ T, F (templateCopyDecode μ hs ⟨c, hc⟩)) =
      (255 / 256 : ℝ) * (templateFamilyLaw μ q₁ q₂ s hs).toFiniteLaw.prob F := by
    calc
      _ = χ.uniformCopies.prob
          (fun c => ∃ hc : c ∈ T, F (templateCopyDecode μ hs ⟨c, hc⟩)) := by
            rw [RationalSeparation.copies_uniform_eq]
      _ = χ.uniformCopies.prob (fun c => sourceEvent (χ.forget c)) := by
        congr 1
        funext c
        exact propext (hevent c)
      _ = χ.toFiniteLaw.prob sourceEvent := χ.uniformCopies_prob_preimage sourceEvent
      _ = _ := source_template_event_prob (V := V) μ hs F
  have hnorm := uniform_subtype_prob_mul T hT
    (fun t => F (templateCopyDecode μ hs t))
  rw [hTmass, heventmass] at hnorm
  have hlambda : (0 : ℝ) < 255 / 256 := by norm_num
  change (uniformSubtypeLaw T hT).prob
    (fun t => F (templateCopyDecode μ hs t)) = _
  nlinarith

/-- Coordinatewise exact pushforwards lift to arbitrary joint events under
the complete product laws. -/
theorem pi_pushes {I A B : Type*} [Fintype I] [DecidableEq I]
    [Fintype A] [Fintype B]
    (α : FiniteLaw A) (β : FiniteLaw B) (f : A → B)
    (hf : α.PushesTo β f) :
    (FiniteLaw.pi (fun _ : I => α)).PushesTo
      (FiniteLaw.pi (fun _ : I => β)) (fun x i => f (x i)) := by
  intro E
  apply FiniteLaw.prob_preimage_eq_of_fibres
    (FiniteLaw.pi (fun _ : I => α))
    (FiniteLaw.pi (fun _ : I => β)) (fun x i => f (x i))
    (fun y => ?_) E
  change (FiniteLaw.pi (fun _ : I => α)).prob
      (fun x => (fun i => f (x i)) = y) =
      (FiniteLaw.pi (fun _ : I => β)).weight y
  have hpoint : (fun x : I → A => (fun i => f (x i)) = y) =
      (fun x => ∀ i, f (x i) = y i) := by
    funext x
    apply propext
    constructor
    · intro h i; exact congrFun h i
    · intro h; exact funext h
  rw [hpoint]
  have hπ := FiniteLaw.pi_prob_coordinatewise
    (fun _ : I => α) (fun i a => f a = y i)
  rw [hπ]
  change (∏ i : I, α.prob (fun a => f a = y i)) =
    ∏ i : I, β.weight (y i)
  apply Finset.prod_congr rfl
  intro i _
  simpa only [FiniteLaw.prob_singleton] using hf (fun b => b = y i)

/-- Uniform words over the restricted copy alphabet are exactly the
independent product of its one-coordinate uniform laws. -/
theorem restrictedCopyLaw_eq_pi {I Z : Type*} [Fintype I] [DecidableEq I]
    [Fintype Z] [DecidableEq Z]
    (T : Finset Z) (hT : T.Nonempty) (J : Finset I) :
    restrictedCopyLaw T hT J =
      FiniteLaw.pi (fun _ : J => uniformSubtypeLaw T hT) := by
  classical
  letI : Nonempty T := ⟨⟨hT.choose, hT.choose_spec⟩⟩
  apply FiniteLaw.eq_of_weight_eq
  funext x
  simp [restrictedCopyLaw, uniformSubtypeLaw, FiniteLaw.uniform,
    FiniteLaw.pi, Finset.prod_const, ← inv_pow]

/-- The exact source pushforward on all selected coordinates, matching
the `hpush` input of `copy_projection_mass_le_image`. -/
theorem source_template_pi_pushes (μ : PositiveRationalLaw X) (hs : 4 ≤ s)
    (J : Finset I) [Fintype I] [DecidableEq I]
    [DecidableEq (SourceLawBinding.matrixColumnLaw (V := V) μ q₁ q₂ s hs).Copies] :
    (restrictedCopyLaw
      (sourceTemplateCopies (V := V) (q₁ := q₁) (q₂ := q₂) μ hs)
      (sourceTemplateCopies_nonempty μ hs) J).PushesTo
      (FiniteLaw.pi (fun _ : J => (templateFamilyLaw μ q₁ q₂ s hs).toFiniteLaw))
      (fun y j => templateCopyDecode μ hs (y j)) := by
  rw [restrictedCopyLaw_eq_pi]
  exact pi_pushes _ _ _ (template_copy_pushes (V := V) μ hs)

/-- The joint template-family image is witnessed by one retained original
tuple for all selected coordinates. -/
def templateJointImage {w : ℕ}
    (U : Set (Fin w → Column V X q₁ q₂ s))
    (J : Finset (Fin w)) : Set (J → Fin s × Template q₁ q₂ X) :=
  fun b => ∃ y ∈ U, ∀ j : J, y j.val = .inl (b j)

theorem copy_projection_image_subset
    (μ : PositiveRationalLaw X) (hs : 4 ≤ s)
    {w : ℕ}
    [DecidableEq (matrixColumnLaw (V := V) μ q₁ q₂ s hs).Copies]
    (U : Set (Fin w → Column V X q₁ q₂ s))
    (J : Finset (Fin w)) :
    (fun z : J → sourceTemplateCopies (V := V) (q₁ := q₁) (q₂ := q₂) μ hs =>
       fun j => templateCopyDecode μ hs (z j)) ''
        (TemplateProjection.projectionSet
          (copyRetained (matrixColumnLaw (V := V) μ q₁ q₂ s hs) w U)
          (sourceTemplateCopies (V := V) (q₁ := q₁) (q₂ := q₂) μ hs) J :
            Set (J → sourceTemplateCopies (V := V) (q₁ := q₁) (q₂ := q₂) μ hs)) ⊆
      templateJointImage U J := by
  classical
  let χ := matrixColumnLaw (V := V) μ q₁ q₂ s hs
  let T := sourceTemplateCopies (V := V) (q₁ := q₁) (q₂ := q₂) μ hs
  let P := copyRetained χ w U
  rintro b ⟨z, hz, rfl⟩
  obtain ⟨c, hc, hcoords⟩ :=
    (TemplateProjection.mem_projectionSet P T J z).mp hz
  refine ⟨χ.forgetTuple w c, ?_, ?_⟩
  · simpa [P, copyRetained] using hc
  · intro j
    have hj := hcoords j
    have hspec := templateCopyDecode_spec μ hs (z j)
    change χ.forget (c j.val) = .inl (templateCopyDecode μ hs (z j))
    rw [hj]
    exact hspec

open Classical in
/-- The checked copy density transfers to the literal source
template-family product law, with no law premise left to the caller. -/
theorem source_joint_mass_of_density
    (μ : PositiveRationalLaw X) (hs : 4 ≤ s)
    {w : ℕ} (U : Set (Fin w → Column V X q₁ q₂ s))
    (J : Finset (Fin w))
    (hdensity : (12 / 25 : ℝ) <
      TemplateProjection.projectionDensity
        (copyRetained (matrixColumnLaw (V := V) μ q₁ q₂ s hs) w U)
        (sourceTemplateCopies (V := V) (q₁ := q₁) (q₂ := q₂) μ hs) J) :
    (12 / 25 : ℝ) <
      (FiniteLaw.pi (fun _ : J => (templateFamilyLaw μ q₁ q₂ s hs).toFiniteLaw)).prob
        (· ∈ templateJointImage U J) := by
  classical
  let χ := matrixColumnLaw (V := V) μ q₁ q₂ s hs
  let T := sourceTemplateCopies (V := V) (q₁ := q₁) (q₂ := q₂) μ hs
  let hT := sourceTemplateCopies_nonempty (V := V) (q₁ := q₁) (q₂ := q₂) μ hs
  let P := copyRetained χ w U
  let ν : FiniteLaw (J → Fin s × Template q₁ q₂ X) :=
    FiniteLaw.pi (fun _ : J => (templateFamilyLaw μ q₁ q₂ s hs).toFiniteLaw)
  have hpush : (restrictedCopyLaw T hT J).PushesTo ν
      (fun z j => templateCopyDecode μ hs (z j)) :=
    source_template_pi_pushes (V := V) μ hs J
  have htransfer := copy_projection_mass_le_image P T hT J
    (templateCopyDecode μ hs) ν hpush
  have hsubset := copy_projection_image_subset (V := V) μ hs U J
  exact hdensity.trans_le (htransfer.trans
    (ν.prob_mono (fun b hb => hsubset hb)))

open Classical in
/-- T41 stated with the same explicit source copy alphabet used by the
law bridge, avoiding any change of decidability instance in the density. -/
theorem source_copy_projection_direct
    (μ : PositiveRationalLaw X) (hs : 4 ≤ s)
    (k : ℕ) (hk : 1 ≤ k)
    (U : Set (Fin (2 * k) → Column V X q₁ q₂ s))
    (hmass : (99 / 200 : ℝ) ≤
      (((matrixColumnLaw (V := V) μ q₁ q₂ s hs).toFiniteLaw).iid
        (2 * k)).prob (· ∈ U)) :
    ∃ J : Finset (Fin (2 * k)), J.card = k ∧
      (12 / 25 : ℝ) < TemplateProjection.projectionDensity
        (copyRetained (matrixColumnLaw (V := V) μ q₁ q₂ s hs) (2 * k) U)
        (sourceTemplateCopies (V := V) (q₁ := q₁) (q₂ := q₂) μ hs) J := by
  classical
  let χ := matrixColumnLaw (V := V) μ q₁ q₂ s hs
  let P := copyRetained χ (2 * k) U
  let T := sourceTemplateCopies (V := V) (q₁ := q₁) (q₂ := q₂) μ hs
  let hT := sourceTemplateCopies_nonempty (V := V) (q₁ := q₁) (q₂ := q₂) μ hs
  have hcopy : χ.uniformCopies = FiniteLaw.uniform χ.Copies :=
    RationalSeparation.copies_uniform_eq χ
  have hP : TemplateProjection.retainedDensity P =
      (χ.toFiniteLaw.iid (2 * k)).prob (· ∈ U) := by
    change (P.card : ℝ) / (Fintype.card χ.Copies : ℝ) ^ (2 * k) = _
    rw [← TemplateProjection.wordLaw_prob_finset,
      TemplateProjection.wordLaw, ← hcopy]
    simpa [P, copyRetained] using
      χ.uniformCopies_iid_prob_preimage (2 * k) (· ∈ U)
  have hlambda : TemplateProjection.lambda T = 255 / 256 := by
    rw [show TemplateProjection.lambda T =
      (FiniteLaw.uniform χ.Copies).prob (· ∈ T) from
      (FiniteLaw.uniform_prob_finset T).symm]
    exact (show (FiniteLaw.uniform χ.Copies).prob (· ∈ T) = 255 / 256
      from by
        rw [← hcopy]
        simp only [T, sourceTemplateCopies, copyFamily, Finset.mem_filter,
          Finset.mem_univ, true_and]
        change χ.uniformCopies.prob
          (fun c => columnFamilyIndex (χ.forget c) = 0) = _
        exact (χ.uniformCopies_prob_preimage
          (fun a => columnFamilyIndex a = 0)).trans
          (column_family_masses (V := V) μ hs).1)
  obtain ⟨J, hJ, hsharp, hcoarse⟩ :=
    TemplateProjection.dense_alphabet_projection k hk P T hT
  refine ⟨J, hJ, ?_⟩
  have hbound : (12 / 25 : ℝ) <
      TemplateProjection.retainedDensity P -
        2 * (1 - TemplateProjection.lambda T) := by
    rw [hP, hlambda]
    linarith
  exact hbound.trans_le (hcoarse.trans hsharp)

set_option maxHeartbeats 1000000 in
/-- Source-facing selection of a joint original template image. -/
theorem exists_source_template_joint_image
    (μ : PositiveRationalLaw X) (hs : 4 ≤ s)
    (k : ℕ) (hk : 1 ≤ k)
    (U : Set (Fin (2 * k) → Column V X q₁ q₂ s))
    (hmass : (99 / 200 : ℝ) ≤
      (((matrixColumnLaw (V := V) μ q₁ q₂ s hs).toFiniteLaw).iid
        (2 * k)).prob (· ∈ U)) :
    ∃ J : Finset (Fin (2 * k)), J.card = k ∧
      (12 / 25 : ℝ) <
        (FiniteLaw.pi (fun _ : J => (templateFamilyLaw μ q₁ q₂ s hs).toFiniteLaw)).prob
          (· ∈ templateJointImage U J) := by
  classical
  obtain ⟨J, hJ, hdensity⟩ :=
    source_copy_projection_direct (V := V) μ hs k hk U hmass
  exact ⟨J, hJ, source_joint_mass_of_density (V := V) μ hs U J hdensity⟩

/-- Regroup a whole vector of pairs into one whole bin vector and one
whole selector vector. -/
def mergeEquiv {I A B : Type*} : ((I → A) × (I → B)) ≃ (I → A × B) where
  toFun ab := fun i => (ab.1 i, ab.2 i)
  invFun z := (fun i => (z i).1, fun i => (z i).2)
  left_inv ab := by cases ab; simp
  right_inv z := by funext i; simp

/-- The ambient independent template-family product splits exactly into
independent *whole tuples* of bin labels and selectors. -/
theorem pi_prod_pushes {I A B : Type*} [Fintype I] [DecidableEq I]
    [Fintype A] [Fintype B] (α : FiniteLaw A) (β : FiniteLaw B) :
    ((FiniteLaw.pi (fun _ : I => α)).prod (FiniteLaw.pi (fun _ : I => β))).PushesTo
      (FiniteLaw.pi (fun _ : I => α.prod β)) (mergeEquiv) := by
  classical
  intro E
  unfold FiniteLaw.prob
  apply Fintype.sum_equiv (mergeEquiv (I := I) (A := A) (B := B))
  intro ab
  have hw :
      ((FiniteLaw.pi (fun _ : I => α)).prod (FiniteLaw.pi (fun _ : I => β))).weight ab =
      (FiniteLaw.pi (fun _ : I => α.prod β)).weight (mergeEquiv ab) := by
    simp [FiniteLaw.pi, FiniteLaw.prod, mergeEquiv,
      Finset.prod_mul_distrib]
  split_ifs <;> simp_all

/-- Average over complete first-coordinate tuples. The selected tuple is
one fixed public bin assignment, not a coordinatewise selection depending
on the selector word. -/
theorem exists_bin_tuple {I A B : Type*} [Fintype I] [DecidableEq I]
    [Fintype A] [Fintype B] (α : FiniteLaw A) (β : FiniteLaw B)
    (H : (I → A × B) → Prop) (r : ℝ)
    (hjoint : r < (FiniteLaw.pi (fun _ : I => α.prod β)).prob H) :
    ∃ p : I → A,
      r < (FiniteLaw.pi (fun _ : I => β)).prob
        (fun z => H (fun i => (p i, z i))) := by
  classical
  let αI := FiniteLaw.pi (fun _ : I => α)
  let βI := FiniteLaw.pi (fun _ : I => β)
  have hdecomp : (FiniteLaw.pi (fun _ : I => α.prod β)).prob H =
      ∑ p : I → A, αI.weight p * βI.prob
        (fun z => H (fun i => (p i, z i))) := by
    rw [← pi_prod_pushes α β H]
    exact FiniteLaw.prod_prob αI βI
      (fun p z => H (fun i => (p i, z i)))
  by_contra hn
  have hall (p : I → A) : βI.prob
      (fun z => H (fun i => (p i, z i))) ≤ r := by
    exact le_of_not_gt (fun hp => hn ⟨p, hp⟩)
  have hupper :
      (∑ p : I → A, αI.weight p * βI.prob
        (fun z => H (fun i => (p i, z i)))) ≤
      ∑ p : I → A, αI.weight p * r := by
    apply Finset.sum_le_sum
    intro p _
    exact mul_le_mul_of_nonneg_left (hall p) (αI.nonneg p)
  have heq : (∑ p : I → A, αI.weight p * r) = r := by
    rw [← Finset.sum_mul, αI.total, one_mul]
  linarith

/-- The literal source template-family law is a uniform bin followed by
the original selector law, on the same labelled pair carrier. -/
theorem source_template_family_prod [Nonempty (Fin s)]
    (μ : PositiveRationalLaw X) (hs : 4 ≤ s) :
    (templateFamilyLaw μ q₁ q₂ s hs).toFiniteLaw =
      (FiniteLaw.uniform (Fin s)).prod
        (SourceLaws.templateLaw μ q₁ q₂).toFiniteLaw := by
  letI : NeZero s := ⟨by omega⟩
  change (SourceLaws.templateRowLaw μ q₁ q₂ s).toFiniteLaw = _
  rw [SourceLaws.templateRowLaw, PositiveRationalLaw.toFiniteLaw_prod]
  have hbin : (PositiveRationalLaw.uniform (Fin s)).toFiniteLaw =
      FiniteLaw.uniform (Fin s) := by
    apply FiniteLaw.eq_of_weight_eq
    funext p
    simp [PositiveRationalLaw.uniform, FiniteLaw.uniform,
      PositiveRationalLaw.toFiniteLaw]
  rw [hbin]

def selectorJointImage {w : ℕ}
    (U : Set (Fin w → Column V X q₁ q₂ s))
    (J : Finset (Fin w)) (p : J → Fin s) :
    Set (J → Template q₁ q₂ X) :=
  fun z => ∃ y ∈ U, ∀ j : J, y j.val = .inl (p j, z j)

/-- One entire bin vector retains the joint template image mass; the
selector event still has one whole original-column completion. -/
theorem exists_source_fixed_bins
    (μ : PositiveRationalLaw X) (hs : 4 ≤ s)
    (k : ℕ) (hk : 1 ≤ k)
    (U : Set (Fin (2 * k) → Column V X q₁ q₂ s))
    (hmass : (99 / 200 : ℝ) ≤
      (((matrixColumnLaw (V := V) μ q₁ q₂ s hs).toFiniteLaw).iid
        (2 * k)).prob (· ∈ U)) :
    ∃ J : Finset (Fin (2 * k)), J.card = k ∧
      ∃ p : J → Fin s,
        (12 / 25 : ℝ) <
          (FiniteLaw.pi (fun _ : J =>
            (SourceLaws.templateLaw μ q₁ q₂).toFiniteLaw)).prob
              (· ∈ selectorJointImage U J p) := by
  classical
  letI : Nonempty (Fin s) := ⟨⟨0, by omega⟩⟩
  obtain ⟨J, hJ, hmassJ⟩ :=
    exists_source_template_joint_image (V := V) μ hs k hk U hmass
  let σ := (SourceLaws.templateLaw μ q₁ q₂).toFiniteLaw
  have hprod : (12 / 25 : ℝ) <
      (FiniteLaw.pi (fun _ : J => (FiniteLaw.uniform (Fin s)).prod σ)).prob
        (· ∈ templateJointImage U J) := by
    dsimp [σ]
    simpa only [← source_template_family_prod μ hs] using hmassJ
  obtain ⟨p, hp⟩ := exists_bin_tuple (FiniteLaw.uniform (Fin s)) σ
    (fun b => b ∈ templateJointImage U J) (12 / 25) hprod
  refine ⟨J, hJ, p, ?_⟩
  simpa only [selectorJointImage, templateJointImage] using hp

/-- Reindex the selected original coordinates by `Fin k`. The selector
tuple image and its ambient iid law are unchanged under this bijection. -/
theorem exists_source_selector_image
    (μ : PositiveRationalLaw X) (hs : 4 ≤ s)
    (k : ℕ) (hk : 1 ≤ k)
    (U : Set (Fin (2 * k) → Column V X q₁ q₂ s))
    (hmass : (99 / 200 : ℝ) ≤
      (((matrixColumnLaw (V := V) μ q₁ q₂ s hs).toFiniteLaw).iid
        (2 * k)).prob (· ∈ U)) :
    ∃ e : Fin k → Fin (2 * k), Function.Injective e ∧
      ∃ p : Fin k → Fin s,
        (12 / 25 : ℝ) <
          (((SourceLaws.templateLaw μ q₁ q₂).toFiniteLaw).iid k).prob
            (· ∈ selectorImage U e p) := by
  classical
  obtain ⟨J, hJ, pJ, hmassJ⟩ :=
    exists_source_fixed_bins (V := V) μ hs k hk U hmass
  let jEquiv : Fin k ≃ J :=
    (Fintype.equivFinOfCardEq (by simpa using hJ)).symm
  let e : Fin k → Fin (2 * k) := fun t => (jEquiv t).val
  let p : Fin k → Fin s := fun t => pJ (jEquiv t)
  let σ := (SourceLaws.templateLaw μ q₁ q₂).toFiniteLaw
  have he : Function.Injective e := by
    intro t u h
    exact jEquiv.injective (Subtype.ext h)
  have hevent (z : J → Template q₁ q₂ X) :
      z ∈ selectorJointImage U J pJ ↔
        (fun t => z (jEquiv t)) ∈ selectorImage U e p := by
    constructor
    · rintro ⟨y, hy, hall⟩
      exact ⟨y, hy, fun t => hall (jEquiv t)⟩
    · rintro ⟨y, hy, hall⟩
      refine ⟨y, hy, ?_⟩
      intro j
      obtain ⟨t, rfl⟩ := jEquiv.surjective j
      exact hall t
  have hrestrict := FiniteLaw.pi_prob_restrict (fun _ : J => σ)
    jEquiv jEquiv.injective (fun z : Fin k → Template q₁ q₂ X =>
      z ∈ selectorImage U e p)
  have hmass' : (12 / 25 : ℝ) <
      (FiniteLaw.pi (fun _ : Fin k => σ)).prob (· ∈ selectorImage U e p) := by
    have heq : (FiniteLaw.pi (fun _ : J => σ)).prob
        (· ∈ selectorJointImage U J pJ) =
        (FiniteLaw.pi (fun _ : Fin k => σ)).prob
          (· ∈ selectorImage U e p) := by
      rw [show (fun z : J → Template q₁ q₂ X =>
        z ∈ selectorJointImage U J pJ) =
        (fun z => (fun t => z (jEquiv t)) ∈ selectorImage U e p) from by
          funext z
          exact propext (hevent z)]
      exact hrestrict
    exact hmassJ.trans_eq heq
  refine ⟨e, he, p, ?_⟩
  simpa only [RestorationCovers.pi_const_prob] using hmass'

/-- Starting from the good joint projection on original full columns,
the actual first-Bob child has original selected coordinates and fixed
template bins whose selector-tuple image has mass above `12/25`. -/
theorem exists_original_bob_child_selector_image
    (μ : PositiveRationalLaw X) (hs : 4 ≤ s)
    {w : ℕ} (k : ℕ) (hk : 1 ≤ k)
    (Y' : Set (Fin w → Column V X q₁ q₂ s))
    (e₀ : Fin (2 * k) → Fin w) (he₀ : Function.Injective e₀)
    (query : (Fin w → Column V X q₁ q₂ s) → Bool)
    (hgood : (99 / 100 : ℝ) ≤
      ProductProjections.projectionMass
        (fun _ : Fin w => (matrixColumnLaw (V := V) μ q₁ q₂ s hs).toFiniteLaw)
        (· ∈ Y') (Finset.univ.image e₀)) :
    ∃ b : Bool, ∃ e : Fin k → Fin w, Function.Injective e ∧
      (∀ t, e t ∈ Finset.univ.image e₀) ∧
      ∃ p : Fin k → Fin s,
        (12 / 25 : ℝ) <
          (((SourceLaws.templateLaw μ q₁ q₂).toFiniteLaw).iid k).prob
            (· ∈ selectorImage (ReferenceColumnStep.columnChild Y' query b) e p) := by
  classical
  let χ := (matrixColumnLaw (V := V) μ q₁ q₂ s hs).toFiniteLaw
  obtain ⟨b, hchild⟩ := good_projected_child χ Y' e₀ he₀ query hgood
  let O := ReferenceColumnStep.columnChild Y' query b
  let U := ReferenceCapacity.selectedColumns e₀ O
  obtain ⟨e₁, he₁, p, hmass⟩ :=
    exists_source_selector_image (V := V) μ hs k hk U hchild
  let e : Fin k → Fin w := fun t => e₀ (e₁ t)
  have he : Function.Injective e := he₀.comp he₁
  have hsub : selectorImage U e₁ p ⊆ selectorImage O e p := by
    rintro z ⟨v, hv, hall⟩
    obtain ⟨y, hy, rfl⟩ := hv
    refine ⟨y, hy, ?_⟩
    exact hall
  refine ⟨b, e, he, ?_, p, ?_⟩
  · intro t
    exact Finset.mem_image.mpr ⟨e₁ t, Finset.mem_univ _, rfl⟩
  · exact hmass.trans_le
      ((((SourceLaws.templateLaw μ q₁ q₂).toFiniteLaw).iid k).prob_mono
        (fun z hz => hsub hz))

/-- At a final node, no Bob child is taken: the same source projection
directly supplies an original fixed-bin selector image. -/
theorem exists_original_final_selector_image
    (μ : PositiveRationalLaw X) (hs : 4 ≤ s)
    {w : ℕ} (k : ℕ) (hk : 1 ≤ k)
    (Y' : Set (Fin w → Column V X q₁ q₂ s))
    (e₀ : Fin (2 * k) → Fin w) (he₀ : Function.Injective e₀)
    (hgood : (99 / 100 : ℝ) ≤
      ProductProjections.projectionMass
        (fun _ : Fin w => (matrixColumnLaw (V := V) μ q₁ q₂ s hs).toFiniteLaw)
        (· ∈ Y') (Finset.univ.image e₀)) :
    ∃ e : Fin k → Fin w, Function.Injective e ∧
      (∀ t, e t ∈ Finset.univ.image e₀) ∧
      ∃ p : Fin k → Fin s,
        (12 / 25 : ℝ) <
          (((SourceLaws.templateLaw μ q₁ q₂).toFiniteLaw).iid k).prob
            (· ∈ selectorImage Y' e p) := by
  classical
  let χ := (matrixColumnLaw (V := V) μ q₁ q₂ s hs).toFiniteLaw
  let U := ReferenceCapacity.selectedColumns e₀ Y'
  have hselected : (99 / 200 : ℝ) ≤ (χ.iid (2 * k)).prob (· ∈ U) := by
    have hfull : (99 / 100 : ℝ) ≤ (χ.iid (2 * k)).prob (· ∈ U) := by
      rwa [ReferenceProjectionMass.projectionMass_eq_selectedColumns_of_injective
        χ Y' (Finset.univ.image e₀) e₀ he₀ rfl] at hgood
    linarith
  obtain ⟨e₁, he₁, p, hmass⟩ :=
    exists_source_selector_image (V := V) μ hs k hk U hselected
  let e : Fin k → Fin w := fun t => e₀ (e₁ t)
  have he : Function.Injective e := he₀.comp he₁
  have hsub : selectorImage U e₁ p ⊆ selectorImage Y' e p := by
    rintro z ⟨v, hv, hall⟩
    obtain ⟨y, hy, rfl⟩ := hv
    exact ⟨y, hy, hall⟩
  refine ⟨e, he, ?_, p, ?_⟩
  · intro t
    exact Finset.mem_image.mpr ⟨e₁ t, Finset.mem_univ _, rfl⟩
  · exact hmass.trans_le
      ((((SourceLaws.templateLaw μ q₁ q₂).toFiniteLaw).iid k).prob_mono
        (fun z hz => hsub hz))

end Paper2.ProtectedIncomingTemplateLaw

#print axioms Paper2.ProtectedIncomingTemplateLaw.uniform_subtype_prob_mul
#print axioms Paper2.ProtectedIncomingTemplateLaw.template_copy_pushes
#print axioms Paper2.ProtectedIncomingTemplateLaw.pi_pushes
#print axioms Paper2.ProtectedIncomingTemplateLaw.source_template_pi_pushes
#print axioms Paper2.ProtectedIncomingTemplateLaw.exists_source_template_joint_image
#print axioms Paper2.ProtectedIncomingTemplateLaw.pi_prod_pushes
#print axioms Paper2.ProtectedIncomingTemplateLaw.exists_bin_tuple
#print axioms Paper2.ProtectedIncomingTemplateLaw.exists_source_fixed_bins
#print axioms Paper2.ProtectedIncomingTemplateLaw.exists_source_selector_image
#print axioms Paper2.ProtectedIncomingTemplateLaw.exists_original_bob_child_selector_image
#print axioms Paper2.ProtectedIncomingTemplateLaw.exists_original_final_selector_image
