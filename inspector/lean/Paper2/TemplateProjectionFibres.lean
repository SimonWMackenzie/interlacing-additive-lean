import Mathlib

/-!
# Exact pattern fibres for projection into a restricted alphabet

Frozen v12: `appendices/A-interlacing.tex:608--676`, T41.
The retained word set is arbitrary. The product structure used here belongs
to the ambient complete cube and to its exact alphabet-membership fibres,
not to the retained set.
-/

namespace Paper2.TemplateProjection

open scoped BigOperators

variable {ι Z : Type*} [Fintype ι] [DecidableEq ι] [Fintype Z] [DecidableEq Z]

/-- The coordinates at which a word belongs to the distinguished alphabet. -/
def pattern (T : Finset Z) (w : ι → Z) : Finset ι :=
  Finset.univ.filter (fun i => w i ∈ T)

@[simp] theorem mem_pattern (T : Finset Z) (w : ι → Z) (i : ι) :
    i ∈ pattern T w ↔ w i ∈ T := by simp [pattern]

/-- Actual projected patterns whose values all belong to `T`. -/
noncomputable def projectionSet (P : Finset (ι → Z)) (T : Finset Z) (J : Finset ι) :
    Finset (J → T) := by
  classical
  exact Finset.univ.filter (fun y => ∃ w ∈ P, ∀ j : J, w j.val = (y j).val)

@[simp] theorem mem_projectionSet (P : Finset (ι → Z)) (T : Finset Z) (J : Finset ι)
    (y : J → T) : y ∈ projectionSet P T J ↔ ∃ w ∈ P, ∀ j : J, w j.val = (y j).val := by
  classical
  simp [projectionSet]

noncomputable def projectionDensity (P : Finset (ι → Z)) (T : Finset Z) (J : Finset ι) : ℝ :=
  (projectionSet P T J).card / (T.card : ℝ) ^ J.card

/-- Words with exactly a specified membership pattern. -/
abbrev PatternWord (T : Finset Z) (I : Finset ι) := {w : ι → Z // pattern T w = I}

/-- The coordinates outside the chosen projection, with their exact prescribed
membership status. Empty fibres are permitted and handled by cardinalities. -/
abbrev OtherWord (T : Finset Z) (I J : Finset ι) :=
  (i : {i : ι // i ∉ J}) → {z : Z // z ∈ T ↔ i.val ∈ I}

/-- On a fixed membership fibre, the selected `T`-coordinates form an honest
Cartesian factor. No nonemptiness of the other factor is assumed. -/
noncomputable def patternEquiv (T : Finset Z) (I J : Finset ι) (hJI : J ⊆ I) :
    PatternWord T I ≃ (J → T) × OtherWord T I J := by
  classical
  refine
    { toFun := fun w =>
        (fun j => ⟨w.val j.val, (mem_pattern T w.val j.val).mp (w.property.symm ▸ hJI j.property)⟩,
         fun i => ⟨w.val i.val, by rw [← mem_pattern, w.property]⟩)
      invFun := fun yz => ⟨fun i => if hi : i ∈ J then (yz.1 ⟨i, hi⟩).val
          else (yz.2 ⟨i, hi⟩).val, ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · ext i
    rw [mem_pattern]
    by_cases hi : i ∈ J
    · simp only [dif_pos hi]
      exact iff_of_true (yz.1 ⟨i, hi⟩).property (hJI hi)
    · simp only [dif_neg hi]
      exact (yz.2 ⟨i, hi⟩).property
  · intro w
    apply Subtype.ext
    funext i
    by_cases hi : i ∈ J <;> simp [hi]
  · intro yz
    apply Prod.ext
    · funext j
      apply Subtype.ext
      simp
    · funext i
      apply Subtype.ext
      simp [i.property]

@[simp] theorem patternEquiv_fst_val (T : Finset Z) (I J : Finset ι) (hJI : J ⊆ I)
    (w : PatternWord T I) (j : J) : ((patternEquiv T I J hJI w).1 j).val = w.val j.val := rfl

theorem card_patternWord (T : Finset Z) (I J : Finset ι) (hJI : J ⊆ I) :
    Fintype.card (PatternWord T I) =
      T.card ^ J.card * Fintype.card (OtherWord T I J) := by
  classical
  rw [Fintype.card_congr (patternEquiv T I J hJI), Fintype.card_prod]
  simp

/-- The retained part of one membership fibre injects into the actual
projection set times the unchanged outside-coordinate factor. -/
theorem retained_fibre_card_le (P : Finset (ι → Z)) (T : Finset Z)
    (I J : Finset ι) (hJI : J ⊆ I) :
    (P.filter (fun w => pattern T w = I)).card ≤
      (projectionSet P T J).card * Fintype.card (OtherWord T I J) := by
  classical
  let Q := P.filter (fun w => pattern T w = I)
  let f : Q → (projectionSet P T J) × OtherWord T I J := fun w =>
    let w' : PatternWord T I := ⟨w.val, (Finset.mem_filter.mp w.property).2⟩
    let yz := patternEquiv T I J hJI w'
    (⟨yz.1, (mem_projectionSet P T J yz.1).mpr
      ⟨w.val, (Finset.mem_filter.mp w.property).1, fun _ => rfl⟩⟩, yz.2)
  have hf : Function.Injective f := by
    intro w v h
    have he : patternEquiv T I J hJI ⟨w.val, (Finset.mem_filter.mp w.property).2⟩ =
        patternEquiv T I J hJI ⟨v.val, (Finset.mem_filter.mp v.property).2⟩ := by
      have h1 := congrArg (fun z => z.1.val) h
      have h2 := congrArg Prod.snd h
      exact Prod.ext h1 h2
    exact Subtype.ext (congrArg (fun w : PatternWord T I => w.val)
      ((patternEquiv T I J hJI).injective he))
  simpa only [Fintype.card_prod, Fintype.card_coe] using Fintype.card_le_of_injective f hf

/-- Conditional projection domination in exact cardinality form. -/
theorem retained_fibre_density_le (P : Finset (ι → Z)) (T : Finset Z) (hT : T.Nonempty)
    (I J : Finset ι) (hJI : J ⊆ I) :
    ((P.filter (fun w => pattern T w = I)).card : ℝ) ≤
      projectionDensity P T J * Fintype.card (PatternWord T I) := by
  classical
  have ht : (0 : ℝ) < T.card := Nat.cast_pos.mpr (Finset.card_pos.mpr hT)
  rw [card_patternWord T I J hJI]
  unfold projectionDensity
  push_cast
  have he : ((projectionSet P T J).card : ℝ) / (T.card : ℝ) ^ J.card *
      ((T.card : ℝ) ^ J.card * Fintype.card (OtherWord T I J)) =
      (projectionSet P T J).card * Fintype.card (OtherWord T I J) := by
    field_simp
  rw [he]
  exact_mod_cast retained_fibre_card_le P T I J hJI

end Paper2.TemplateProjection
