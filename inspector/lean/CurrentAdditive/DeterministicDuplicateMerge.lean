import Paper2.RestrictionProfiles

/-! Private duplicate-index merging for Appendix I.  The target carrier is
the set of distinct decoded entries.  Every old index contributes its full
weight to its fibre; no canonical representative's weight is substituted. -/

namespace Paper2

open scoped BigOperators
open Workspace.Types.CommComplexity

namespace PositiveRationalLaw

variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq B]

/-- Merge a surjective family of old indices by summing every fibre. -/
noncomputable def merge (μ : PositiveRationalLaw A) (f : A → B)
    (hf : Function.Surjective f) : PositiveRationalLaw B where
  weight b := ∑ a, if f a = b then μ.weight a else 0
  positive b := by
    classical
    obtain ⟨a, rfl⟩ := hf b
    have hle : μ.weight a ≤ ∑ x, if f x = f a then μ.weight x else 0 := by
      have hnonneg (x : A) : 0 ≤ (if f x = f a then μ.weight x else 0) := by
        split_ifs <;> simp [(μ.positive x).le]
      have h := Finset.single_le_sum (s := Finset.univ)
        (fun x (_ : x ∈ (Finset.univ : Finset A)) => hnonneg x)
        (Finset.mem_univ a)
      simpa using h
    exact lt_of_lt_of_le (μ.positive a) hle
  total := by
    classical
    rw [Finset.sum_comm]
    simpa using μ.total

theorem merge_weight (μ : PositiveRationalLaw A) (f : A → B)
    (hf : Function.Surjective f) (b : B) :
    (μ.merge f hf).weight b = ∑ a, if f a = b then μ.weight a else 0 := rfl

theorem merge_prob_preimage (μ : PositiveRationalLaw A) (f : A → B)
    (hf : Function.Surjective f) (E : B → Prop) :
    μ.toFiniteLaw.prob (fun a => E (f a)) =
      (μ.merge f hf).toFiniteLaw.prob E := by
  classical
  apply FiniteLaw.prob_preimage_eq_of_fibres
  intro b
  simp only [FiniteLaw.prob, toFiniteLaw, merge_weight]
  simp only [Rat.cast_sum]
  apply Finset.sum_congr rfl
  intro a _
  by_cases h : f a = b <;> simp [h]

theorem merge_pushesTo (μ : PositiveRationalLaw A) (f : A → B)
    (hf : Function.Surjective f) :
    μ.toFiniteLaw.PushesTo (μ.merge f hf).toFiniteLaw f :=
  μ.merge_prob_preimage f hf

end PositiveRationalLaw

namespace DuplicateMerge

variable {A X : Type*} [Fintype A]

/-- The exact set of distinct decoded labels; it is finite because `A` is. -/
abbrev Decoded (f : A → X) := Set.range f

noncomputable instance decodedFintype (f : A → X) : Fintype (Decoded f) :=
  Fintype.ofFinite _

noncomputable instance decodedDecidableEq (f : A → X) : DecidableEq (Decoded f) :=
  Classical.decEq _

noncomputable def decode (f : A → X) : A → Decoded f :=
  fun a => ⟨f a, ⟨a, rfl⟩⟩

theorem decode_surjective (f : A → X) : Function.Surjective (decode f) := by
  rintro ⟨x, a, ha⟩
  exact ⟨a, Subtype.ext ha⟩

noncomputable def mergedOnImage (μ : PositiveRationalLaw A) (f : A → X) :
    PositiveRationalLaw (Decoded f) :=
  μ.merge (decode f) (decode_surjective f)

theorem mergedOnImage_prob (μ : PositiveRationalLaw A) (f : A → X)
    (E : Decoded f → Prop) :
    μ.toFiniteLaw.prob (fun a => E (decode f a)) =
      (mergedOnImage μ f).toFiniteLaw.prob E := by
  exact μ.merge_prob_preimage (decode f) (decode_surjective f) E

end DuplicateMerge

namespace DuplicateMerge

variable {A B X Y : Type*}
  [Fintype A] [Fintype B] [Fintype X] [Fintype Y]
  [DecidableEq X] [DecidableEq Y]

/-- Choose a representative only to recover an entry.  Its weight is not used. -/
noncomputable def representative (f : A → X) (hf : Function.Surjective f) :
    X → A := fun x => Classical.choose (hf x)

theorem representative_spec (f : A → X) (hf : Function.Surjective f) (x : X) :
    f (representative f hf x) = x := Classical.choose_spec (hf x)

theorem cost_eq (F : X → Y → Bool) (f : A → X) (g : B → Y)
    (hf : Function.Surjective f) (hg : Function.Surjective g) :
    D (fun a b => F (f a) (g b)) = D F :=
  pullback_D_eq_of_surjective F f g hf hg

theorem restriction_cost_eq (F : X → Y → Bool) (f : A → X) (g : B → Y)
    (hf : Function.Surjective f) (hg : Function.Surjective g)
    (U : Set X) (V : Set Y) :
    Compression.restrictionD (fun a b => F (f a) (g b))
      (f ⁻¹' U) (g ⁻¹' V) = Compression.restrictionD F U V :=
  restrictionD_pullback_preimage F f g hf hg U V

theorem profile_iff (F : X → Y → Bool) (f : A → X) (g : B → Y)
    (hf : Function.Surjective f) (hg : Function.Surjective g)
    (μA : PositiveRationalLaw A) (μB : PositiveRationalLaw B)
    (ρ : ℝ) (d : ℤ) :
    RestrictionProfile (fun a b => F (f a) (g b))
      μA.toFiniteLaw μB.toFiniteLaw ρ d ↔
    RestrictionProfile F (μA.merge f hf).toFiniteLaw
      (μB.merge g hg).toFiniteLaw ρ d :=
  restrictionProfile_pullback_iff F
    (μA.merge f hf).toFiniteLaw (μB.merge g hg).toFiniteLaw
    μA.toFiniteLaw μB.toFiniteLaw f g
    (μA.merge_pushesTo f hf) (μB.merge_pushesTo g hg)
    hf hg ρ d

/-- The final distinct-label matrix uses only values that were actually
decoded, so its two decoders are automatically onto. -/
theorem image_cost_eq (F : X → Y → Bool) (f : A → X) (g : B → Y) :
    D (fun a b => F (f a) (g b)) =
      D (fun x : Decoded f => fun y : Decoded g => F x.val y.val) := by
  let f' := decode f
  let g' := decode g
  exact cost_eq (fun x : Decoded f => fun y : Decoded g => F x.val y.val)
    f' g' (decode_surjective f) (decode_surjective g)

theorem image_restriction_cost_eq (F : X → Y → Bool)
    (f : A → X) (g : B → Y) (U : Set (Decoded f)) (V : Set (Decoded g)) :
    Compression.restrictionD (fun a b => F (f a) (g b))
      ((decode f) ⁻¹' U) ((decode g) ⁻¹' V) =
    Compression.restrictionD
      (fun x : Decoded f => fun y : Decoded g => F x.val y.val) U V := by
  exact restriction_cost_eq
    (fun x : Decoded f => fun y : Decoded g => F x.val y.val)
    (decode f) (decode g) (decode_surjective f) (decode_surjective g) U V

theorem image_profile_iff (F : X → Y → Bool) (f : A → X) (g : B → Y)
    (μA : PositiveRationalLaw A) (μB : PositiveRationalLaw B)
    (ρ : ℝ) (d : ℤ) :
    RestrictionProfile (fun a b => F (f a) (g b))
      μA.toFiniteLaw μB.toFiniteLaw ρ d ↔
    RestrictionProfile
      (fun x : Decoded f => fun y : Decoded g => F x.val y.val)
      (mergedOnImage μA f).toFiniteLaw (mergedOnImage μB g).toFiniteLaw ρ d := by
  exact profile_iff
    (fun x : Decoded f => fun y : Decoded g => F x.val y.val)
    (decode f) (decode g) (decode_surjective f) (decode_surjective g)
    μA μB ρ d

end DuplicateMerge
end Paper2

#print axioms Paper2.PositiveRationalLaw.merge_prob_preimage
#print axioms Paper2.DuplicateMerge.mergedOnImage_prob
#print axioms Paper2.DuplicateMerge.image_cost_eq
#print axioms Paper2.DuplicateMerge.image_restriction_cost_eq
#print axioms Paper2.DuplicateMerge.image_profile_iff
