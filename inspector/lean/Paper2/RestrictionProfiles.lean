import Paper2.RationalTupleTransport
import Paper2.Compression

/-!
# Restriction profiles and exact transport through duplicate labels

Frozen source: v12 Section 3, `def:profile`, and Appendix A,
`cl:rational-laws`. All lower bounds below refer to the actual deterministic
protocol complexity. Costs are cast to integers before comparison with
`d - j`; this is not truncated natural subtraction.

An arbitrary retained set of labels is sent to its actual image. No product
structure, independence, or closure under copy fibres is required. Transport
is proved in both directions, including on full interlace tuple carriers.
Numerical ceiling repair and the interlacing lower-bound theorem are separate
obligations; no amplifier conclusion is an assumption in this module.
-/

namespace Paper2

open scoped BigOperators
open Workspace.Types.CommComplexity

namespace FiniteLaw

variable {A X : Type*} [Fintype A] [Fintype X]

/-- The equality of laws used below is equality on every event, not only
on coordinatewise or independent events. -/
def PushesTo (μ : FiniteLaw A) (ν : FiniteLaw X) (f : A → X) : Prop :=
  ∀ E : X → Prop, μ.prob (fun a => E (f a)) = ν.prob E

/-- A retained set may contain only part of each fibre. Its actual image
still has at least its mass under exact pushforward. -/
theorem prob_le_image (μ : FiniteLaw A) (ν : FiniteLaw X) (f : A → X)
    (hf : μ.PushesTo ν f) (U : Set A) :
    μ.prob (· ∈ U) ≤ ν.prob (· ∈ f '' U) := by
  rw [← hf (· ∈ f '' U)]
  exact μ.prob_mono fun a ha => ⟨a, ha, rfl⟩

end FiniteLaw

variable {X Y A B : Type*}

/-- Forgetting labels on a retained set maps onto its actual image. -/
def retainedImageMap (f : A → X) (U : Set A) : U → (f '' U) :=
  fun a => ⟨f a.val, a.val, a.property, rfl⟩

theorem retainedImageMap_surjective (f : A → X) (U : Set A) :
    Function.Surjective (retainedImageMap f U) := by
  rintro ⟨x, a, ha, hax⟩
  exact ⟨⟨a, ha⟩, Subtype.ext hax⟩

/-- Exact cost equality for arbitrary retained labelled inputs. The maps
need not be surjective on their ambient input spaces. -/
theorem restrictionD_pullback_image [Fintype X] [Fintype Y]
    [Fintype A] [Fintype B] (F : X → Y → Bool)
    (f : A → X) (g : B → Y) (U : Set A) (V : Set B) :
    Compression.restrictionD (fun a b => F (f a) (g b)) U V =
      Compression.restrictionD F (f '' U) (g '' V) := by
  classical
  exact pullback_D_eq_of_surjective
    (fun (x : f '' U) (y : g '' V) => F x.val y.val)
    (retainedImageMap f U) (retainedImageMap g V)
    (retainedImageMap_surjective f U) (retainedImageMap_surjective g V)

/-- Keeping all copies of each retained original label preserves cost
exactly. Surjectivity prevents original inputs from disappearing. -/
theorem restrictionD_pullback_preimage [Fintype X] [Fintype Y]
    [Fintype A] [Fintype B] (F : X → Y → Bool)
    (f : A → X) (g : B → Y) (hf : Function.Surjective f)
    (hg : Function.Surjective g) (U : Set X) (V : Set Y) :
    Compression.restrictionD (fun a b => F (f a) (g b)) (f ⁻¹' U) (g ⁻¹' V) =
      Compression.restrictionD F U V := by
  rw [restrictionD_pullback_image, Set.image_preimage_eq _ hf, Set.image_preimage_eq _ hg]

variable [Fintype X] [Fintype Y]

/-- A two-threshold lower bound for every retained rectangle, measured
under the specified finite laws. The target lower bound is an integer. -/
def RestrictionLowerBound (F : X → Y → Bool) (μX : FiniteLaw X)
    (μY : FiniteLaw Y) (a b : ℝ) (c : ℤ) : Prop :=
  ∀ (U : Set X) (V : Set Y), a ≤ μX.prob (· ∈ U) → b ≤ μY.prob (· ∈ V) →
    c ≤ (Compression.restrictionD F U V : ℤ)

/-- V12 `def:profile`. In applications `0 < ρ ≤ 1`; the same predicate
is meaningful for any threshold, so those side conditions are external.
The three column thresholds are exactly `3/5`, `3/10`, and `3/20`. -/
def RestrictionProfile (F : X → Y → Bool) (μX : FiniteLaw X)
    (μY : FiniteLaw Y) (ρ : ℝ) (d : ℤ) : Prop :=
  ∀ j : Fin 3, RestrictionLowerBound F μX μY ρ
    ((3 / 5 : ℝ) * (1 / 2 : ℝ) ^ j.val) (d - (j.val : ℤ))

/-- A direct natural-index form of the profile definition, retaining
integer subtraction even when `d < j`. -/
theorem restrictionProfile_iff (F : X → Y → Bool) (μX : FiniteLaw X)
    (μY : FiniteLaw Y) (ρ : ℝ) (d : ℤ) :
    RestrictionProfile F μX μY ρ d ↔
      ∀ j : ℕ, j ≤ 2 → RestrictionLowerBound F μX μY ρ
        ((3 / 5 : ℝ) * (1 / 2 : ℝ) ^ j) (d - (j : ℤ)) := by
  constructor
  · intro h j hj
    exact h ⟨j, by omega⟩
  · intro h j
    exact h j.val (by omega)

namespace RestrictionLowerBound

variable [Fintype A] [Fintype B]

/-- Lower-bound profiles survive labelled pullback because the retained
images are large enough and have exactly the same restricted cost. -/
theorem pullback (F : X → Y → Bool) (μX : FiniteLaw X) (μY : FiniteLaw Y)
    (μA : FiniteLaw A) (μB : FiniteLaw B) (f : A → X) (g : B → Y)
    (hf : μA.PushesTo μX f) (hg : μB.PushesTo μY g)
    (a b : ℝ) (c : ℤ) (h : RestrictionLowerBound F μX μY a b c) :
    RestrictionLowerBound (fun x y => F (f x) (g y)) μA μB a b c := by
  intro U V hU hV
  rw [restrictionD_pullback_image]
  exact h (f '' U) (g '' V)
    (hU.trans (μA.prob_le_image μX f hf U))
    (hV.trans (μB.prob_le_image μY g hg V))

/-- Conversely, lift a retained original rectangle by keeping every copy.
The event masses and the restricted protocol complexity are both exact. -/
theorem of_pullback (F : X → Y → Bool) (μX : FiniteLaw X) (μY : FiniteLaw Y)
    (μA : FiniteLaw A) (μB : FiniteLaw B) (f : A → X) (g : B → Y)
    (hf : μA.PushesTo μX f) (hg : μB.PushesTo μY g)
    (hfs : Function.Surjective f) (hgs : Function.Surjective g)
    (a b : ℝ) (c : ℤ)
    (h : RestrictionLowerBound (fun x y => F (f x) (g y)) μA μB a b c) :
    RestrictionLowerBound F μX μY a b c := by
  intro U V hU hV
  have hU' : a ≤ μA.prob (· ∈ f ⁻¹' U) := by
    change a ≤ μA.prob (fun x => f x ∈ U)
    rw [hf (· ∈ U)]
    exact hU
  have hV' : b ≤ μB.prob (· ∈ g ⁻¹' V) := by
    change b ≤ μB.prob (fun y => g y ∈ V)
    rw [hg (· ∈ V)]
    exact hV
  have h' := h (f ⁻¹' U) (g ⁻¹' V) hU' hV'
  rwa [restrictionD_pullback_preimage F f g hfs hgs U V] at h'

theorem pullback_iff (F : X → Y → Bool) (μX : FiniteLaw X) (μY : FiniteLaw Y)
    (μA : FiniteLaw A) (μB : FiniteLaw B) (f : A → X) (g : B → Y)
    (hf : μA.PushesTo μX f) (hg : μB.PushesTo μY g)
    (hfs : Function.Surjective f) (hgs : Function.Surjective g)
    (a b : ℝ) (c : ℤ) :
    RestrictionLowerBound (fun x y => F (f x) (g y)) μA μB a b c ↔
      RestrictionLowerBound F μX μY a b c :=
  ⟨of_pullback F μX μY μA μB f g hf hg hfs hgs a b c,
    pullback F μX μY μA μB f g hf hg a b c⟩

end RestrictionLowerBound

/-- The exact three-level profile is invariant under any surjective
labelled pullback with the prescribed arbitrary-event pushforward laws. -/
theorem restrictionProfile_pullback_iff [Fintype A] [Fintype B]
    (F : X → Y → Bool) (μX : FiniteLaw X) (μY : FiniteLaw Y)
    (μA : FiniteLaw A) (μB : FiniteLaw B) (f : A → X) (g : B → Y)
    (hf : μA.PushesTo μX f) (hg : μB.PushesTo μY g)
    (hfs : Function.Surjective f) (hgs : Function.Surjective g)
    (ρ : ℝ) (d : ℤ) :
    RestrictionProfile (fun x y => F (f x) (g y)) μA μB ρ d ↔
      RestrictionProfile F μX μY ρ d := by
  unfold RestrictionProfile
  apply forall_congr'
  intro j
  exact RestrictionLowerBound.pullback_iff F μX μY μA μB f g hf hg hfs hgs _ _ _

/-- Expanding the profile gives precisely the three bounds printed after
`def:profile`, with no loss when one of the integer bounds is negative. -/
theorem restrictionProfile_three_levels (F : X → Y → Bool)
    (μX : FiniteLaw X) (μY : FiniteLaw Y) (ρ : ℝ) (d : ℤ) :
    RestrictionProfile F μX μY ρ d ↔
      RestrictionLowerBound F μX μY ρ (3 / 5) d ∧
      RestrictionLowerBound F μX μY ρ (3 / 10) (d - 1) ∧
      RestrictionLowerBound F μX μY ρ (3 / 20) (d - 2) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · simpa using h ⟨0, by decide⟩
    · convert h ⟨1, by decide⟩ using 1; norm_num
    · convert h ⟨2, by decide⟩ using 1; norm_num
  · rintro ⟨h0, h1, h2⟩ j
    fin_cases j
    · simpa using h0
    · convert h1 using 1; norm_num
    · convert h2 using 1; norm_num

/-- Common-denominator copies preserve every two-threshold restriction
lower bound, not just the three thresholds in the profile. -/
theorem rationalCopies_restrictionLowerBound_iff
    (μ : PositiveRationalLaw X) (ν : PositiveRationalLaw Y)
    (F : X → Y → Bool) (a b : ℝ) (c : ℤ) :
    RestrictionLowerBound (fun x y => F (μ.forget x) (ν.forget y))
      μ.uniformCopies ν.uniformCopies a b c ↔
    RestrictionLowerBound F μ.toFiniteLaw ν.toFiniteLaw a b c :=
  RestrictionLowerBound.pullback_iff F μ.toFiniteLaw ν.toFiniteLaw
    μ.uniformCopies ν.uniformCopies μ.forget ν.forget
    μ.uniformCopies_prob_preimage ν.uniformCopies_prob_preimage
    μ.forget_surjective ν.forget_surjective a b c

/-- Full profile equivalence under the explicit common-denominator
realization of arbitrary positive rational input laws. -/
theorem rationalCopies_profile_iff
    (μ : PositiveRationalLaw X) (ν : PositiveRationalLaw Y)
    (F : X → Y → Bool) (ρ : ℝ) (d : ℤ) :
    RestrictionProfile (fun x y => F (μ.forget x) (ν.forget y))
      μ.uniformCopies ν.uniformCopies ρ d ↔
    RestrictionProfile F μ.toFiniteLaw ν.toFiniteLaw ρ d :=
  restrictionProfile_pullback_iff F μ.toFiniteLaw ν.toFiniteLaw
    μ.uniformCopies ν.uniformCopies μ.forget ν.forget
    μ.uniformCopies_prob_preimage ν.uniformCopies_prob_preimage
    μ.forget_surjective ν.forget_surjective ρ d

/-- Arbitrary retained interlace rows and full tuples are covered by this
equivalence: the row selector has law `σ`, and the original column tuples
have the prescribed independent law. The retained subsets themselves may
be completely correlated. -/
theorem rationalCopies_interlace_restrictionLowerBound_iff
    (μ : PositiveRationalLaw X) (ν : PositiveRationalLaw Y)
    (F : X → Y → Bool) (q : ℕ) (σ : FiniteLaw (Fin q))
    (a b : ℝ) (c : ℤ) :
    RestrictionLowerBound
      (fullInterlace (fun x y => F (μ.forget x) (ν.forget y)) q)
      (σ.prod μ.uniformCopies) (ν.uniformCopies.iid q) a b c ↔
    RestrictionLowerBound (fullInterlace F q)
      (σ.prod μ.toFiniteLaw) (ν.toFiniteLaw.iid q) a b c :=
  RestrictionLowerBound.pullback_iff (fullInterlace F q)
    (σ.prod μ.toFiniteLaw) (ν.toFiniteLaw.iid q)
    (σ.prod μ.uniformCopies) (ν.uniformCopies.iid q)
    (μ.forgetBlock q) (ν.forgetTuple q)
    (μ.uniformCopies_block_prob_preimage q σ)
    (ν.uniformCopies_iid_prob_preimage q)
    (μ.forgetBlock_surjective q) (ν.forgetTuple_surjective q) a b c

theorem rationalCopies_interlace_profile_iff
    (μ : PositiveRationalLaw X) (ν : PositiveRationalLaw Y)
    (F : X → Y → Bool) (q : ℕ) (σ : FiniteLaw (Fin q))
    (ρ : ℝ) (d : ℤ) :
    RestrictionProfile
      (fullInterlace (fun x y => F (μ.forget x) (ν.forget y)) q)
      (σ.prod μ.uniformCopies) (ν.uniformCopies.iid q) ρ d ↔
    RestrictionProfile (fullInterlace F q)
      (σ.prod μ.toFiniteLaw) (ν.toFiniteLaw.iid q) ρ d :=
  restrictionProfile_pullback_iff (fullInterlace F q)
    (σ.prod μ.toFiniteLaw) (ν.toFiniteLaw.iid q)
    (σ.prod μ.uniformCopies) (ν.uniformCopies.iid q)
    (μ.forgetBlock q) (ν.forgetTuple q)
    (μ.uniformCopies_block_prob_preimage q σ)
    (ν.uniformCopies_iid_prob_preimage q)
    (μ.forgetBlock_surjective q) (ν.forgetTuple_surjective q) ρ d

namespace FiniteLaw

/-- The actual uniform law on `h` new labels, used for further equal
duplication after choosing common denominators. -/
noncomputable def uniformFin (h : ℕ) (hh : 0 < h) : FiniteLaw (Fin h) where
  weight _ := (h : ℝ)⁻¹
  nonneg _ := inv_nonneg.mpr (Nat.cast_nonneg h)
  total := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    exact mul_inv_cancel₀ (by exact_mod_cast hh.ne')

/-- Adding an independent label leaves all original event masses intact. -/
theorem prod_snd_pushesTo {ι : Type*} [Fintype ι]
    (σ : FiniteLaw ι) (μ : FiniteLaw X) : (σ.prod μ).PushesTo μ Prod.snd := by
  intro E
  rw [prod_prob σ μ (fun _ x => E x)]
  rw [← Finset.sum_mul, σ.total, one_mul]

end FiniteLaw

omit [Fintype X] in
/-- Forgetting one of `h` equal new row labels is surjective. -/
theorem uniformDuplication_snd_surjective (h : ℕ) (hh : 0 < h) :
    Function.Surjective (Prod.snd : Fin h × X → X) := by
  intro x
  exact ⟨(⟨0, hh⟩, x), rfl⟩

/-- The new labels multiply the actual carrier size by exactly `h`. -/
theorem uniformDuplication_card (h : ℕ) :
    Fintype.card (Fin h × X) = h * Fintype.card X := by simp

/-- Applied after the common-denominator realization, every new input
still has the same weight, now the reciprocal of `h` times the denominator. -/
theorem uniformCopies_furtherDuplication_weight (μ : PositiveRationalLaw X)
    (h : ℕ) (hh : 0 < h) (z : Fin h × μ.Copies) :
    ((FiniteLaw.uniformFin h hh).prod μ.uniformCopies).weight z =
      ((h * μ.denominator : ℕ) : ℝ)⁻¹ := by
  simp [FiniteLaw.prod, FiniteLaw.uniformFin, PositiveRationalLaw.uniformCopies,
    mul_inv_rev, mul_comm]

theorem uniformCopies_furtherDuplication_card (μ : PositiveRationalLaw X) (h : ℕ) :
    Fintype.card (Fin h × μ.Copies) = h * μ.denominator := by
  simp [μ.card_copies]

/-- The precise extra uniform duplication used for ceiling repair changes
neither the matrix values nor any restriction lower-bound property. -/
theorem uniform_row_duplication_restrictionLowerBound_iff
    (F : X → Y → Bool) (μX : FiniteLaw X) (μY : FiniteLaw Y)
    (h : ℕ) (hh : 0 < h) (a b : ℝ) (c : ℤ) :
    RestrictionLowerBound (fun (x : Fin h × X) y => F x.2 y)
      ((FiniteLaw.uniformFin h hh).prod μX) μY a b c ↔
    RestrictionLowerBound F μX μY a b c :=
  RestrictionLowerBound.pullback_iff F μX μY
    ((FiniteLaw.uniformFin h hh).prod μX) μY Prod.snd id
    (FiniteLaw.prod_snd_pushesTo (FiniteLaw.uniformFin h hh) μX)
    (fun _ => rfl) (uniformDuplication_snd_surjective h hh)
    Function.surjective_id a b c

theorem uniform_row_duplication_profile_iff
    (F : X → Y → Bool) (μX : FiniteLaw X) (μY : FiniteLaw Y)
    (h : ℕ) (hh : 0 < h) (ρ : ℝ) (d : ℤ) :
    RestrictionProfile (fun (x : Fin h × X) y => F x.2 y)
      ((FiniteLaw.uniformFin h hh).prod μX) μY ρ d ↔
    RestrictionProfile F μX μY ρ d :=
  restrictionProfile_pullback_iff F μX μY
    ((FiniteLaw.uniformFin h hh).prod μX) μY Prod.snd id
    (FiniteLaw.prod_snd_pushesTo (FiniteLaw.uniformFin h hh) μX)
    (fun _ => rfl) (uniformDuplication_snd_surjective h hh)
    Function.surjective_id ρ d

/-- The standard uniform-selector full interlace is a specialization of
the arbitrary-selector law theorem, still quantifying over all retained
full-tuple subsets. -/
theorem rationalCopies_uniform_interlace_profile_iff
    (μ : PositiveRationalLaw X) (ν : PositiveRationalLaw Y)
    (F : X → Y → Bool) (q : ℕ) (hq : 0 < q) (ρ : ℝ) (d : ℤ) :
    RestrictionProfile
      (fullInterlace (fun x y => F (μ.forget x) (ν.forget y)) q)
      ((FiniteLaw.uniformFin q hq).prod μ.uniformCopies)
      (ν.uniformCopies.iid q) ρ d ↔
    RestrictionProfile (fullInterlace F q)
      ((FiniteLaw.uniformFin q hq).prod μ.toFiniteLaw)
      (ν.toFiniteLaw.iid q) ρ d :=
  rationalCopies_interlace_profile_iff μ ν F q (FiniteLaw.uniformFin q hq) ρ d

end Paper2

#print axioms Paper2.restrictionD_pullback_image
#print axioms Paper2.restrictionProfile_pullback_iff
#print axioms Paper2.restrictionProfile_three_levels
#print axioms Paper2.rationalCopies_profile_iff
#print axioms Paper2.rationalCopies_interlace_profile_iff
#print axioms Paper2.uniform_row_duplication_profile_iff
#print axioms Paper2.rationalCopies_uniform_interlace_profile_iff
