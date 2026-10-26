import Paper2.SourceLaws

/-!
# Few deficient coordinates in an actual retained template family

Frozen v12 Section 4, `src:near-full`, the paragraph beginning
"Let A_j be the dominant template set". Projections below are actual images
of the same retained, arbitrarily correlated template event. The ambient law
is precisely `SourceLaws.templateLaw`, not a separately assumed product bound.

An elementary geometric-power bound replaces the manuscript's exponential
estimate: mass greater than `1/8` already suffices for the required strict
`8*q₁` bound, so in particular the stated mass greater than `0.998` suffices.
This component does not prove the preceding protocol separation or the later
collision/frontier argument.
-/

namespace Paper2.SourceDeficiencyTemplate

open scoped BigOperators
open SourceMatrix

variable {X : Type*} [Fintype X] {q₁ q₂ : ℕ}

/-- Actual image of the retained template family at one outer coordinate. -/
def projectedAt (A : Template q₁ q₂ X → Prop) (α : Fin q₂)
    (z : InnerRow q₁ X) : Prop := ∃ t, A t ∧ t α = z

/-- Some coordinate-labelled base-row block has less than one eighth left. -/
def Deficient (μ : PositiveRationalLaw X) (A : Template q₁ q₂ X → Prop)
    (α : Fin q₂) : Prop :=
  ∃ r : Fin q₁, μ.toFiniteLaw.prob (fun x => projectedAt A α (r, x)) < 1 / 8

noncomputable def deficientCoordinates (μ : PositiveRationalLaw X)
    (A : Template q₁ q₂ X → Prop) : Finset (Fin q₂) := by
  classical
  exact Finset.univ.filter (Deficient μ A)

@[simp] theorem mem_deficientCoordinates (μ : PositiveRationalLaw X)
    (A : Template q₁ q₂ X → Prop) (α : Fin q₂) :
    α ∈ deficientCoordinates μ A ↔ Deficient μ A α := by
  classical
  simp [deficientCoordinates]

/-- The actual threshold from the source schedule may be smaller than `1/8`. -/
noncomputable def deficientAt (μ : PositiveRationalLaw X)
    (A : Template q₁ q₂ X → Prop) (xcap : ℝ) : Finset (Fin q₂) := by
  classical
  exact Finset.univ.filter (fun α =>
    ∃ r : Fin q₁, μ.toFiniteLaw.prob (fun x => projectedAt A α (r, x)) < xcap)

@[simp] theorem mem_deficientAt (μ : PositiveRationalLaw X)
    (A : Template q₁ q₂ X → Prop) (xcap : ℝ) (α : Fin q₂) :
    α ∈ deficientAt μ A xcap ↔
      ∃ r : Fin q₁, μ.toFiniteLaw.prob (fun x => projectedAt A α (r, x)) < xcap := by
  classical
  simp [deficientAt]

theorem deficientAt_subset (μ : PositiveRationalLaw X)
    (A : Template q₁ q₂ X → Prop) (xcap : ℝ) (hxcap : xcap ≤ 1 / 8) :
    deficientAt μ A xcap ⊆ deficientCoordinates μ A := by
  intro α hα
  obtain ⟨r, hr⟩ := (mem_deficientAt μ A xcap α).mp hα
  exact (mem_deficientCoordinates μ A α).mpr ⟨r, hr.trans_le hxcap⟩

theorem block_mass_ge_of_not_mem (μ : PositiveRationalLaw X)
    (A : Template q₁ q₂ X → Prop) (xcap : ℝ) (α : Fin q₂)
    (hα : α ∉ deficientAt μ A xcap) (r : Fin q₁) :
    xcap ≤ μ.toFiniteLaw.prob (fun x => projectedAt A α (r, x)) := by
  by_contra! h
  exact hα ((mem_deficientAt μ A xcap α).mpr ⟨r, h⟩)

variable [NeZero q₁]

/-- One poor base-row block removes at least `7/(8*q₁)` of the actual
uniform-coordinate/base-row marginal. -/
theorem projection_mass_le (μ : PositiveRationalLaw X)
    (A : Template q₁ q₂ X → Prop) (α : Fin q₂) (hα : Deficient μ A α) :
    ((PositiveRationalLaw.uniform (Fin q₁)).prod μ).toFiniteLaw.prob
      (projectedAt A α) ≤ 1 - 7 / (8 * (q₁ : ℝ)) := by
  classical
  obtain ⟨r, hr⟩ := hα
  let p : Fin q₁ → ℝ := fun i => μ.toFiniteLaw.prob (fun x => projectedAt A α (i, x))
  have hsum : ∑ i, p i ≤ (q₁ : ℝ) - 7 / 8 := by
    calc
      _ ≤ ∑ i : Fin q₁, (1 - if i = r then (7 / 8 : ℝ) else 0) := by
        apply Finset.sum_le_sum
        intro i _
        by_cases hi : i = r
        · subst i
          simp only [↓reduceIte]
          dsimp [p]
          linarith
        · simp only [hi, ↓reduceIte, sub_zero]
          exact μ.toFiniteLaw.prob_le_one _
      _ = _ := by simp [Finset.sum_sub_distrib]
  have hq : (0 : ℝ) < q₁ := by exact_mod_cast NeZero.pos q₁
  rw [PositiveRationalLaw.toFiniteLaw_prod]
  change ((PositiveRationalLaw.uniform (Fin q₁)).toFiniteLaw.prod μ.toFiniteLaw).prob
    (fun z => projectedAt A α (z.1, z.2)) ≤ _
  rw [FiniteLaw.prod_prob _ _ (fun i x => projectedAt A α (i, x))]
  simp only [PositiveRationalLaw.toFiniteLaw, PositiveRationalLaw.uniform,
    Fintype.card_fin, Rat.cast_inv, Rat.cast_natCast]
  change (∑ i : Fin q₁, (q₁ : ℝ)⁻¹ * p i) ≤ _
  rw [← Finset.mul_sum]
  calc
    _ ≤ (q₁ : ℝ)⁻¹ * ((q₁ : ℝ) - 7 / 8) :=
      mul_le_mul_of_nonneg_left hsum (inv_nonneg.mpr hq.le)
    _ = _ := by field_simp

/-- The actual retained family lies inside the independent product of its
coordinate projections. Its own membership predicate may correlate all inputs. -/
theorem retained_mass_le_power (μ : PositiveRationalLaw X)
    (A : Template q₁ q₂ X → Prop) :
    (SourceLaws.templateLaw μ q₁ q₂).toFiniteLaw.prob A ≤
      (1 - 7 / (8 * (q₁ : ℝ))) ^ (deficientCoordinates μ A).card := by
  classical
  let ν := ((PositiveRationalLaw.uniform (Fin q₁)).prod μ).toFiniteLaw
  let D := deficientCoordinates μ A
  let E : Fin q₂ → InnerRow q₁ X → Prop := fun α z =>
    if α ∈ D then projectedAt A α z else True
  rw [SourceLaws.templateLaw, PositiveRationalLaw.toFiniteLaw_iid]
  calc
    _ ≤ (ν.iid q₂).prob (fun t => ∀ α, E α (t α)) := by
      apply FiniteLaw.prob_mono
      intro t ht α
      dsimp [E]
      split_ifs
      · exact ⟨t, ht, rfl⟩
    _ = ∏ α, ν.prob (E α) := FiniteLaw.iid_prob_coordinatewise ν q₂ E
    _ ≤ ∏ α : Fin q₂, if α ∈ D then (1 - 7 / (8 * (q₁ : ℝ))) else 1 := by
      apply Finset.prod_le_prod
      · intro α _
        exact ν.prob_nonneg _
      · intro α _
        by_cases hα : α ∈ D
        · simp only [E, hα, ↓reduceIte]
          apply projection_mass_le μ A α
          exact (Finset.mem_filter.mp hα).2
        · simp only [E, hα, ↓reduceIte, FiniteLaw.prob_true]
          exact le_rfl
    _ = _ := by
      rw [Finset.prod_ite_mem_eq]
      simp [D]

/-- Elementary reciprocal bound for a geometric power. -/
theorem geometric_power_bound (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (n : ℕ) :
    (1 + (n : ℝ) * (1 - p)) * p ^ n ≤ 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hmul := mul_le_mul_of_nonneg_right ih hp
    have hpow : p ^ (n + 1) ≤ 1 := pow_le_one₀ hp hp1
    have hterm := mul_le_mul_of_nonneg_left hpow (sub_nonneg.mpr hp1)
    simp only [Nat.cast_add, Nat.cast_one, pow_succ] at *
    nlinarith

/-- Stronger finite form of the manuscript's deficient-coordinate bound. -/
theorem deficient_card_lt_of_mass_gt_eighth (μ : PositiveRationalLaw X)
    (A : Template q₁ q₂ X → Prop)
    (hA : (1 / 8 : ℝ) < (SourceLaws.templateLaw μ q₁ q₂).toFiniteLaw.prob A) :
    (deficientCoordinates μ A).card < 8 * q₁ := by
  by_contra! hlarge
  have hq : (0 : ℝ) < q₁ := by exact_mod_cast NeZero.pos q₁
  have hq1 : (1 : ℝ) ≤ q₁ := by exact_mod_cast NeZero.pos q₁
  let p : ℝ := 1 - 7 / (8 * (q₁ : ℝ))
  have hp : 0 ≤ p := by
    dsimp [p]
    apply sub_nonneg.mpr
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 8 * q₁)).mpr
    nlinarith
  have hp1 : p ≤ 1 := by
    dsimp [p]
    exact sub_le_self _ (by positivity)
  have hc : (8 : ℝ) * q₁ ≤ (deficientCoordinates μ A).card := by exact_mod_cast hlarge
  have hscale : 7 ≤ ((deficientCoordinates μ A).card : ℝ) * (1 - p) := by
    dsimp [p]
    rw [sub_sub_cancel]
    have := mul_le_mul_of_nonneg_right hc
      (by positivity : 0 ≤ (7 : ℝ) / (8 * q₁))
    have he : (8 : ℝ) * q₁ * (7 / (8 * q₁)) = 7 := by field_simp
    rwa [he] at this
  have hpower := geometric_power_bound p hp hp1 (deficientCoordinates μ A).card
  have hnonneg := pow_nonneg hp (deficientCoordinates μ A).card
  have hmass := retained_mass_le_power μ A
  change (SourceLaws.templateLaw μ q₁ q₂).toFiniteLaw.prob A ≤ p ^ _ at hmass
  nlinarith

/-- The exact high-mass hypothesis used for a dominant template branch. -/
theorem deficient_card_lt (μ : PositiveRationalLaw X)
    (A : Template q₁ q₂ X → Prop)
    (hA : (998 / 1000 : ℝ) < (SourceLaws.templateLaw μ q₁ q₂).toFiniteLaw.prob A) :
    (deficientCoordinates μ A).card < 8 * q₁ := by
  apply deficient_card_lt_of_mass_gt_eighth μ A
  linarith

/-- Fewer than `8*q₁` outer coordinates are deficient at the actual public
threshold, with no correlation restriction on the retained templates. -/
theorem deficientAt_card_lt (μ : PositiveRationalLaw X)
    (A : Template q₁ q₂ X → Prop) (xcap : ℝ) (hxcap : xcap ≤ 1 / 8)
    (hA : (998 / 1000 : ℝ) < (SourceLaws.templateLaw μ q₁ q₂).toFiniteLaw.prob A) :
    (deficientAt μ A xcap).card < 8 * q₁ :=
  (Finset.card_le_card (deficientAt_subset μ A xcap hxcap)).trans_lt
    (deficient_card_lt μ A hA)

end Paper2.SourceDeficiencyTemplate

#print axioms Paper2.SourceDeficiencyTemplate.projection_mass_le
#print axioms Paper2.SourceDeficiencyTemplate.retained_mass_le_power
#print axioms Paper2.SourceDeficiencyTemplate.deficient_card_lt
#print axioms Paper2.SourceDeficiencyTemplate.deficientAt_card_lt
