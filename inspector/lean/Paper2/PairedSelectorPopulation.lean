import Paper2.SourceDeficiency
import Paper2.PairedSupportStepCounts

/-!
# Initial ordinary and foreign fibre populations

Frozen v12 Section 5, `res:paired`, initial population calculation.
The zero-deletion case is included. Strict pair excess comes from the
explicit `2/q` slack, not from an unstated positive deletion allowance.
-/

namespace Paper2.PairedSelectorPopulation

open scoped BigOperators

variable {I W : Type*}

theorem deficient_card_mul_le [Fintype I] [Nonempty I]
    (p : I → ℝ) (t ε : ℝ) (hp : ∀ i, p i ≤ 1)
    (havg : 1 - ε ≤ (Fintype.card I : ℝ)⁻¹ * ∑ i, p i) :
    ((Finset.univ.filter fun i => p i < t).card : ℝ) * (1 - t) ≤
      ε * Fintype.card I := by
  classical
  let B := Finset.univ.filter fun i => p i < t
  have hN : (0 : ℝ) < Fintype.card I := Nat.cast_pos.mpr Fintype.card_pos
  have hsum : (∑ i, (1 - p i)) ≤ ε * Fintype.card I := by
    have hmul := mul_le_mul_of_nonneg_left havg hN.le
    have hid : (Fintype.card I : ℝ) *
        ((Fintype.card I : ℝ)⁻¹ * ∑ i, p i) = ∑ i, p i := by
      rw [← mul_assoc, mul_inv_cancel₀ hN.ne', one_mul]
    rw [hid] at hmul
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, mul_one]
    nlinarith
  have hlocal : (B.card : ℝ) * (1 - t) ≤ ∑ i ∈ B, (1 - p i) := by
    have hh := Finset.sum_le_sum (s := B) (fun i hi =>
      (sub_lt_sub_left (Finset.mem_filter.mp hi).2 1).le)
    simpa only [Finset.sum_const, nsmul_eq_mul] using hh
  have hsub : (∑ i ∈ B, (1 - p i)) ≤ ∑ i, (1 - p i) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ B)
      (fun i _ _ => sub_nonneg.mpr (hp i))
  exact hlocal.trans (hsub.trans hsum)

theorem good_card_mul_ge [Fintype I] [Nonempty I]
    (p : I → ℝ) (t δ : ℝ) (hp : ∀ i, p i ≤ 1)
    (havg : δ ≤ (Fintype.card I : ℝ)⁻¹ * ∑ i, p i) :
    (Fintype.card I : ℝ) * (δ - t) ≤
      ((Finset.univ.filter fun i => t ≤ p i).card : ℝ) * (1 - t) := by
  classical
  let G := Finset.univ.filter fun i => t ≤ p i
  have hN : (0 : ℝ) < Fintype.card I := Nat.cast_pos.mpr Fintype.card_pos
  have havg' : (Fintype.card I : ℝ) * δ ≤ ∑ i, p i := by
    have h := mul_le_mul_of_nonneg_left havg hN.le
    simpa only [← mul_assoc, mul_inv_cancel₀ hN.ne', one_mul] using h
  have hbound : (∑ i, p i) ≤ (G.card : ℝ) * (1 - t) + Fintype.card I * t := by
    have hh : (∑ i, p i) ≤ ∑ i : I, ((if i ∈ G then 1 - t else 0) + t) := by
      apply Finset.sum_le_sum
      intro i _
      by_cases hi : i ∈ G
      · simpa [hi] using hp i
      · have hlt : p i < t := by simpa [G] using hi
        simpa [hi] using hlt.le
    simpa only [Finset.sum_add_distrib, ← Finset.sum_filter, Finset.sum_const,
      Finset.filter_mem_eq_inter, Finset.univ_inter, Finset.card_univ,
      nsmul_eq_mul] using hh
  nlinarith

variable [Fintype W]

noncomputable def fibre (U : Set (I × W)) (i : I) : Finset W := by
  classical
  exact Finset.univ.filter fun w => (i, w) ∈ U

@[simp] theorem mem_fibre (U : Set (I × W)) (i : I) (w : W) :
    w ∈ fibre U i ↔ (i, w) ∈ U := by
  classical
  simp [fibre]

noncomputable def good [Fintype I] (μ : FiniteLaw W) (U : Set (I × W))
    (t : ℝ) : Finset I := by
  classical
  exact Finset.univ.filter fun i => t ≤ μ.prob (fun w => (i, w) ∈ U)

@[simp] theorem mem_good [Fintype I] (μ : FiniteLaw W) (U : Set (I × W))
    (t : ℝ) (i : I) :
    i ∈ good μ U t ↔ t ≤ μ.prob (fun w => (i, w) ∈ U) := by
  classical
  simp [good]

/-- The original column law is uniform on the coordinate and unchanged
on its word. No conditional or renormalized support law is introduced. -/
noncomputable def columnLaw [Fintype I] [Nonempty I]
    (μ : PositiveRationalLaw W) : PositiveRationalLaw (I × W) :=
  (PositiveRationalLaw.uniform I).prod μ

theorem column_average [Fintype I] [Nonempty I]
    (μ : PositiveRationalLaw W) (U : Set (I × W)) :
    (columnLaw μ).toFiniteLaw.prob (· ∈ U) =
      (Fintype.card I : ℝ)⁻¹ * ∑ i, μ.toFiniteLaw.prob (fun w => (i, w) ∈ U) :=
  SourceDeficiency.item_average μ (· ∈ U)

/-- Sufficient ordinary and foreign mass forces more than three pairs
per missing ordinary coordinate. This is valid also when `ε = 0`. -/
theorem pair_excess [Fintype I] [Nonempty I] [DecidableEq I]
    (μ : PositiveRationalLaw W) (O F : Set (I × W)) (t ε δ : ℝ)
    (hO : 1 - ε ≤ (columnLaw μ).toFiniteLaw.prob (· ∈ O))
    (hF : δ ≤ (columnLaw μ).toFiniteLaw.prob (· ∈ F))
    (hδ : δ ≤ 1)
    (hslack : t + 5 * ε + 2 / Fintype.card I ≤ δ) :
    0 ≤ ε ∧ t < 1 ∧
      3 * (Finset.univ \ good μ.toFiniteLaw O t).card <
        (good μ.toFiniteLaw O t ∩ good μ.toFiniteLaw F t).card := by
  classical
  let GO := good μ.toFiniteLaw O t
  let GF := good μ.toFiniteLaw F t
  let B := Finset.univ \ GO
  let P := GO ∩ GF
  have hN : (0 : ℝ) < Fintype.card I := Nat.cast_pos.mpr Fintype.card_pos
  have hε : 0 ≤ ε := by
    have := (columnLaw μ).toFiniteLaw.prob_le_one (· ∈ O)
    linarith
  have ht : t < 1 := by
    have := div_pos (show (0 : ℝ) < 2 by norm_num) hN
    linarith
  refine ⟨hε, ht, ?_⟩
  have hBdef : B = Finset.univ.filter
      (fun i => μ.toFiniteLaw.prob (fun w => (i, w) ∈ O) < t) := by
    ext i
    simp [B, GO]
  have hb : (B.card : ℝ) * (1 - t) ≤ ε * Fintype.card I := by
    rw [hBdef]
    apply deficient_card_mul_le _ t ε (fun _ => μ.toFiniteLaw.prob_le_one _)
    simpa only [column_average] using hO
  have hf : (Fintype.card I : ℝ) * (δ - t) ≤ (GF.card : ℝ) * (1 - t) := by
    apply good_card_mul_ge _ t δ (fun _ => μ.toFiniteLaw.prob_le_one _)
    simpa only [column_average] using hF
  have hsub : GF ⊆ P ∪ B := by
    intro i hi
    by_cases h : i ∈ GO
    · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨h, hi⟩)
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨Finset.mem_univ i, h⟩)
  have hcard : GF.card ≤ P.card + B.card :=
    (Finset.card_le_card hsub).trans (Finset.card_union_le P B)
  change 3 * B.card < P.card
  by_contra hn
  have hle : GF.card ≤ 4 * B.card := by omega
  have hleR : (GF.card : ℝ) ≤ 4 * B.card := by exact_mod_cast hle
  have hh := mul_le_mul_of_nonneg_right hleR (sub_nonneg.mpr ht.le)
  have hslack' := mul_le_mul_of_nonneg_left hslack hN.le
  have hid : (Fintype.card I : ℝ) * (2 / Fintype.card I) = 2 := by
    field_simp
  have hεN := mul_nonneg hε hN.le
  nlinarith

section Initial

variable [Fintype I] [DecidableEq I]

noncomputable def bad (μ : FiniteLaw W) (O : Set (I × W)) (t : ℝ) : Finset I :=
  Finset.univ \ good μ O t

noncomputable def pairs (μ : FiniteLaw W) (O F : Set (I × W)) (t : ℝ) : Finset I :=
  good μ O t ∩ good μ F t

noncomputable def singles (μ : FiniteLaw W) (O F : Set (I × W)) (t : ℝ) :
    Finset (Bool × I) :=
  (good μ O t \ good μ F t).image (fun i => (false, i))

noncomputable def support (O F : Set (I × W)) (a : Bool × I) : Finset W :=
  if a.1 then fibre F a.2 else fibre O a.2

def columns (O F : Set (I × W)) : Set ((Bool × I) × W) :=
  {c | if c.1.1 then (c.1.2, c.2) ∈ F else (c.1.2, c.2) ∈ O}

@[simp] theorem mem_pairs (μ : FiniteLaw W) (O F : Set (I × W)) (t : ℝ) (i : I) :
    i ∈ pairs μ O F t ↔ i ∈ good μ O t ∧ i ∈ good μ F t := by
  simp [pairs]

@[simp] theorem mem_singles (μ : FiniteLaw W) (O F : Set (I × W)) (t : ℝ)
    (a : Bool × I) :
    a ∈ singles μ O F t ↔ a.1 = false ∧ a.2 ∈ good μ O t ∧ a.2 ∉ good μ F t := by
  rcases a with ⟨tag, i⟩
  cases tag <;> simp [singles]

theorem initial_valid (μ : FiniteLaw W) (O F : Set (I × W)) (t : ℝ) :
    PairedSupportStep.Valid (singles μ O F t) (pairs μ O F t) := by
  intro i hi tag hs
  have hp := (mem_pairs μ O F t i).mp hi
  have h := (mem_singles μ O F t (tag, i)).mp hs
  exact h.2.2 hp.2

theorem initial_count (μ : FiniteLaw W) (O F : Set (I × W)) (t : ℝ) :
    (singles μ O F t).card + (pairs μ O F t).card + (bad μ O t).card = Fintype.card I := by
  have hinj : Function.Injective (fun i : I => (false, i)) := by
    intro i j h
    exact congrArg Prod.snd h
  rw [singles, Finset.card_image_of_injective _ hinj, pairs,
    Finset.card_sdiff_add_card_inter]
  simpa [bad, Nat.add_comm] using
    Finset.card_sdiff_add_card_eq_card (Finset.subset_univ (good μ O t))

theorem initial_floor (μ : FiniteLaw W) (O F : Set (I × W)) (t : ℝ) :
    ∀ a ∈ PairedSupportStep.active (singles μ O F t) (pairs μ O F t),
      t ≤ SourceSupportStep.mass μ (support O F a) := by
  intro a ha
  rcases (PairedSupportStep.mem_active _ _ a).mp ha with hs | hp
  · obtain ⟨ht, ho, _⟩ := (mem_singles μ O F t a).mp hs
    simpa only [support, ht, Bool.false_eq_true, ↓reduceIte,
      SourceSupportStep.mass, mem_fibre] using (mem_good μ O t a.2).mp ho
  · obtain ⟨ho, hf⟩ := (mem_pairs μ O F t a.2).mp hp
    cases ht : a.1
    · simpa only [support, ht, Bool.false_eq_true, ↓reduceIte,
        SourceSupportStep.mass, mem_fibre] using (mem_good μ O t a.2).mp ho
    · simpa only [support, ht, ↓reduceIte, SourceSupportStep.mass, mem_fibre]
        using (mem_good μ F t a.2).mp hf

omit [Fintype I] [DecidableEq I] in
theorem initial_reaches (O F : Set (I × W)) (a : Bool × I) (w : W)
    (hw : w ∈ support O F a) : (a, w) ∈ columns O F := by
  cases ht : a.1 <;> simpa [support, columns, ht] using hw

end Initial

end Paper2.PairedSelectorPopulation
