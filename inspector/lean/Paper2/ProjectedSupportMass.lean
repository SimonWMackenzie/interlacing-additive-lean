import Paper2.SourceSupportStep
import Paper2.RestrictionProfiles

/-!
# Size of the actual selector image of a raw row support

Frozen v12, Section 5, `res:two-stream`, lines 134--201. Original rows
may have the same selector and different answers to the next row query.
Their child images cover the parent image but need not be disjoint.
Only subadditivity is used for half-mass routing. Ambient raw-row loss
is bounded separately by the exact selector pushforward.
-/

namespace Paper2.ProjectedSupportStep

variable {W S : Type*} [Fintype S]

noncomputable abbrev fibre := @SourceSupportStep.fibre
abbrev mem_fibre := @SourceSupportStep.mem_fibre
abbrev fibre_subset := @SourceSupportStep.fibre_subset

/-- Measured selector image of the original retained row labels. -/
noncomputable def mass (μ : FiniteLaw S) (σ : W → S) (F : Finset W) : ℝ :=
  μ.prob (fun s => ∃ w ∈ F, σ w = s)

theorem mass_nonneg (μ : FiniteLaw S) (σ : W → S) (F : Finset W) :
    0 ≤ mass μ σ F := μ.prob_nonneg _

theorem mass_le_one (μ : FiniteLaw S) (σ : W → S) (F : Finset W) :
    mass μ σ F ≤ 1 := μ.prob_le_one _

@[simp] theorem mass_empty (μ : FiniteLaw S) (σ : W → S) :
    mass μ σ ∅ = 0 := by simp [mass]

theorem mass_mono (μ : FiniteLaw S) (σ : W → S) {F G : Finset W}
    (h : F ⊆ G) : mass μ σ F ≤ mass μ σ G := by
  apply μ.prob_mono
  rintro s ⟨w, hw, hs⟩
  exact ⟨w, h hw, hs⟩

omit [Fintype S] in
/-- Equality of image events, without a disjointness assertion. -/
theorem image_fibres (σ : W → S) (F : Finset W) (query : W → Bool) (s : S) :
    (∃ w ∈ F, σ w = s) ↔
      (∃ w ∈ fibre F query false, σ w = s) ∨
        (∃ w ∈ fibre F query true, σ w = s) := by
  constructor
  · rintro ⟨w, hw, hs⟩
    cases hb : query w
    · exact Or.inl ⟨w, (mem_fibre F query false w).mpr ⟨hw, hb⟩, hs⟩
    · exact Or.inr ⟨w, (mem_fibre F query true w).mpr ⟨hw, hb⟩, hs⟩
  · rintro (⟨w, hw, hs⟩ | ⟨w, hw, hs⟩)
    · exact ⟨w, fibre_subset F query false hw, hs⟩
    · exact ⟨w, fibre_subset F query true hw, hs⟩

/-- Child images may overlap, so this is an inequality, not a partition. -/
theorem mass_cover (μ : FiniteLaw S) (σ : W → S) (F : Finset W)
    (query : W → Bool) :
    mass μ σ F ≤ mass μ σ (fibre F query false) +
      mass μ σ (fibre F query true) := by
  classical
  unfold mass FiniteLaw.prob
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro s _
  dsimp only
  have he := image_fibres σ F query s
  simp only [he]
  by_cases h0 : ∃ w ∈ fibre F query false, σ w = s <;>
    by_cases h1 : ∃ w ∈ fibre F query true, σ w = s <;>
    simp only [h0, h1, true_or, or_true, false_or, or_false, ite_true, ite_false,
      add_zero, zero_add] <;> linarith [μ.nonneg s]

/-- A single fixed choice; false wins projected-mass ties. -/
noncomputable def heavyBit (μ : FiniteLaw S) (σ : W → S) (F : Finset W)
    (query : W → Bool) : Bool :=
  if mass μ σ (fibre F query true) ≤ mass μ σ (fibre F query false)
    then false else true

theorem heavy_ge_other (μ : FiniteLaw S) (σ : W → S) (F : Finset W)
    (query : W → Bool) :
    mass μ σ (fibre F query (!(heavyBit μ σ F query))) ≤
      mass μ σ (fibre F query (heavyBit μ σ F query)) := by
  classical
  unfold heavyBit
  split_ifs with h <;> simp only [Bool.not_false, Bool.not_true]
  · exact h
  · exact (lt_of_not_ge h).le

theorem mass_cover_heavy (μ : FiniteLaw S) (σ : W → S) (F : Finset W)
    (query : W → Bool) :
    mass μ σ F ≤ mass μ σ (fibre F query (heavyBit μ σ F query)) +
      mass μ σ (fibre F query (!(heavyBit μ σ F query))) := by
  cases heavyBit μ σ F query <;> simpa [add_comm] using mass_cover μ σ F query

theorem heavy_floor (μ : FiniteLaw S) (σ : W → S) (F : Finset W)
    (query : W → Bool) (t : ℝ) (h : 2 * t ≤ mass μ σ F) :
    t ≤ mass μ σ (fibre F query (heavyBit μ σ F query)) := by
  have hp := mass_cover_heavy μ σ F query
  have hg := heavy_ge_other μ σ F query
  linarith

/-- Both actual child images meet the next floor. -/
def Both (μ : FiniteLaw S) (σ : W → S) (F : Finset W)
    (query : W → Bool) (t : ℝ) : Prop :=
  t ≤ mass μ σ (fibre F query false) ∧ t ≤ mass μ σ (fibre F query true)

theorem other_lt_of_not_both (μ : FiniteLaw S) (σ : W → S) (F : Finset W)
    (query : W → Bool) (t : ℝ) (h : ¬ Both μ σ F query t) :
    mass μ σ (fibre F query (!(heavyBit μ σ F query))) < t := by
  by_contra hn
  have ho := le_of_not_gt hn
  have hh := ho.trans (heavy_ge_other μ σ F query)
  apply h
  cases hb : heavyBit μ σ F query <;>
    simp only [hb, Bool.not_false, Bool.not_true] at ho hh
  · exact ⟨hh, ho⟩
  · exact ⟨ho, hh⟩

/-- Exact pushforward bounds raw discarded mass by its image mass. The
raw law is the original ambient law, not conditional on this support. -/
theorem raw_mass_le [Fintype W] (κ : FiniteLaw W) (μ : FiniteLaw S)
    (σ : W → S) (hσ : κ.PushesTo μ σ) (F : Finset W) :
    SourceSupportStep.mass κ F ≤ mass μ σ F := by
  exact FiniteLaw.prob_le_image κ μ σ hσ {w | w ∈ F}

end Paper2.ProjectedSupportStep
