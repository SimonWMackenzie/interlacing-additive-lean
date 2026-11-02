import CurrentAdditive.IndexedIncomingBlockCount
import CurrentAdditive.IndexedTemplateSection

/-! Appendix I `det:incoming`: a good-flag section of the actual triple
source and its selected original outer positions. -/

namespace CurrentAdditive.DeterministicIndexedMatrix

open Paper2
open scoped BigOperators

variable {I X Y : Type*} [Fintype I] [Fintype X] [Fintype Y]
  [DecidableEq I] [DecidableEq X] [DecidableEq Y]
  {D q₁ q₂ s : ℕ} [NeZero s] [NeZero q₁] [NeZero q₂]
  {μX : PositiveRationalLaw X} {μY : PositiveRationalLaw Y}
  (src : Sources (D := D) (q₁ := q₁) (q₂ := q₂) (s := s) μX μY)
  {μI : PositiveRationalLaw I} {w : ℕ}
  (streams : Sources.InternalStreams src μI w)

/-- Enumeration of an original set of outer positions, with no quotient of
source labels. -/
noncomputable def enumerateGroup (V : Finset (Fin w)) : Fin V.card → Fin w :=
  fun t => (V.equivFin.symm t).val

theorem enumerateGroup_injective (V : Finset (Fin w)) :
    Function.Injective (enumerateGroup V) := by
  intro a b hab
  apply V.equivFin.symm.injective
  apply Subtype.ext
  exact hab

theorem enumerateGroup_mem (V : Finset (Fin w)) (t : Fin V.card) :
    enumerateGroup V t ∈ V := (V.equivFin.symm t).property

/-- The fixed metadata label's template bin at an original outer position.
The fallback value is used only outside the good template set. -/
def templateBin (md : streams.metadataStream.Label) (i : Fin w) : Fin s :=
  match streams.metadataStream.decode md i with
  | .inl p => p
  | .inr _ => 0

theorem templateBin_eq_of_flag (md : streams.metadataStream.Label)
    (i : Fin w)
    (hflag : isTemplateFlag (streams.metadataStream.decode md i) = true) :
    streams.metadataStream.decode md i =
      .inl (templateBin src streams md i) := by
  cases h : streams.metadataStream.decode md i with
  | inl p => simp [templateBin, h]
  | inr j => simp [isTemplateFlag, h] at hflag

/-- The flags selected from a density group retain at least half of its
original positions; after fixing both complete nonselector streams, the
selector-index event still has ambient mass at least `θ/4`. -/
theorem incoming_template_group_section
    (V : Finset (Fin w))
    (Ystar : Set (streams.metadataStream.Label ×
      (streams.baseStream.Label × streams.selectorStream.Label)))
    (θ : ℝ) (hθ : 0 < θ) (hD : 8*256 ≤ D)
    (hYstar : θ/2 ≤ streams.law.toFiniteLaw.prob (· ∈ Ystar))
    (hguard : 2 * ((64 : ℝ) * V.card) ^ 128 /
      (((255 / 256 : ℝ) - 1/2) * V.card) ^ 256 ≤ θ/4) :
    ∃ md : streams.metadataStream.Label,
      ∃ base : streams.baseStream.Label,
      ∃ VG : Finset (Fin w),
        VG ⊆ V ∧
        (V.card : ℝ) / 2 ≤ VG.card ∧
        (∀ i ∈ VG, isTemplateFlag
          (streams.metadataStream.decode md i) = true) ∧
        θ/4 ≤ streams.selectorStream.law.toFiniteLaw.prob
          (fun sel => (md, (base, sel)) ∈ Ystar) := by
  classical
  let e := enumerateGroup V
  obtain ⟨md, hflags, base, hsection⟩ :=
    incoming_complete_template_section src streams e
      (enumerateGroup_injective V) Ystar θ hθ hD hYstar hguard
  let G : Finset (Fin V.card) := Finset.univ.filter
    (fun t => isTemplateFlag (streams.metadataStream.decode md (e t)))
  let VG : Finset (Fin w) := G.image e
  have hGcard : (G.card : ℝ) =
      ∑ t : Fin V.card,
        if isTemplateFlag (streams.metadataStream.decode md (e t))
        then (1 : ℝ) else 0 := by
    simp [G, ← Finset.sum_ite]
  have hVGcard : VG.card = G.card :=
    Finset.card_image_of_injective G (enumerateGroup_injective V)
  refine ⟨md, base, VG, ?_, ?_, ?_, hsection⟩
  · intro i hi
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hi
    exact enumerateGroup_mem V t
  · rw [hVGcard]
    exact hflags.trans_eq hGcard.symm
  · intro i hi
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hi
    exact (Finset.mem_filter.mp ht).2

#print axioms incoming_template_group_section

end CurrentAdditive.DeterministicIndexedMatrix
