import Paper2.TwoStreamRawRows

/-!
# The initial supports derived from original retained rows

Frozen v12, Section 5, `res:two-stream`. Ordinary supports consist of all
retained original rows in their physical bin. The distinguished support
uses the original paired labels. Entry identities for paired rows need
hold only on the initially retained paired set, not outside that set.
-/

namespace Paper2.TwoStreamOriginalInputs

open TwoStreamRawRows

variable {E Rw S : Type*} [Fintype E] [Fintype Rw] [Fintype S] {s : ℕ}

noncomputable def binRows (R : Set Rw) (bin : Rw → Fin s) (i : Fin s) :
    Finset Rw := by
  classical
  exact Finset.univ.filter (fun r => r ∈ R ∧ bin r = i)

@[simp] theorem mem_binRows (R : Set Rw) (bin : Rw → Fin s) (i : Fin s) (r : Rw) :
    r ∈ binRows R bin i ↔ r ∈ R ∧ bin r = i := by
  classical
  simp [binRows]

theorem binRows_image (R : Set Rw) (bin : Rw → Fin s)
    (selector : Rw → S) (i : Fin s) :
    selector '' (binRows R bin i : Set Rw) =
      {z | ∃ r ∈ R, bin r = i ∧ selector r = z} := by
  ext z
  simp only [Set.mem_image, Finset.mem_coe, mem_binRows, Set.mem_setOf_eq]
  constructor
  · rintro ⟨r, ⟨hr, hi⟩, hz⟩
    exact ⟨r, hr, hi, hz⟩
  · rintro ⟨r, hr, hi, hz⟩
    exact ⟨r, ⟨hr, hi⟩, hz⟩

theorem supports_bin (R : Set Rw) (bin : Rw → Fin s)
    (ι : E → Rw) (star : Fin s) (P0 : Finset E)
    (hstar : ∀ e ∈ P0, bin (ι e) = star) :
    ∀ i w, w ∈ initialSupport star P0 (binRows R bin) i →
      bin (rawInput ι w) = i := by
  apply initialSupport_bin ι bin star P0 (binRows R bin) hstar
  intro i r hr
  exact ((mem_binRows R bin i r).mp hr).2

theorem supports_retained (R : Set Rw) (bin : Rw → Fin s)
    (ι : E → Rw) (star : Fin s) (P0 : Finset E)
    (hι : ∀ e ∈ P0, ι e ∈ R) :
    ∀ i w, w ∈ initialSupport star P0 (binRows R bin) i → rawInput ι w ∈ R := by
  apply initialSupport_row_subset ι R star P0 (binRows R bin) hι
  intro i r hr
  exact ((mem_binRows R bin i r).mp hr).1

/-- Selector equality is required only on the original paired support;
the raw extension away from the support need not describe any matrix row. -/
theorem supports_selector (R : Set Rw) (bin : Rw → Fin s)
    (ι : E → Rw) (ζ : E → S × S) (selector : Rw → S) (default : S)
    (star : Fin s) (P0 : Finset E)
    (hfirst : ∀ e ∈ P0, selector (ι e) = (ζ e).1) :
    ∀ i w, w ∈ initialSupport star P0 (binRows R bin) i →
      firstSelector ζ selector default w = selector (rawInput ι w) := by
  classical
  intro i w hw
  by_cases hi : i = star
  · subst i
    rw [initialSupport_star] at hw
    cases w with
    | inl e => exact (hfirst e ((mem_pairedSupport P0 e).mp hw)).symm
    | inr r => simp [pairedSupport] at hw
  · rw [initialSupport_other star i P0 (binRows R bin) hi] at hw
    cases w with
    | inl e => simp [otherSupport] at hw
    | inr r => rfl

theorem supports_floor (μ : FiniteLaw S) (R : Set Rw) (bin : Rw → Fin s)
    (ζ : E → S × S) (selector : Rw → S) (default : S)
    (star : Fin s) (P0 : Finset E) (t : ℝ)
    (hpair : t ≤ μ.prob (· ∈ (fun e => (ζ e).1) '' (P0 : Set E)))
    (hrow : ∀ i ≠ star, t ≤ μ.prob
      (fun z => ∃ r ∈ R, bin r = i ∧ selector r = z)) :
    ∀ i, t ≤ ProjectedSupportStep.mass μ (firstSelector ζ selector default)
      (initialSupport star P0 (binRows R bin) i) := by
  classical
  intro i
  rw [initialSupport_mass]
  split_ifs with hi
  · exact hpair
  · rw [binRows_image]
    exact hrow i hi

variable {C : Type*}

/-- Only original paired-row entries are used on the attachment. -/
theorem supports_foreign (R : Set Rw) (bin : Rw → Fin s)
    (ι : E → Rw) (ζ : E → S × S) (selector : Rw → S) (default : S)
    (star : Fin s) (P0 : Finset E) (M : Rw → C → Bool) (T : S → C → Bool)
    (hforeign : ∀ e ∈ P0, ∀ c, M (ι e) c = T (ζ e).2 c) :
    ∀ w ∈ initialSupport star P0 (binRows R bin) star, ∀ c,
      M (rawInput ι w) c = T (jointSelector ζ selector default w).2 c := by
  intro w hw c
  rw [initialSupport_star] at hw
  cases w with
  | inl e => exact hforeign e ((mem_pairedSupport P0 e).mp hw) c
  | inr r => simp [pairedSupport] at hw

end Paper2.TwoStreamOriginalInputs

#print axioms Paper2.TwoStreamOriginalInputs.supports_selector
#print axioms Paper2.TwoStreamOriginalInputs.supports_floor
#print axioms Paper2.TwoStreamOriginalInputs.supports_foreign
