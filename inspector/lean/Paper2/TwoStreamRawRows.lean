import Paper2.TwoStreamRetention

/-!
# Original paired labels inside one raw row carrier

Frozen v12, Section 5, `res:two-stream`. The paired probability space `E`
is not identified with the matrix row space `Rw`: its labels are preserved
as the left summand of `E ⊕ Rw`. The derived law on that sum puts no mass on
the right summand. No injectivity of the original row map is required.
-/

namespace Paper2.TwoStreamRawRows

open scoped BigOperators

variable {E Rw S : Type*} [Fintype E] [Fintype Rw] [Fintype S]

/-- An original raw label is evaluated at its original matrix row. -/
def rawInput (ι : E → Rw) : (E ⊕ Rw) → Rw := Sum.elim ι id

@[simp] theorem rawInput_inl (ι : E → Rw) (e : E) :
    rawInput ι (.inl e) = ι e := rfl

@[simp] theorem rawInput_inr (ι : E → Rw) (r : Rw) :
    rawInput ι (.inr r) = r := rfl

/-- The extension's first selector agrees globally with the ordinary row
selector on the right summand. Its second right-summand component is unused. -/
def jointSelector (ζ : E → S × S) (selector : Rw → S) (default : S) :
    (E ⊕ Rw) → S × S
  | .inl e => ζ e
  | .inr r => (selector r, default)

def firstSelector (ζ : E → S × S) (selector : Rw → S) (default : S) :
    (E ⊕ Rw) → S := fun w => (jointSelector ζ selector default w).1

@[simp] theorem jointSelector_inl (ζ : E → S × S) (selector : Rw → S)
    (default : S) (e : E) : jointSelector ζ selector default (.inl e) = ζ e := rfl

@[simp] theorem jointSelector_inr (ζ : E → S × S) (selector : Rw → S)
    (default : S) (r : Rw) :
    jointSelector ζ selector default (.inr r) = (selector r, default) := rfl

@[simp] theorem firstSelector_inl (ζ : E → S × S) (selector : Rw → S)
    (default : S) (e : E) :
    firstSelector ζ selector default (.inl e) = (ζ e).1 := rfl

@[simp] theorem firstSelector_inr (ζ : E → S × S) (selector : Rw → S)
    (default : S) (r : Rw) :
    firstSelector ζ selector default (.inr r) = selector r := rfl

/-- Original ambient paired weights, with zero mass on ordinary-only labels. -/
def pairedLaw (κE : FiniteLaw E) : FiniteLaw (E ⊕ Rw) where
  weight := fun w => match w with
    | .inl e => κE.weight e
    | .inr _ => 0
  nonneg := by
    intro w
    cases w with
    | inl e => exact κE.nonneg e
    | inr r => exact le_refl 0
  total := by
    rw [Fintype.sum_sum_type]
    simp [κE.total]

/-- The concentrated law transports the *whole* original paired law. -/
theorem pairedLaw_pushes (κE : FiniteLaw E) (μ : FiniteLaw S)
    (ζ : E → S × S) (selector : Rw → S) (default : S)
    (hζ : κE.PushesTo (μ.prod μ) ζ) :
    (pairedLaw κE).PushesTo (μ.prod μ) (jointSelector ζ selector default) := by
  intro U
  have he : (pairedLaw κE).prob (fun w => U (jointSelector ζ selector default w)) =
      κE.prob (fun e => U (ζ e)) := by
    classical
    unfold FiniteLaw.prob
    rw [Fintype.sum_sum_type]
    simp [pairedLaw, jointSelector]
  exact he.trans (hζ U)

/-- The original first-coordinate law follows without a row-space law. -/
theorem first_pushes (κE : FiniteLaw E) (μ : FiniteLaw S)
    (ζ : E → S × S) (selector : Rw → S) (default : S)
    (hζ : κE.PushesTo (μ.prod μ) ζ) :
    (pairedLaw κE).PushesTo μ (firstSelector ζ selector default) := by
  exact TwoStreamMatrix.paired_first_pushes μ (pairedLaw κE)
    (jointSelector ζ selector default) (pairedLaw_pushes κE μ ζ selector default hζ)

/-- The original paired support keeps its `E` labels distinct. -/
noncomputable def pairedSupport (P0 : Finset E) : Finset (E ⊕ Rw) := by
  classical
  exact P0.image Sum.inl

/-- Ordinary-only supports use the other tag. -/
noncomputable def otherSupport (R : Finset Rw) : Finset (E ⊕ Rw) := by
  classical
  exact R.image Sum.inr

/-- Recover the original paired subset from a tagged raw support. -/
noncomputable def decode (P : Finset (E ⊕ Rw)) : Finset E := by
  classical
  exact Finset.univ.filter fun e => Sum.inl e ∈ P

@[simp] theorem mem_pairedSupport (P0 : Finset E) (e : E) :
    (Sum.inl e : E ⊕ Rw) ∈ pairedSupport (Rw := Rw) P0 ↔ e ∈ P0 := by
  classical
  simp [pairedSupport]

@[simp] theorem mem_otherSupport (R : Finset Rw) (r : Rw) :
    (Sum.inr r : E ⊕ Rw) ∈ otherSupport (E := E) R ↔ r ∈ R := by
  classical
  simp [otherSupport]

@[simp] theorem mem_decode (P : Finset (E ⊕ Rw)) (e : E) :
    e ∈ decode P ↔ Sum.inl e ∈ P := by
  classical
  simp [decode]

theorem decode_subset (P0 : Finset E) (P : Finset (E ⊕ Rw))
    (h : P ⊆ pairedSupport P0) : decode P ⊆ P0 := by
  intro e he
  exact (mem_pairedSupport (Rw := Rw) P0 e).mp (h ((mem_decode P e).mp he))

/-- Every subset of a paired initial support is again precisely an embedded
original `E`-subset. There is no unlabelled row-space replacement. -/
theorem pairedSupport_decode (P0 : Finset E) (P : Finset (E ⊕ Rw))
    (h : P ⊆ pairedSupport P0) : pairedSupport (decode P) = P := by
  classical
  ext w
  cases w with
  | inl e => simp [mem_pairedSupport, mem_decode]
  | inr r =>
    have hn : Sum.inr r ∉ P := by
      intro hr
      have := h hr
      simp [pairedSupport] at this
    simp [pairedSupport, hn]

/-- On every tagged label, the frontier's first selector is the selector
of its actual matrix row, provided the original paired-row identity holds. -/
theorem firstSelector_eq_rowSelector (ι : E → Rw) (ζ : E → S × S)
    (selector : Rw → S) (default : S)
    (hstar : ∀ e, selector (ι e) = (ζ e).1) :
    firstSelector ζ selector default = selector ∘ rawInput ι := by
  funext w
  cases w with
  | inl e => exact (hstar e).symm
  | inr r => rfl

/-- First-selector images of initial paired supports are exactly the
original `E` images, with labelled duplicates preserved before projection. -/
theorem paired_first_image (ζ : E → S × S) (selector : Rw → S)
    (default : S) (P0 : Finset E) :
    firstSelector ζ selector default '' (pairedSupport (Rw := Rw) P0 : Set (E ⊕ Rw)) =
      (fun e => (ζ e).1) '' (P0 : Set E) := by
  classical
  ext x
  constructor
  · rintro ⟨w, hw, rfl⟩
    cases w with
    | inl e => exact ⟨e, (mem_pairedSupport (Rw := Rw) P0 e).mp hw, rfl⟩
    | inr r => simp [pairedSupport] at hw
  · rintro ⟨e, he, rfl⟩
    exact ⟨.inl e, (mem_pairedSupport (Rw := Rw) P0 e).mpr he, rfl⟩

/-- Ordinary-only tagged supports have the actual original selector image. -/
theorem other_first_image (ζ : E → S × S) (selector : Rw → S)
    (default : S) (R : Finset Rw) :
    firstSelector ζ selector default '' (otherSupport (E := E) R : Set (E ⊕ Rw)) =
      selector '' (R : Set Rw) := by
  classical
  ext x
  constructor
  · rintro ⟨w, hw, rfl⟩
    cases w with
    | inl e => simp [otherSupport] at hw
    | inr r => exact ⟨r, (mem_otherSupport (E := E) R r).mp hw, rfl⟩
  · rintro ⟨r, hr, rfl⟩
    exact ⟨.inr r, (mem_otherSupport (E := E) R r).mpr hr, rfl⟩

/-- Selector-image floor transport for the distinguished bin. -/
theorem paired_first_mass (μ : FiniteLaw S) (ζ : E → S × S)
    (selector : Rw → S) (default : S) (P0 : Finset E) :
    ProjectedSupportStep.mass μ (firstSelector ζ selector default)
      (pairedSupport P0) = μ.prob (· ∈ (fun e => (ζ e).1) '' (P0 : Set E)) := by
  unfold ProjectedSupportStep.mass
  congr 1
  funext x
  apply propext
  change x ∈ firstSelector ζ selector default ''
    (pairedSupport (Rw := Rw) P0 : Set (E ⊕ Rw)) ↔ _
  rw [paired_first_image]

/-- Selector-image floor transport for every ordinary-only bin. -/
theorem other_first_mass (μ : FiniteLaw S) (ζ : E → S × S)
    (selector : Rw → S) (default : S) (R : Finset Rw) :
    ProjectedSupportStep.mass μ (firstSelector ζ selector default)
      (otherSupport R) = μ.prob (· ∈ selector '' (R : Set Rw)) := by
  unfold ProjectedSupportStep.mass
  congr 1
  funext x
  apply propext
  change x ∈ firstSelector ζ selector default ''
    (otherSupport (E := E) R : Set (E ⊕ Rw)) ↔ _
  rw [other_first_image]

/-- The retained tagged paired support has exactly the original joint
selector image, even when `ι` merges original matrix rows. -/
theorem joint_image_decode (ζ : E → S × S) (selector : Rw → S)
    (default : S) (P0 : Finset E) (P : Finset (E ⊕ Rw))
    (h : P ⊆ pairedSupport P0) :
    jointSelector ζ selector default '' (P : Set (E ⊕ Rw)) =
      ζ '' ((decode P : Finset E) : Set E) := by
  classical
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    cases w with
    | inl e => exact ⟨e, (mem_decode P e).mpr hw, rfl⟩
    | inr r =>
      have hn := h hw
      simp [pairedSupport] at hn
  · rintro ⟨e, he, rfl⟩
    exact ⟨.inl e, (mem_decode P e).mp he, rfl⟩

/-- Raw ambient loss in the tagged carrier is *exactly* the loss in `E`;
no law on the original matrix row space is introduced. -/
theorem paired_loss_eq [DecidableEq E] [DecidableEq Rw]
    (κE : FiniteLaw E) (P0 : Finset E) (P : Finset (E ⊕ Rw)) :
    SourceSupportStep.mass (pairedLaw κE) (pairedSupport P0 \ P) =
      SourceSupportStep.mass κE (P0 \ decode P) := by
  classical
  unfold SourceSupportStep.mass FiniteLaw.prob
  rw [Fintype.sum_sum_type]
  simp [pairedLaw, mem_pairedSupport, mem_decode]

/-- The frozen paired-retention hypothesis transfers to *any* tagged raw
subset of the original paired support, with exactly the same loss bound. -/
theorem retention_transfer [DecidableEq E] [DecidableEq Rw]
    (κE : FiniteLaw E) (μ : FiniteLaw S)
    (ζ : E → S × S) (selector : Rw → S) (default : S)
    (P0 : Finset E) (τ : ℝ)
    (hretain : ∀ P' : Finset E, P' ⊆ P0 →
      SourceSupportStep.mass κE (P0 \ P') < τ →
      (49 / 64 : ℝ) ≤ (μ.prod μ).prob (· ∈ ζ '' (P' : Set E))) :
    ∀ P : Finset (E ⊕ Rw), P ⊆ pairedSupport P0 →
      SourceSupportStep.mass (pairedLaw κE) (pairedSupport P0 \ P) < τ →
      (49 / 64 : ℝ) ≤ (μ.prod μ).prob
        (· ∈ jointSelector ζ selector default '' (P : Set (E ⊕ Rw))) := by
  intro P hP hloss
  have hsub := decode_subset P0 P hP
  have heq := paired_loss_eq κE P0 P
  rw [heq] at hloss
  have himage := joint_image_decode ζ selector default P0 P hP
  rw [himage]
  exact hretain (decode P) hsub hloss

section InitialSupports

variable {I : Type*}

/-- Exactly one paired support, in the distinguished bin, and ordinary-only
supports on the other original bin labels. -/
noncomputable def initialSupport (star : I) (P0 : Finset E)
    (R : I → Finset Rw) (i : I) : Finset (E ⊕ Rw) := by
  classical
  exact if i = star then pairedSupport P0 else otherSupport (R i)

@[simp] theorem initialSupport_star (star : I) (P0 : Finset E)
    (R : I → Finset Rw) :
    initialSupport star P0 R star = pairedSupport P0 := by
  simp [initialSupport]

theorem initialSupport_other (star i : I) (P0 : Finset E)
    (R : I → Finset Rw) (hi : i ≠ star) :
    initialSupport star P0 R i = otherSupport (R i) := by
  simp [initialSupport, hi]

/-- Every initial tagged label evaluates at a row in its declared bin. -/
theorem initialSupport_bin (ι : E → Rw) (bin : Rw → I)
    (star : I) (P0 : Finset E) (R : I → Finset Rw)
    (hP : ∀ e ∈ P0, bin (ι e) = star)
    (hR : ∀ i, ∀ r ∈ R i, bin r = i) :
    ∀ i w, w ∈ initialSupport star P0 R i → bin (rawInput ι w) = i := by
  classical
  intro i w hw
  by_cases hi : i = star
  · subst i
    rw [initialSupport_star] at hw
    cases w with
    | inl e => exact hP e ((mem_pairedSupport (Rw := Rw) P0 e).mp hw)
    | inr r => simp [pairedSupport] at hw
  · rw [initialSupport_other star i P0 R hi] at hw
    cases w with
    | inl e => simp [otherSupport] at hw
    | inr r => exact hR i r ((mem_otherSupport (E := E) (R i) r).mp hw)

/-- Initial tagged labels map to actually retained original matrix rows. -/
theorem initialSupport_row_subset (ι : E → Rw) (retained : Set Rw)
    (star : I) (P0 : Finset E) (R : I → Finset Rw)
    (hP : ∀ e ∈ P0, ι e ∈ retained)
    (hR : ∀ i, ∀ r ∈ R i, r ∈ retained) :
    ∀ i w, w ∈ initialSupport star P0 R i → rawInput ι w ∈ retained := by
  classical
  intro i w hw
  by_cases hi : i = star
  · subst i
    rw [initialSupport_star] at hw
    cases w with
    | inl e => exact hP e ((mem_pairedSupport (Rw := Rw) P0 e).mp hw)
    | inr r => simp [pairedSupport] at hw
  · rw [initialSupport_other star i P0 R hi] at hw
    cases w with
    | inl e => simp [otherSupport] at hw
    | inr r => exact hR i r ((mem_otherSupport (E := E) (R i) r).mp hw)

/-- The initial frontier floors are precisely the original selector-image
floors on `P0` and the raw single-bin sets, with no replacement rows. -/
theorem initialSupport_mass (μ : FiniteLaw S) (ζ : E → S × S)
    (selector : Rw → S) (default : S)
    [DecidableEq I]
    (star : I) (P0 : Finset E) (R : I → Finset Rw) (i : I) :
    ProjectedSupportStep.mass μ (firstSelector ζ selector default)
      (initialSupport star P0 R i) =
      if i = star then μ.prob (· ∈ (fun e => (ζ e).1) '' (P0 : Set E))
      else μ.prob (· ∈ selector '' ((R i : Finset Rw) : Set Rw)) := by
  classical
  by_cases hi : i = star
  · subst i
    simpa using paired_first_mass μ ζ selector default P0
  · rw [initialSupport_other star i P0 R hi,
      other_first_mass μ ζ selector default (R i)]
    simp [hi]

end InitialSupports

end Paper2.TwoStreamRawRows

#print axioms Paper2.TwoStreamRawRows.pairedLaw_pushes
#print axioms Paper2.TwoStreamRawRows.first_pushes
#print axioms Paper2.TwoStreamRawRows.paired_loss_eq
#print axioms Paper2.TwoStreamRawRows.retention_transfer
#print axioms Paper2.TwoStreamRawRows.initialSupport_bin
#print axioms Paper2.TwoStreamRawRows.initialSupport_mass
