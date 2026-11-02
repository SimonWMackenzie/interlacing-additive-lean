import Paper2.SourceLaws
import Paper2.ProductProjections

/-!
Private v27 proof development for `det:flat` and its use in
`I-deterministic-transfer.tex`, lines 138--149 and 601--608.

The carriers are *indices*, not decoded words. In particular, two indices
with the same decoded word remain separate outcomes of the finite law.
-/

namespace CurrentAdditive

open Paper2 Paper2.FiniteLaw
open scoped BigOperators

variable {Meta Seed J : Type*}
  [Fintype Meta] [Fintype Seed] [Fintype J]

/-- Fixing a complete, independent metadata value leaves every event of the
entire seed stream with its original probability, before normalization. -/
theorem fixed_metadata_joint_event (ρ : FiniteLaw Meta) (σ : FiniteLaw Seed)
    (m : Meta) (E : Seed → Prop) :
    (ρ.prod σ).prob (fun x => x.1 = m ∧ E x.2) =
      ρ.weight m * σ.prob E := by
  exact FiniteLaw.prod_prob_fixed_fst ρ σ m E

/-- The ordinary finite conditional probability at a positive-mass *whole*
metadata value is exactly the ambient seed marginal. -/
theorem fixed_metadata_conditional (ρ : FiniteLaw Meta) (σ : FiniteLaw Seed)
    (m : Meta) (hm : 0 < ρ.weight m) (E : Seed → Prop) :
    (ρ.prod σ).prob (fun x => x.1 = m ∧ E x.2) /
      (ρ.prod σ).prob (fun x => x.1 = m) = σ.prob E := by
  rw [fixed_metadata_joint_event]
  have hden : (ρ.prod σ).prob (fun x => x.1 = m) = ρ.weight m := by
    convert fixed_metadata_joint_event ρ σ m (fun _ => True) using 1
    · congr 1
      funext x
      simp
    · simp
  rw [hden]
  exact mul_div_cancel_left₀ (σ.prob E) (ne_of_gt hm)

/-- A complete metadata *tuple* may comprise any fixed number of streams.
Its product carrier can be nested here without changing the assertion. -/
theorem fixed_two_metadata_streams
    {Meta₂ : Type*} [Fintype Meta₂]
    (ρ₁ : FiniteLaw Meta) (ρ₂ : FiniteLaw Meta₂) (σ : FiniteLaw Seed)
    (m₁ : Meta) (m₂ : Meta₂)
    (hm₁ : 0 < ρ₁.weight m₁) (hm₂ : 0 < ρ₂.weight m₂)
    (E : Seed → Prop) :
    ((ρ₁.prod ρ₂).prod σ).prob
        (fun x => x.1 = (m₁, m₂) ∧ E x.2) /
      ((ρ₁.prod ρ₂).prod σ).prob
        (fun x => x.1 = (m₁, m₂)) = σ.prob E := by
  apply fixed_metadata_conditional
  exact mul_pos hm₁ hm₂

/-- Exact bounded-wise marginals of a source of *indexed* labels. No
identification of indices with the same decoding is performed. -/
def IsDWise {ι A Ω : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype A] [Fintype Ω]
    (D : ℕ) (ν : FiniteLaw Ω) (decode : Ω → ι → A)
    (μ : FiniteLaw A) : Prop :=
  ∀ (s : Finset ι), s.card ≤ D → ∀ E : (s → A) → Prop,
    ν.prob (fun x => E (fun i : s => decode x i)) =
      (FiniteLaw.pi (fun _ : s => μ)).prob E

section Flatten

variable {I : Type*} [Fintype I] [DecidableEq I]
  {O : Type*} [Fintype O] [DecidableEq O]
  {Outer : Type*} [Fintype Outer]
  [DecidableEq J]

/-- Coordinates of a flattened subset that lie over one outer position. -/
private def slice (s : Finset (O × I)) (o : O) : Finset I :=
  (s.filter (fun a => a.1 = o)).image Prod.snd

private theorem mem_slice_iff (s : Finset (O × I)) (o : O) (i : I) :
    i ∈ slice s o ↔ (o, i) ∈ s := by
  classical
  simp only [slice, Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨a, ⟨ha, hfst⟩, hsnd⟩
    have : a = (o, i) := Prod.ext hfst hsnd
    simpa [this] using ha
  · intro h
    exact ⟨(o, i), ⟨h, rfl⟩, rfl⟩

private theorem slice_card_le (s : Finset (O × I)) (o : O) :
    (slice s o).card ≤ s.card :=
  (Finset.card_image_le).trans (Finset.card_filter_le _ _)

private theorem outer_card_le (s : Finset (O × I)) :
    (s.image Prod.fst).card ≤ s.card := Finset.card_image_le

/-- A probability fibre of a partial decoded inner word equals the product
of its requested coordinate weights. -/
private theorem inner_fibre (D : ℕ) (σ : FiniteLaw Seed)
    (μ : FiniteLaw J) (decode : Seed → I → J)
    (hinner : IsDWise D σ decode μ)
    (s : Finset (O × I)) (o : O) (hs : s.card ≤ D)
    (y : s → J) :
    σ.prob (fun a => ∀ i : slice s o,
      decode a i = y ⟨(o, i), (mem_slice_iff s o i).mp i.property⟩) =
      ∏ i : slice s o,
        μ.weight (y ⟨(o, i), (mem_slice_iff s o i).mp i.property⟩) := by
  let u := slice s o
  let v : u → J := fun i => y ⟨(o, i), (mem_slice_iff s o i).mp i.property⟩
  have h := hinner u ((slice_card_le s o).trans hs) (fun z => z = v)
  rw [FiniteLaw.prob_singleton] at h
  simpa only [FiniteLaw.pi, v, u, funext_iff] using h

private theorem slice_product (s : Finset (O × I)) (o : O)
    (μ : FiniteLaw J) (y : s → J) :
    (∏ i : slice s o,
        μ.weight (y ⟨(o, i), (mem_slice_iff s o i).mp i.property⟩)) =
      ∏ a ∈ s.filter (fun a => a.1 = o),
        μ.weight (if h : a ∈ s then y ⟨a, h⟩ else Classical.choice μ.nonempty) := by
  classical
  let f : I → ℝ := fun i =>
    μ.weight (if h : (o, i) ∈ s then y ⟨(o, i), h⟩ else Classical.choice μ.nonempty)
  have hinj : ∀ a ∈ s.filter (fun a => a.1 = o),
      ∀ b ∈ s.filter (fun a => a.1 = o), a.2 = b.2 → a = b := by
    intro a ha b hb h
    have h₁ : a.1 = o := (Finset.mem_filter.mp ha).2
    have h₂ : b.1 = o := (Finset.mem_filter.mp hb).2
    exact Prod.ext (h₁.trans h₂.symm) h
  have himage := Finset.prod_image (f := f) hinj
  change (∏ i ∈ slice s o, f i) =
    ∏ a ∈ s.filter (fun a => a.1 = o), f a.2 at himage
  calc
    _ = ∏ i : slice s o, f i := by
      apply Finset.prod_congr rfl
      intro i _
      simp only [f, dif_pos ((mem_slice_iff s o i).mp i.property)]
    _ = ∏ i ∈ slice s o, f i := by
      exact (Finset.prod_subtype (slice s o) (by simp) f).symm
    _ = ∏ a ∈ s.filter (fun a => a.1 = o), f a.2 := himage
    _ = _ := by
      apply Finset.prod_congr rfl
      intro a ha
      have hfst : a.1 = o := (Finset.mem_filter.mp ha).2
      cases a with
      | mk a i => simp only at hfst; subst a; rfl

/-- The exact flattened singleton marginals; here `O` and `I` are the
outer-position and within-seed coordinate sets. -/
private theorem flattened_fibre (D : ℕ) (σ : FiniteLaw Seed)
    (τ : FiniteLaw Outer) (μ : FiniteLaw J)
    (decode : Seed → I → J) (outerDecode : Outer → O → Seed)
    (hinner : IsDWise D σ decode μ)
    (houter : IsDWise D τ outerDecode σ)
    (s : Finset (O × I)) (hs : s.card ≤ D) (y : s → J) :
    τ.prob (fun x => ∀ a : s,
      decode (outerDecode x a.val.1) a.val.2 = y a) =
      ∏ a : s, μ.weight (y a) := by
  classical
  let sO : Finset O := s.image Prod.fst
  let F : sO → Seed → Prop := fun o a =>
    ∀ p : s, p.val.1 = o.val → decode a p.val.2 = y p
  let Ev : (sO → Seed) → Prop := fun v => ∀ p : s,
    decode (v ⟨p.val.1, Finset.mem_image_of_mem Prod.fst p.property⟩) p.val.2 = y p
  have hev (v : sO → Seed) : Ev v ↔ ∀ o : sO, F o (v o) := by
    constructor
    · intro h o p hp
      have e : (⟨p.val.1, Finset.mem_image_of_mem Prod.fst p.property⟩ : sO) = o :=
        Subtype.ext hp
      simpa only [F, e] using h p
    · intro h p
      have hp := h ⟨p.val.1, Finset.mem_image_of_mem Prod.fst p.property⟩ p rfl
      exact hp
  have hsource := houter sO ((outer_card_le s).trans hs) Ev
  have hleft : τ.prob (fun x => ∀ p : s,
      decode (outerDecode x p.val.1) p.val.2 = y p) =
      τ.prob (fun x => Ev (fun o : sO => outerDecode x o)) := rfl
  rw [hleft, hsource]
  have hproduct : (FiniteLaw.pi (fun _ : sO => σ)).prob Ev =
      ∏ o : sO, σ.prob (F o) := by
    calc
      _ = (FiniteLaw.pi (fun _ : sO => σ)).prob
          (fun v => ∀ o : sO, F o (v o)) := by
        congr 1
        funext v
        exact propext (hev v)
      _ = _ := FiniteLaw.pi_prob_coordinatewise (fun _ : sO => σ) F
  rw [hproduct]
  have hfibre (o : sO) : σ.prob (F o) =
      ∏ i : slice s o.val,
        μ.weight (y ⟨(o.val, i), (mem_slice_iff s o.val i).mp i.property⟩) := by
    have hevent (a : Seed) : F o a ↔ ∀ i : slice s o.val,
        decode a i = y ⟨(o.val, i), (mem_slice_iff s o.val i).mp i.property⟩ := by
      constructor
      · intro h i
        exact h ⟨(o.val, i), (mem_slice_iff s o.val i).mp i.property⟩ rfl
      · intro h p hp
        have ep : p.val = (o.val, p.val.2) := Prod.ext hp rfl
        have hi : p.val.2 ∈ slice s o.val :=
          (mem_slice_iff s o.val p.val.2).mpr (by rw [← ep]; exact p.property)
        have hpSub : (⟨(o.val, p.val.2), (mem_slice_iff s o.val p.val.2).mp hi⟩ : s) = p :=
          Subtype.ext ep.symm
        simpa only [hpSub] using h ⟨p.val.2, hi⟩
    calc
      _ = σ.prob (fun a => ∀ i : slice s o.val,
          decode a i = y ⟨(o.val, i), (mem_slice_iff s o.val i).mp i.property⟩) := by
        congr 1
        funext a
        exact propext (hevent a)
      _ = _ := inner_fibre D σ μ decode hinner s o.val hs y
  simp_rw [hfibre]
  let f : O × I → ℝ := fun a =>
    μ.weight (if h : a ∈ s then y ⟨a, h⟩ else Classical.choice μ.nonempty)
  have hgroup : (∏ o : sO, ∏ i : slice s o.val,
      μ.weight (y ⟨(o.val, i), (mem_slice_iff s o.val i).mp i.property⟩)) =
      ∏ a ∈ s, f a := by
    calc
      _ = ∏ o : sO, ∏ a ∈ s.filter (fun a => a.1 = o.val), f a := by
        apply Finset.prod_congr rfl
        intro o _
        simpa only [f] using slice_product s o.val μ y
      _ = ∏ o ∈ sO, ∏ a ∈ s.filter (fun a => a.1 = o), f a := by
        exact (Finset.prod_subtype sO (by intro x; rfl)
          (fun o : O => ∏ a ∈ s.filter (fun a => a.1 = o), f a)).symm
      _ = ∏ a ∈ s, f a :=
        Finset.prod_fiberwise_of_maps_to
          (s := s) (t := sO) (g := Prod.fst)
          (fun a ha => Finset.mem_image_of_mem Prod.fst ha) f
  rw [hgroup]
  calc
    _ = ∏ a : s, f a := Finset.prod_subtype s (by intro x; rfl) f
    _ = ∏ a : s, μ.weight (y a) := by
      apply Finset.prod_congr rfl
      intro a _
      simp [f, a.property]

/-- `det:flat`: bounded-wise independence survives an indexed outer source
of inner seed indices. The conclusion holds for arbitrary joint events of
every selected set of at most `D` *distinct flattened positions*. -/
theorem flatten_dwise (D : ℕ) (σ : FiniteLaw Seed)
    (τ : FiniteLaw Outer) (μ : FiniteLaw J)
    (decode : Seed → I → J) (outerDecode : Outer → O → Seed)
    (hinner : IsDWise D σ decode μ)
    (houter : IsDWise D τ outerDecode σ) :
    IsDWise D τ
      (fun x (p : O × I) => decode (outerDecode x p.1) p.2) μ := by
  intro s hs E
  refine FiniteLaw.prob_preimage_eq_of_fibres
    τ (FiniteLaw.pi (fun _ : s => μ))
    (fun x a => decode (outerDecode x a.val.1) a.val.2) ?_ E
  intro y
  have hevent : (fun x : Outer =>
      (fun a : s => decode (outerDecode x a.val.1) a.val.2) = y) =
      (fun x => ∀ a : s,
        decode (outerDecode x a.val.1) a.val.2 = y a) := by
    funext x
    exact propext funext_iff
  rw [hevent]
  rw [flattened_fibre D σ τ μ decode outerDecode hinner houter s hs y]
  rfl

/-- Direct form used after fixing all metadata and base-label indices in the
constructed internal interlace of Appendix I. The third independent whole
stream is the selector-index source `τ`. -/
theorem fixed_metadata_flatten_dwise
    {Meta₂ : Type*} [Fintype Meta₂]
    (D : ℕ) (ρ₁ : FiniteLaw Meta) (ρ₂ : FiniteLaw Meta₂)
    (σ : FiniteLaw Seed) (τ : FiniteLaw Outer)
    (μ : FiniteLaw J) (decode : Seed → I → J)
    (outerDecode : Outer → O → Seed)
    (hinner : IsDWise D σ decode μ)
    (houter : IsDWise D τ outerDecode σ)
    (m₁ : Meta) (m₂ : Meta₂)
    (hm₁ : 0 < ρ₁.weight m₁) (hm₂ : 0 < ρ₂.weight m₂)
    (s : Finset (O × I)) (hs : s.card ≤ D)
    (E : (s → J) → Prop) :
    ((ρ₁.prod ρ₂).prod τ).prob
        (fun x => x.1 = (m₁, m₂) ∧
          E (fun a : s => decode (outerDecode x.2 a.val.1) a.val.2)) /
      ((ρ₁.prod ρ₂).prod τ).prob
        (fun x => x.1 = (m₁, m₂)) =
      (FiniteLaw.pi (fun _ : s => μ)).prob E := by
  rw [fixed_two_metadata_streams ρ₁ ρ₂ τ m₁ m₂ hm₁ hm₂
    (fun x => E (fun a : s => decode (outerDecode x a.val.1) a.val.2))]
  exact flatten_dwise D σ τ μ decode outerDecode hinner houter s hs E

/-- The same consumer interface for the repository's positive rational
weighted lists. `toFiniteLaw` changes only the coefficient field. -/
theorem rational_fixed_metadata_flatten_dwise
    {Meta₂ : Type*} [Fintype Meta₂]
    (D : ℕ) (ρ₁ : PositiveRationalLaw Meta)
    (ρ₂ : PositiveRationalLaw Meta₂)
    (σ : PositiveRationalLaw Seed)
    (τ : PositiveRationalLaw Outer)
    (μ : PositiveRationalLaw J) (decode : Seed → I → J)
    (outerDecode : Outer → O → Seed)
    (hinner : IsDWise D σ.toFiniteLaw decode μ.toFiniteLaw)
    (houter : IsDWise D τ.toFiniteLaw outerDecode σ.toFiniteLaw)
    (m₁ : Meta) (m₂ : Meta₂)
    (s : Finset (O × I)) (hs : s.card ≤ D)
    (E : (s → J) → Prop) :
    ((ρ₁.toFiniteLaw.prod ρ₂.toFiniteLaw).prod τ.toFiniteLaw).prob
        (fun x => x.1 = (m₁, m₂) ∧
          E (fun a : s => decode (outerDecode x.2 a.val.1) a.val.2)) /
      ((ρ₁.toFiniteLaw.prod ρ₂.toFiniteLaw).prod τ.toFiniteLaw).prob
        (fun x => x.1 = (m₁, m₂)) =
      (FiniteLaw.pi (fun _ : s => μ.toFiniteLaw)).prob E := by
  apply fixed_metadata_flatten_dwise D ρ₁.toFiniteLaw ρ₂.toFiniteLaw
    σ.toFiniteLaw τ.toFiniteLaw μ.toFiniteLaw decode outerDecode
    hinner houter m₁ m₂
  · change (0 : ℝ) < (ρ₁.weight m₁ : ℝ)
    exact_mod_cast ρ₁.positive m₁
  · change (0 : ℝ) < (ρ₂.weight m₂ : ℝ)
    exact_mod_cast ρ₂.positive m₂
  · exact hs

end Flatten

end CurrentAdditive

#print axioms CurrentAdditive.fixed_metadata_joint_event
#print axioms CurrentAdditive.fixed_metadata_conditional
#print axioms CurrentAdditive.fixed_two_metadata_streams
#print axioms CurrentAdditive.flatten_dwise
#print axioms CurrentAdditive.fixed_metadata_flatten_dwise
#print axioms CurrentAdditive.rational_fixed_metadata_flatten_dwise
