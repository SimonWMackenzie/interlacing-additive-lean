import Paper2.ProtectedIncomingRows
import Paper2.ProtectedIncomingColumns
import Paper2.RationalRowEstimates

/-!
# Labelled high-fibre blocks in the original incoming rectangle

This scratch development follows frozen v12 `res:incoming`, lines 360--386.
The selector-image density is an explicit upstream premise. Blocks retain
both their selected original coordinate and their inner coordinate; no
independent-coordinate column event is substituted for the whole image.
-/

namespace Paper2.ProtectedIncomingBlocks

open SourceMatrix SourceLaws ProtectedIncomingRows ProtectedIncomingColumns
open Workspace.Types.CommComplexity
open Workspace.Types.Protocol

variable {q₁ q₂ s w k : ℕ} {Y : Type*}

/-- Distinct coordinate/fibre labels, before choosing any original rows. -/
noncomputable def labelledBlocks (fibres : Fin k → Finset (Fin q₂)) :
    Finset (Σ _t : Fin k, Fin q₂) :=
  Finset.univ.sigma fibres

theorem labelledBlocks_card (fibres : Fin k → Finset (Fin q₂)) :
    (labelledBlocks fibres).card = ∑ t : Fin k, (fibres t).card := by
  simp [labelledBlocks, Finset.card_sigma]

/-- The actual outer labels available at a selected original coordinate.
`true` selects its fixed-tail tag and `false` its diagonal tag. -/
def incomingImage (R : Set (Fin w × TaggedColumn q₁ q₂ s Y))
    (e : Fin k → Fin w) (p : Fin k → Fin s) (tag : Fin k → Bool)
    (t : Fin k) : Set (OuterColumn q₁ q₂ s Y) :=
  if tag t then fixedImage R (e t) (p t) else diagonalEvent R (e t)

/-- The explicit original-tag density hypothesis yields the high-fibre
count separately in each chosen coordinate. -/
theorem actual_high_fibres [Fintype Y] [NeZero q₂]
    (ν : PositiveRationalLaw Y)
    (R : Set (Fin w × TaggedColumn q₁ q₂ s Y))
    (e : Fin k → Fin w) (p : Fin k → Fin s) (tag : Fin k → Bool)
    (δ : ℝ) (hδ : 0 < δ)
    (hmass : ∀ t : Fin k, δ / 2 <
      if tag t then (fixedTailLaw ν q₁ q₂ s).toFiniteLaw.prob
        (· ∈ fixedEvent R (e t))
      else (outerLaw ν q₁ q₂ s).toFiniteLaw.prob
        (· ∈ diagonalEvent R (e t)))
    (t : Fin k) :
    δ * q₂ / 4 < (highFibres ν (incomingImage R e p tag t) δ).card := by
  by_cases ht : tag t = true
  · simpa only [incomingImage, ht, Bool.cond_true] using
      fixed_high_fibres ν R (e t) (p t) δ hδ (by simpa [ht] using hmass t)
  · have hf : tag t = false := Bool.eq_false_iff.mpr ht
    simpa only [incomingImage, hf, Bool.cond_false] using
      diagonal_high_fibres ν R (e t) δ hδ (by simpa [hf] using hmass t)

/-- The strict per-coordinate fibre estimates yield more than `K` distinct
labelled blocks; the first label prevents collisions across coordinates. -/
theorem more_than_K_blocks (fibres : Fin k → Finset (Fin q₂))
    (δ : ℝ) (s κ u : ℕ) (hk : 0 < k) (hu : u = 2 * k)
    (hsize : 16 * (s : ℝ) * (κ : ℝ) ≤ (u : ℝ) * δ)
    (hfibre : ∀ t : Fin k, δ * (q₂ : ℝ) / 4 < (fibres t).card) :
    (2 * s * κ * q₂ : ℕ) < (labelledBlocks fibres).card := by
  have hne : (Finset.univ : Finset (Fin k)).Nonempty := by
    exact ⟨⟨0, hk⟩, Finset.mem_univ _⟩
  have hsum := Finset.sum_lt_sum_of_nonempty hne
    (fun t _ => hfibre t)
  have hleft : (∑ _t : Fin k, δ * (q₂ : ℝ) / 4) =
      (k : ℝ) * (δ * (q₂ : ℝ) / 4) := by simp
  rw [hleft] at hsum
  have hq : 0 ≤ (q₂ : ℝ) := by positivity
  have hK : ((2 * s * κ * q₂ : ℕ) : ℝ) ≤
      (k : ℝ) * (δ * (q₂ : ℝ) / 4) := by
    rw [hu] at hsize
    push_cast at hsize ⊢
    nlinarith [mul_nonneg hq (sub_nonneg.mpr hsize)]
  have htarget : ((2 * s * κ * q₂ : ℕ) : ℝ) <
      ((labelledBlocks fibres).card : ℝ) := by
    rw [labelledBlocks_card]
    exact lt_of_le_of_lt hK (by simpa using hsum)
  exact_mod_cast htarget

/-- Select precisely `K/2+1` of the more-than-`K` original coordinate/
inner-coordinate blocks. No block-count certificate is assumed. -/
theorem select_actual_blocks [Fintype Y] [NeZero q₂]
    (ν : PositiveRationalLaw Y)
    (R : Set (Fin w × TaggedColumn q₁ q₂ s Y))
    (e : Fin k → Fin w) (p : Fin k → Fin s) (tag : Fin k → Bool)
    (δ : ℝ) (hδ : 0 < δ) (u s₀ κ : ℕ)
    (hk : 0 < k) (hu : u = 2 * k)
    (hsize : 16 * (s₀ : ℝ) * (κ : ℝ) ≤ (u : ℝ) * δ)
    (hmass : ∀ t : Fin k, δ / 2 <
      if tag t then (fixedTailLaw ν q₁ q₂ s).toFiniteLaw.prob
        (· ∈ fixedEvent R (e t))
      else (outerLaw ν q₁ q₂ s).toFiniteLaw.prob
        (· ∈ diagonalEvent R (e t))) :
    ∃ Q : Finset (Σ _t : Fin k, Fin q₂),
      Q ⊆ labelledBlocks (fun t => highFibres ν (incomingImage R e p tag t) δ) ∧
      Q.card = s₀ * κ * q₂ + 1 := by
  classical
  let fibres := fun t : Fin k => highFibres ν (incomingImage R e p tag t) δ
  have hlarge : 2 * s₀ * κ * q₂ < (labelledBlocks fibres).card :=
    more_than_K_blocks fibres δ s₀ κ u hk hu hsize
      (actual_high_fibres ν R e p tag δ hδ hmass)
  have hlarge' : 2 * (s₀ * κ * q₂) < (labelledBlocks fibres).card := by
    convert hlarge using 1 <;> ring
  have hneed : s₀ * κ * q₂ + 1 ≤ (labelledBlocks fibres).card := by omega
  obtain ⟨Q, hQ, hc⟩ := Finset.exists_subset_card_eq hneed
  exact ⟨Q, hQ, hc⟩

/-- The published smallness and density-group guards imply the row-mass
threshold needed for `K = 2 s κ q₂`, with no new power guard. -/
theorem Kx_le_quarter (w s κ q₂ : ℕ) (δ D x : ℝ)
    (hw : 0 < w) (hq : 0 < q₂) (hD : 1 ≤ D)
    (hδ : D / (2 * (w : ℝ)) ≤ δ)
    (hsize : 16 * (s : ℝ) * (κ : ℝ) ≤ (w : ℝ) * δ)
    (hx : x ≤ 1 / ((w : ℝ) ^ 2 * (q₂ : ℝ))) :
    (2 * s * κ * q₂ : ℕ) * x ≤ δ / 4 := by
  have hwR : (0 : ℝ) < w := by exact_mod_cast hw
  have hqR : (0 : ℝ) < q₂ := by exact_mod_cast hq
  have hδ0 : 0 ≤ δ :=
    (by positivity : 0 ≤ D / (2 * (w : ℝ))).trans hδ
  have hsκ : 0 ≤ (s : ℝ) * κ := by positivity
  have hx' : (q₂ : ℝ) * x ≤ 1 / (w : ℝ) ^ 2 := by
    have hh := mul_le_mul_of_nonneg_left hx hqR.le
    have hden : (w : ℝ) ^ 2 ≠ 0 := by positivity
    convert hh using 1 <;> field_simp
  have hprod : (2 : ℝ) * s * κ * q₂ * x ≤ δ / (8 * (w : ℝ)) := by
    have hh := mul_le_mul_of_nonneg_left hx' (show (0 : ℝ) ≤ 2 * s * κ by positivity)
    have hbd : (2 : ℝ) * s * κ / (w : ℝ) ^ 2 ≤ δ / (8 * (w : ℝ)) := by
      apply (div_le_div_iff₀ (by positivity : 0 < (w : ℝ) ^ 2)
        (by positivity : 0 < 8 * (w : ℝ))).2
      have hm := mul_le_mul_of_nonneg_right hsize hwR.le
      nlinarith
    calc
      (2 : ℝ) * s * κ * q₂ * x = (2 : ℝ) * s * κ * ((q₂ : ℝ) * x) := by ring
      _ ≤ (2 : ℝ) * s * κ * (1 / (w : ℝ) ^ 2) := hh
      _ = (2 : ℝ) * s * κ / (w : ℝ) ^ 2 := by ring
      _ ≤ δ / (8 * (w : ℝ)) := hbd
  have hδw : 1 / (2 * (w : ℝ)) ≤ δ := by
    have hh := div_le_div_of_nonneg_right hD (by positivity : 0 ≤ 2 * (w : ℝ))
    exact hh.trans hδ
  have hdelta : δ / (8 * (w : ℝ)) ≤ δ / 4 := by
    have hw1 : (1 : ℝ) ≤ w := by exact_mod_cast hw
    apply (div_le_div_iff₀ (by positivity : 0 < 8 * (w : ℝ))
      (by norm_num : (0 : ℝ) < 4)).2
    nlinarith [mul_nonneg hδ0 (sub_nonneg.mpr (by linarith : (0 : ℝ) ≤ 2 * (w : ℝ) - 1))]
  have hh : (2 : ℝ) * s * κ * q₂ * x ≤ δ / 4 := hprod.trans hdelta
  simpa only [Nat.cast_mul] using hh

/-- A selected outer label is completed to one protected row of its actual
tag. The choice of fixed-tail versus diagonal is made per coordinate. -/
noncomputable def incomingRepresentative
    (R : Set (Fin w × TaggedColumn q₁ q₂ s Y))
    (e : Fin k → Fin w) (p : Fin k → Fin s) (tag : Fin k → Bool)
    (t : Fin k) (j : incomingImage R e p tag t) :
    Fin w × TaggedColumn q₁ q₂ s Y := by
  by_cases ht : tag t = true
  · exact fixedRepresentative R (e t) (p t)
      ⟨j.val, by simpa [incomingImage, ht] using j.property⟩
  · have hf : tag t = false := Bool.eq_false_iff.mpr ht
    exact diagonalRepresentative R (e t)
      ⟨j.val, by simpa [incomingImage, hf] using j.property⟩

theorem incomingRepresentative_survives
    (R : Set (Fin w × TaggedColumn q₁ q₂ s Y))
    (e : Fin k → Fin w) (p : Fin k → Fin s) (tag : Fin k → Bool)
    (t : Fin k) (j : incomingImage R e p tag t) :
    incomingRepresentative R e p tag t j ∈ R := by
  by_cases ht : tag t = true
  · simpa only [incomingRepresentative, dif_pos ht] using
      fixedRepresentative_survives R (e t) (p t)
        (⟨j.val, by simpa [incomingImage, ht] using j.property⟩ :
          fixedImage R (e t) (p t))
  · have hf : tag t = false := Bool.eq_false_iff.mpr ht
    simpa only [incomingRepresentative, dif_neg ht] using
      diagonalRepresentative_survives R (e t)
        (⟨j.val, by simpa [incomingImage, hf] using j.property⟩ :
          diagonalEvent R (e t))

theorem incomingRepresentative_injective
    (R : Set (Fin w × TaggedColumn q₁ q₂ s Y))
    (e : Fin k → Fin w) (p : Fin k → Fin s) (tag : Fin k → Bool)
    (t : Fin k) : Function.Injective (incomingRepresentative R e p tag t) := by
  intro j j' h
  apply Subtype.ext
  by_cases ht : tag t = true
  · have hj : (⟨j.val, by simpa [incomingImage, ht] using j.property⟩ :
        fixedImage R (e t) (p t)) =
        ⟨j'.val, by simpa [incomingImage, ht] using j'.property⟩ := by
      apply fixedRepresentative_injective R (e t) (p t)
      simpa only [incomingRepresentative, dif_pos ht] using h
    exact congrArg (fun z : fixedImage R (e t) (p t) => z.val) hj
  · have hf : tag t = false := Bool.eq_false_iff.mpr ht
    have hj : (⟨j.val, by simpa [incomingImage, hf] using j.property⟩ :
        diagonalEvent R (e t)) =
        ⟨j'.val, by simpa [incomingImage, hf] using j'.property⟩ := by
      apply diagonalRepresentative_injective R (e t)
      simpa only [incomingRepresentative, dif_neg ht] using h
    exact congrArg (fun z : diagonalEvent R (e t) => z.val) hj

/-- The literal original source entry read by the selected protected row. -/
theorem incomingRepresentative_entry
    {X V : Type*} [NeZero s]
    (base : X → Y → Bool)
    (activity : V → Fin q₂ → Option (Fin s)) (ξ₀ : Tail s Y)
    (R : Set (Fin w × TaggedColumn q₁ q₂ s Y))
    (e : Fin k → Fin w) (p : Fin k → Fin s) (tag : Fin k → Bool)
    (t : Fin k) (j : incomingImage R e p tag t)
    (z : Template q₁ q₂ X) :
    N base activity ξ₀ (incomingRepresentative R e p tag t j).2 (.inl (p t,z)) =
      T base z j.val := by
  by_cases ht : tag t = true
  · simpa only [incomingRepresentative, dif_pos ht] using
      fixedRepresentative_entry base activity ξ₀ R (e t) (p t)
        (⟨j.val, by simpa [incomingImage, ht] using j.property⟩ :
          fixedImage R (e t) (p t)) z
  · have hf : tag t = false := Bool.eq_false_iff.mpr ht
    simpa only [incomingRepresentative, dif_neg ht] using
      diagonalRepresentative_entry base activity ξ₀ R (e t) (p t)
        (⟨j.val, by simpa [incomingImage, hf] using j.property⟩ :
          diagonalEvent R (e t)) z

/-- An original protected row cannot be the same row at two different
selected copy labels. This is the first half of the row-label injection. -/
theorem incomingRepresentative_distinct_coordinates
    (R : Set (Fin w × TaggedColumn q₁ q₂ s Y))
    (e : Fin k → Fin w) (he : Function.Injective e)
    (p : Fin k → Fin s) (tag : Fin k → Bool)
    (t t' : Fin k) (j : incomingImage R e p tag t)
    (j' : incomingImage R e p tag t') (htt' : t ≠ t') :
    incomingRepresentative R e p tag t j ≠
      incomingRepresentative R e p tag t' j' := by
  intro h
  have hcoord (t : Fin k) (j : incomingImage R e p tag t) :
      (incomingRepresentative R e p tag t j).1 = e t := by
    by_cases ht : tag t = true
    · simp [incomingRepresentative, ht, fixedRepresentative]
    · have hf : tag t = false := Bool.eq_false_iff.mpr ht
      simp [incomingRepresentative, hf, diagonalRepresentative]
  apply htt'
  apply he
  calc
    e t = (incomingRepresentative R e p tag t j).1 := (hcoord t j).symm
    _ = (incomingRepresentative R e p tag t' j').1 := congrArg Prod.fst h
    _ = e t' := hcoord t' j'

/-- The actual selected row set of the transposed `M₁` interlace. Its
flattened labels remember both an original selected copy and an inner
coordinate; the word fibre is drawn from that copy's original row image. -/
def selectedWordRows
    (R : Set (Fin w × TaggedColumn q₁ q₂ s Y))
    (e : Fin k → Fin w) (p : Fin k → Fin s) (tag : Fin k → Bool)
    (Q : Finset (Σ _t : Fin k, Fin q₂)) :
    Set (Fin (k * q₂) × Word q₁ s Y) :=
  fun a =>
    let tα := finProdFinEquiv.symm a.1
    (⟨tα.1, tα.2⟩ : Σ _t : Fin k, Fin q₂) ∈ Q ∧
      (tα.2, a.2) ∈ incomingImage R e p tag tα.1

/-- This is the image of the whole selected template-tuple event under the
canonical flattening. It is not a product of singleton image events. -/
def flattenedSelectorImage {V X : Type*}
    (O : Set (Fin w → RawRow q₁ q₂ s X (SourceConstruction.Items s V)))
    (e : Fin k → Fin w) (p : Fin k → Fin s) :
    Set (Fin (k * q₂) → InnerRow q₁ X) :=
  (fun z : selectorImage O e p =>
    fun b => z.val (finProdFinEquiv.symm b).1 (finProdFinEquiv.symm b).2) ''
      Set.univ

/-- The canonical flattening is an equivalence of full tuple carriers. -/
def flattenTemplates (A : Type*) (k q : ℕ) :
    (Fin k → Fin q → A) ≃ (Fin (k * q) → A) where
  toFun z b := z (finProdFinEquiv.symm b).1 (finProdFinEquiv.symm b).2
  invFun y t α := y (finProdFinEquiv (t,α))
  left_inv z := by
    funext t α
    simp
  right_inv y := by
    funext b
    change y (finProdFinEquiv (finProdFinEquiv.symm b)) = y b
    rw [Equiv.apply_symm_apply]

/-- Full-event law transport along flattening; the event may correlate all
outer and inner positions. -/
theorem iid_flatten_prob {A : Type*} [Fintype A]
    (law : FiniteLaw A) (E : Set (Fin k → Fin q₂ → A)) :
    ((law.iid q₂).iid k).prob (· ∈ E) =
      (law.iid (k * q₂)).prob (· ∈ (flattenTemplates A k q₂) '' E) := by
  classical
  let f := flattenTemplates A k q₂
  unfold FiniteLaw.prob
  apply Fintype.sum_equiv f
  intro z
  have hmem : f z ∈ f '' E ↔ z ∈ E := by
    constructor
    · rintro ⟨u, hu, hzu⟩
      exact f.injective hzu ▸ hu
    · intro hz
      exact ⟨z, hz, rfl⟩
  have hweight : ((law.iid q₂).iid k).weight z =
      (law.iid (k * q₂)).weight (f z) := by
    change (∏ t : Fin k, ∏ α : Fin q₂, law.weight (z t α)) =
      ∏ b : Fin (k * q₂), law.weight (z (finProdFinEquiv.symm b).1
        (finProdFinEquiv.symm b).2)
    rw [← Fintype.prod_prod_type' (fun t α => law.weight (z t α))]
    apply Fintype.prod_equiv finProdFinEquiv
    intro tα
    simp
  change (if z ∈ E then ((law.iid q₂).iid k).weight z else 0) =
    if f z ∈ f '' E then (law.iid (k * q₂)).weight (f z) else 0
  rw [propext hmem, hweight]

/-- The flattened set is exactly the image of the same whole retained
selector-image event, with no coordinatewise replacement. -/
theorem flattenedSelectorImage_eq_flatten {V X : Type*}
    (O : Set (Fin w → RawRow q₁ q₂ s X (SourceConstruction.Items s V)))
    (e : Fin k → Fin w) (p : Fin k → Fin s) :
    flattenedSelectorImage O e p =
      (flattenTemplates (InnerRow q₁ X) k q₂) '' (selectorImage O e p) := by
  ext a
  constructor
  · rintro ⟨z, _, rfl⟩
    exact ⟨z.val, z.property, rfl⟩
  · rintro ⟨z, hz, rfl⟩
    exact ⟨⟨z, hz⟩, Set.mem_univ _, rfl⟩

/-- The source template product law and the flattened inner-row product law
assign identical mass to the exact selector image of the correlated event. -/
theorem selector_image_flatten_mass {V X : Type*} [Fintype X]
    [NeZero q₁]
    (μ : PositiveRationalLaw X)
    (O : Set (Fin w → RawRow q₁ q₂ s X (SourceConstruction.Items s V)))
    (e : Fin k → Fin w) (p : Fin k → Fin s) :
    ((templateLaw μ q₁ q₂).toFiniteLaw.iid k).prob
      (· ∈ selectorImage O e p) =
    ((((PositiveRationalLaw.uniform (Fin q₁)).prod μ).toFiniteLaw).iid
      (k * q₂)).prob (· ∈ flattenedSelectorImage O e p) := by
  let inner := (PositiveRationalLaw.uniform (Fin q₁)).prod μ
  rw [flattenedSelectorImage_eq_flatten]
  change (((inner.iid q₂).toFiniteLaw.iid k)).prob
      (· ∈ selectorImage O e p) = _
  rw [PositiveRationalLaw.toFiniteLaw_iid]
  exact iid_flatten_prob inner.toFiniteLaw (selectorImage O e p)

private theorem incomingRepresentative_first
    (R : Set (Fin w × TaggedColumn q₁ q₂ s Y))
    (e : Fin k → Fin w) (p : Fin k → Fin s) (tag : Fin k → Bool)
    (t : Fin k) (j : incomingImage R e p tag t) :
    (incomingRepresentative R e p tag t j).1 = e t := by
  by_cases ht : tag t = true
  · simp [incomingRepresentative, ht, fixedRepresentative]
  · have hf : tag t = false := Bool.eq_false_iff.mpr ht
    simp [incomingRepresentative, hf, diagonalRepresentative]

/-- Literal embedding in the same original node rectangle. A selected
column label is completed once to a whole surviving original tuple;
the resulting matrix entries are those of the flattened transposed `M₁`
interlace for all selected original protected rows simultaneously. -/
theorem selected_original_rectangle_D_le
    {X V : Type*} [Fintype X] [Fintype Y] [Fintype V] [NeZero s]
    (base : X → Y → Bool)
    (activity : SourceConstruction.Items s V → Fin q₂ → Option (Fin s))
    (ξ₀ : Tail s Y)
    (R : Set (Fin w × TaggedColumn q₁ q₂ s Y))
    (O : Set (Fin w → RawRow q₁ q₂ s X (SourceConstruction.Items s V)))
    (e : Fin k → Fin w) (p : Fin k → Fin s) (tag : Fin k → Bool)
    (Q : Finset (Σ _t : Fin k, Fin q₂)) :
    Compression.restrictionD
      (fullInterlace (fun (γ : Word q₁ s Y) a => M₁ base a γ) (k * q₂))
      (selectedWordRows R e p tag Q) (flattenedSelectorImage O e p) ≤
    Compression.restrictionD
      (fullInterlace (N base activity ξ₀) w) R O := by
  classical
  let S := selectedWordRows R e p tag Q
  let C := flattenedSelectorImage O e p
  let rowMap : S → R := fun a => by
    let tα := finProdFinEquiv.symm a.val.1
    let j : incomingImage R e p tag tα.1 :=
      ⟨(tα.2, a.val.2), a.property.2⟩
    exact ⟨incomingRepresentative R e p tag tα.1 j,
      incomingRepresentative_survives R e p tag tα.1 j⟩
  let colMap : C → O := fun c => by
    let f : selectorImage O e p → (Fin (k * q₂) → InnerRow q₁ X) :=
      fun z b => z.val (finProdFinEquiv.symm b).1
        (finProdFinEquiv.symm b).2
    let z : selectorImage O e p :=
      (SourceProjection.representative f Set.univ c).val
    exact ⟨selectorRepresentative O e p z,
      selectorRepresentative_survives O e p z⟩
  have hentry : (fun (a : S) (c : C) =>
      fullInterlace (fun (γ : Word q₁ s Y) b => M₁ base b γ)
        (k * q₂) a.val c.val) =
      (fun a c => fullInterlace (N base activity ξ₀) w
        (rowMap a).val (colMap c).val) := by
    funext a c
    let tα := finProdFinEquiv.symm a.val.1
    let f : selectorImage O e p → (Fin (k * q₂) → InnerRow q₁ X) :=
      fun z b => z.val (finProdFinEquiv.symm b).1
        (finProdFinEquiv.symm b).2
    let z : selectorImage O e p :=
      (SourceProjection.representative f Set.univ c).val
    have hflat : f z = c.val :=
      SourceProjection.representative_maps f Set.univ c
    let j : incomingImage R e p tag tα.1 :=
      ⟨(tα.2, a.val.2), a.property.2⟩
    have hcoord : (rowMap a).val.1 = e tα.1 :=
      incomingRepresentative_first R e p tag tα.1 j
    have htemplate := selectorRepresentative_coordinates O e p z tα.1
    have hrow := incomingRepresentative_entry base activity ξ₀
      R e p tag tα.1 j (z.val tα.1)
    change M₁ base (c.val a.val.1) a.val.2 =
      N base activity ξ₀ (rowMap a).val.2
        ((colMap c).val (rowMap a).val.1)
    rw [hcoord]
    change M₁ base (c.val a.val.1) a.val.2 =
      N base activity ξ₀ (incomingRepresentative R e p tag tα.1 j).2
        (selectorRepresentative O e p z (e tα.1))
    rw [htemplate, hrow]
    have hc : c.val a.val.1 = z.val tα.1 tα.2 := by
      have hh := congrArg (fun g => g a.val.1) hflat
      exact hh.symm
    rw [hc]
    rfl
  change D (fun (a : S) (c : C) =>
    fullInterlace (fun (γ : Word q₁ s Y) b => M₁ base b γ)
      (k * q₂) a.val c.val) ≤ _
  rw [hentry]
  exact Workspace.ProofLemmas.SublemmaPrecompNoIncrease
    (fun (a : R) (c : O) => fullInterlace (N base activity ξ₀) w a.val c.val)
    rowMap colMap

/-- Once the one whole-event selector-image density is transported to the
flattened inner-row product law, the checked rational power capacity applies
to the actual original rectangle. Its row floors come from the selected
high fibres, not from an assumed row-capacity certificate. -/
theorem selected_original_capacity_power
    {X V : Type*} [Fintype X] [Fintype Y] [Fintype V]
    [NeZero s] [NeZero q₁] [NeZero q₂]
    (μ : PositiveRationalLaw X) (ν : PositiveRationalLaw Y)
    (base : X → Y → Bool)
    (activity : SourceConstruction.Items s V → Fin q₂ → Option (Fin s))
    (ξ₀ : Tail s Y)
    (R : Set (Fin w × TaggedColumn q₁ q₂ s Y))
    (O : Set (Fin w → RawRow q₁ q₂ s X (SourceConstruction.Items s V)))
    (e : Fin k → Fin w) (p : Fin k → Fin s) (tag : Fin k → Bool)
    (δ x : ℝ) (hδ : 0 < δ) (H l : ℕ)
    (hH : 2 ≤ H) (hl : 2 ≤ l) (hx : 0 < x)
    (hpow : (2 : ℝ) ^ l * x ≤ δ / 4)
    (hprofile : RestrictionProfile
      (fun (γ : Word q₁ s Y) a => M₁ base a γ)
      (ν.iid (q₁ + s + 1)).toFiniteLaw
      ((PositiveRationalLaw.uniform (Fin q₁)).prod μ).toFiniteLaw x (H : ℤ))
    (Q : Finset (Σ _t : Fin k, Fin q₂))
    (hQ : Q ⊆ labelledBlocks
      (fun t => highFibres ν (incomingImage R e p tag t) δ))
    (hQcard : 2 ^ (l - 1) + 1 ≤ Q.card)
    (hcol : (12 / 25 : ℝ) <
      ((templateLaw μ q₁ q₂).toFiniteLaw.iid k).prob
        (· ∈ selectorImage O e p)) :
    H + l ≤ Compression.restrictionD
      (fullInterlace (N base activity ξ₀) w) R O := by
  classical
  let μword := ν.iid (q₁ + s + 1)
  let νinner := (PositiveRationalLaw.uniform (Fin q₁)).prod μ
  let S := selectedWordRows R e p tag Q
  let C := flattenedSelectorImage O e p
  have hscale : (2 : ℝ) ^ l * x ≤ 1 := by
    have hδfour : δ / 4 ≤ 1 := by
      -- A selected fibre has probability at most one; no separate scale
      -- certificate is required for the node.
      have hqpos : 0 < Q.card :=
        (Nat.succ_pos (2 ^ (l - 1))).trans_le hQcard
      obtain ⟨b, hb⟩ := Finset.card_pos.mp hqpos
      have hmem : b ∈ labelledBlocks
          (fun t => highFibres ν (incomingImage R e p tag t) δ) := hQ hb
      have hhigh : δ / 4 ≤ (μword.toFiniteLaw).prob
          (fun γ => (b.2, γ) ∈ incomingImage R e p tag b.1) :=
        (mem_highFibres ν (incomingImage R e p tag b.1) δ b.2).mp
          (Finset.mem_sigma.mp hmem).2
      have hle := μword.toFiniteLaw.prob_le_one
        (fun γ => (b.2, γ) ∈ incomingImage R e p tag b.1)
      linarith
    linarith
  have hrow : ∀ b ∈ Q, (2 : ℝ) ^ l * x ≤
      μword.toFiniteLaw.prob (fun γ => (finProdFinEquiv (b.1,b.2), γ) ∈ S) := by
    intro b hb
    have hmem : b ∈ labelledBlocks
        (fun t => highFibres ν (incomingImage R e p tag t) δ) := hQ hb
    have hhigh : δ / 4 ≤ μword.toFiniteLaw.prob
        (fun γ => (b.2, γ) ∈ incomingImage R e p tag b.1) :=
      (mem_highFibres ν (incomingImage R e p tag b.1) δ b.2).mp
        (Finset.mem_sigma.mp hmem).2
    have heq : (fun γ => (finProdFinEquiv (b.1,b.2), γ) ∈ S) =
        (fun γ => (b.2,γ) ∈ incomingImage R e p tag b.1) := by
      funext γ
      apply propext
      change ((⟨(finProdFinEquiv.symm (finProdFinEquiv (b.1,b.2))).1,
        (finProdFinEquiv.symm (finProdFinEquiv (b.1,b.2))).2⟩ :
          Σ _t : Fin k, Fin q₂) ∈ Q ∧
        ((finProdFinEquiv.symm (finProdFinEquiv (b.1,b.2))).2, γ) ∈
          incomingImage R e p tag
            (finProdFinEquiv.symm (finProdFinEquiv (b.1,b.2))).1) ↔ _
      simpa only [Equiv.symm_apply_apply, hb, true_and]
    rw [heq]
    exact hpow.trans hhigh
  let Qflat : Finset (Fin (k * q₂)) := Q.image (fun b => finProdFinEquiv (b.1,b.2))
  have hflatcard : Qflat.card = Q.card := by
    apply Finset.card_image_of_injective
    intro b b' hh
    have := finProdFinEquiv.injective hh
    cases b with | mk bt ba =>
      cases b' with | mk bt' ba' =>
        simpa using this
  have hrows : ∀ b ∈ Qflat, (2 : ℝ) ^ l * x ≤
      μword.toFiniteLaw.prob (fun γ => (b,γ) ∈ S.toFinset) := by
    intro b hb
    obtain ⟨b', hb', rfl⟩ := Finset.mem_image.mp hb
    simpa only [Set.mem_toFinset] using hrow b' hb'
  have hcols : (9 / 25 : ℝ) ≤
      (νinner.toFiniteLaw.iid (k * q₂)).prob (· ∈ C.toFinset) := by
    have hcol' : (9 / 25 : ℝ) ≤
        ((templateLaw μ q₁ q₂).toFiniteLaw.iid k).prob
          (· ∈ selectorImage O e p) := by linarith
    rw [selector_image_flatten_mass] at hcol'
    simpa only [Set.mem_toFinset] using hcol'
  have hh := RationalRowEstimates.small_capacity_power μword νinner
    (fun (γ : Word q₁ s Y) a => M₁ base a γ) H l (k * q₂)
    hH hx hl hscale hprofile Qflat (by simpa [hflatcard] using hQcard)
    S.toFinset C.toFinset hrows hcols
  have heq : D (NPCC.subgame
      (fullInterlace (fun (γ : Word q₁ s Y) a => M₁ base a γ)
        (k * q₂)) S.toFinset C.toFinset) =
      Compression.restrictionD
        (fullInterlace (fun (γ : Word q₁ s Y) a => M₁ base a γ)
          (k * q₂)) S C := by
    have hS : {z | z ∈ S.toFinset} = S := by ext z; simp
    have hC : {z | z ∈ C.toFinset} = C := by ext z; simp
    conv_rhs => rw [← hS, ← hC]
    rfl
  rw [heq] at hh
  exact hh.trans (selected_original_rectangle_D_le base activity ξ₀ R O e p tag Q)

/-- The complete labelled-block capacity step. All `K/2+1` rows are
selected from the actual fixed/diagonal high fibres; the `Kx` guard is
derived from the public width/smallness inputs. The only column hypothesis
is density of the *same* selector-image event under the template law. -/
theorem incoming_capacity_from_guards
    {X V : Type*} [Fintype X] [Fintype Y] [Fintype V]
    [NeZero s] [NeZero q₁] [NeZero q₂]
    (μ : PositiveRationalLaw X) (ν : PositiveRationalLaw Y)
    (base : X → Y → Bool)
    (activity : SourceConstruction.Items s V → Fin q₂ → Option (Fin s))
    (ξ₀ : Tail s Y)
    (R : Set (Fin w × TaggedColumn q₁ q₂ s Y))
    (O : Set (Fin w → RawRow q₁ q₂ s X (SourceConstruction.Items s V)))
    (e : Fin k → Fin w) (p : Fin k → Fin s) (tag : Fin k → Bool)
    (u s₀ κ H l : ℕ) (δ D x : ℝ)
    (hw : 0 < w) (hk : 0 < k) (hu : u = 2 * k) (huw : u ≤ w)
    (hD : 1 ≤ D) (hδ : 0 < δ)
    (hδlow : D / (2 * (w : ℝ)) ≤ δ)
    (hsize : 16 * (s₀ : ℝ) * (κ : ℝ) ≤ (u : ℝ) * δ)
    (hx : 0 < x) (hxsmall : x ≤ 1 / ((w : ℝ) ^ 2 * (q₂ : ℝ)))
    (hH : 2 ≤ H) (hl : 2 ≤ l)
    (hK : 2 ^ l = 2 * s₀ * κ * q₂)
    (hprofile : RestrictionProfile
      (fun (γ : Word q₁ s Y) a => M₁ base a γ)
      (ν.iid (q₁ + s + 1)).toFiniteLaw
      ((PositiveRationalLaw.uniform (Fin q₁)).prod μ).toFiniteLaw x (H : ℤ))
    (hmass : ∀ t : Fin k, δ / 2 <
      if tag t then (fixedTailLaw ν q₁ q₂ s).toFiniteLaw.prob
        (· ∈ fixedEvent R (e t))
      else (outerLaw ν q₁ q₂ s).toFiniteLaw.prob
        (· ∈ diagonalEvent R (e t)))
    (hcol : (12 / 25 : ℝ) <
      ((templateLaw μ q₁ q₂).toFiniteLaw.iid k).prob
        (· ∈ selectorImage O e p)) :
    H + l ≤ Compression.restrictionD
      (fullInterlace (N base activity ξ₀) w) R O := by
  classical
  have hq : 0 < q₂ := NeZero.pos q₂
  have hδ0 : 0 ≤ δ := hδ.le
  have huR : (u : ℝ) ≤ w := by exact_mod_cast huw
  have hsizeW : 16 * (s₀ : ℝ) * (κ : ℝ) ≤ (w : ℝ) * δ :=
    hsize.trans (mul_le_mul_of_nonneg_right huR hδ0)
  have hKx := Kx_le_quarter w s₀ κ q₂ δ D x hw hq hD
    hδlow hsizeW hxsmall
  have hpow : (2 : ℝ) ^ l * x ≤ δ / 4 := by
    have heq : (2 : ℝ) ^ l = ((2 * s₀ * κ * q₂ : ℕ) : ℝ) := by
      exact_mod_cast hK
    rw [heq]
    exact hKx
  obtain ⟨Q, hQ, hQc⟩ := select_actual_blocks ν R e p tag δ hδ
    u s₀ κ hk hu hsize hmass
  have hhalf : 2 ^ (l - 1) = s₀ * κ * q₂ := by
    have hlEq : l - 1 + 1 = l := by omega
    have hp : 2 ^ l = 2 * 2 ^ (l - 1) := by
      conv_lhs => rw [← hlEq, pow_succ]
      ring
    have hK' : 2 * (s₀ * κ * q₂) = 2 * 2 ^ (l - 1) := by
      calc
        2 * (s₀ * κ * q₂) = 2 * s₀ * κ * q₂ := by ring
        _ = 2 ^ l := hK.symm
        _ = 2 * 2 ^ (l - 1) := hp
    omega
  have hQcard : 2 ^ (l - 1) + 1 ≤ Q.card := by
    rw [hhalf, hQc]
  exact selected_original_capacity_power μ ν base activity ξ₀ R O e p tag
    δ x hδ H l hH hl hx hpow hprofile Q hQ hQcard hcol

/-- A protocol for the *same* original node rectangle cannot fit below the
charged row-ladder bound. The capacity lower bound is derived above from
actual protected images and the joint selector event. -/
theorem incoming_no_short_protocol
    {X V : Type*} [Fintype X] [Fintype Y] [Fintype V]
    [NeZero s] [NeZero q₁] [NeZero q₂]
    (μ : PositiveRationalLaw X) (ν : PositiveRationalLaw Y)
    (base : X → Y → Bool)
    (activity : SourceConstruction.Items s V → Fin q₂ → Option (Fin s))
    (ξ₀ : Tail s Y)
    (R : Set (Fin w × TaggedColumn q₁ q₂ s Y))
    (O : Set (Fin w → RawRow q₁ q₂ s X (SourceConstruction.Items s V)))
    (e : Fin k → Fin w) (p : Fin k → Fin s) (tag : Fin k → Bool)
    (u s₀ κ H l : ℕ) (δ D x : ℝ)
    (hw : 0 < w) (hk : 0 < k) (hu : u = 2 * k) (huw : u ≤ w)
    (hD : 1 ≤ D) (hδ : 0 < δ)
    (hδlow : D / (2 * (w : ℝ)) ≤ δ)
    (hsize : 16 * (s₀ : ℝ) * (κ : ℝ) ≤ (u : ℝ) * δ)
    (hx : 0 < x) (hxsmall : x ≤ 1 / ((w : ℝ) ^ 2 * (q₂ : ℝ)))
    (hH : 2 ≤ H) (hl : 2 ≤ l)
    (hK : 2 ^ l = 2 * s₀ * κ * q₂)
    (hprofile : RestrictionProfile
      (fun (γ : Word q₁ s Y) a => M₁ base a γ)
      (ν.iid (q₁ + s + 1)).toFiniteLaw
      ((PositiveRationalLaw.uniform (Fin q₁)).prod μ).toFiniteLaw x (H : ℤ))
    (hmass : ∀ t : Fin k, δ / 2 <
      if tag t then (fixedTailLaw ν q₁ q₂ s).toFiniteLaw.prob
        (· ∈ fixedEvent R (e t))
      else (outerLaw ν q₁ q₂ s).toFiniteLaw.prob
        (· ∈ diagonalEvent R (e t)))
    (hcol : (12 / 25 : ℝ) <
      ((templateLaw μ q₁ q₂).toFiniteLaw.iid k).prob
        (· ∈ selectorImage O e p))
    (P : Protocol R O Bool)
    (hP : P.Computes (fun row col =>
      fullInterlace (N base activity ξ₀) w row.val col.val))
    (hcost : P.cost < H + l) : False := by
  classical
  have hlower := incoming_capacity_from_guards μ ν base activity ξ₀
    R O e p tag u s₀ κ H l δ D x hw hk hu huw hD hδ hδlow
    hsize hx hxsmall hH hl hK hprofile hmass hcol
  have hupper : Compression.restrictionD
      (fullInterlace (N base activity ξ₀) w) R O ≤ P.cost := by
    change Workspace.Types.CommComplexity.D (fun (row : R) (col : O) =>
      fullInterlace (N base activity ξ₀) w row.val col.val) ≤ P.cost
    exact Nat.sInf_le ⟨P, rfl, hP⟩
  omega

end Paper2.ProtectedIncomingBlocks

#print axioms Paper2.ProtectedIncomingBlocks.more_than_K_blocks
#print axioms Paper2.ProtectedIncomingBlocks.Kx_le_quarter
#print axioms Paper2.ProtectedIncomingBlocks.select_actual_blocks
#print axioms Paper2.ProtectedIncomingBlocks.incomingRepresentative_injective
#print axioms Paper2.ProtectedIncomingBlocks.incomingRepresentative_entry
#print axioms Paper2.ProtectedIncomingBlocks.iid_flatten_prob
#print axioms Paper2.ProtectedIncomingBlocks.selector_image_flatten_mass
#print axioms Paper2.ProtectedIncomingBlocks.selected_original_rectangle_D_le
#print axioms Paper2.ProtectedIncomingBlocks.selected_original_capacity_power
#print axioms Paper2.ProtectedIncomingBlocks.incoming_capacity_from_guards
#print axioms Paper2.ProtectedIncomingBlocks.incoming_no_short_protocol
