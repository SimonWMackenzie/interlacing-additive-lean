import EthInapproximability.CurrentPaper.GraphVectors
import Mathlib.Combinatorics.Pigeonhole

/-!
# Surviving graph items on actual branches

Source: locked replacement v8, `A-stage4-details.tex`,
`lem:paper-protected-preparation`, the paragraph defining `L_src` and assigning
surviving graph items to the actual Alice prefix (lines 434--457).

The copy embeddings and retained set below are literal finite inputs.  A branch
function acts on these inputs, not on independently chosen projected rows.  The
prefix geometry and the subsequent communication lower bounds are separate.
-/

noncomputable section

namespace EthInapproximability.CurrentPaper.ProtectedGraphItems

open scoped BigOperators Classical
open Construction

universe u v w z

/-- The source threshold `t = ceil(x*m)` leaves strictly fewer than half the
rows below `s*(t-1)+1`, including when `x*m` is an integer. -/
theorem source_threshold_half {s m : ℕ} {x : ℝ}
    (hs : 0 < s) (hm : 0 < m) (hx : 0 < x) (hcap : x ≤ 1 / (2 * (s : ℝ))) :
    0 < ⌈x * m⌉₊ ∧ 2 * (s * (⌈x * m⌉₊ - 1)) < m := by
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have ht : 0 < ⌈x * m⌉₊ := Nat.ceil_pos.mpr (mul_pos hx hmR)
  have hc := Nat.ceil_lt_add_one (le_of_lt (mul_pos hx hmR))
  have hsub : ((⌈x * m⌉₊ - 1 : ℕ) : ℝ) < x * m := by
    rw [Nat.cast_sub (by omega), Nat.cast_one]
    linarith
  have hbound : 2 * (s : ℝ) * x ≤ 1 := by
    have h := (le_div_iff₀ (show (0 : ℝ) < 2 * s by positivity)).mp hcap
    nlinarith
  have hmul := mul_lt_mul_of_pos_left hsub (show (0 : ℝ) < 2 * s by positivity)
  have hmax := mul_le_mul_of_nonneg_right hbound hmR.le
  refine ⟨ht, ?_⟩
  exact_mod_cast (show (2 : ℝ) * (s * ((⌈x * m⌉₊ - 1 : ℕ) : ℝ)) < m by nlinarith)

section Copies

variable {I : Type u} {X : Type v} {K : Type w} {C : Type z}
  [Fintype I] [Fintype X] [Fintype K] [Fintype C]

/-- Distinct original rows with at least one retained physical copy. -/
def survivingRows (e : I × (X × K) ↪ C) (A : Finset C) (i : I) : Finset X :=
  Finset.univ.filter fun x => ∃ k, e (i, (x, k)) ∈ A

/-- The actual removed copies of one item. -/
def deletedItemCopies (e : I × (X × K) ↪ C) (A : Finset C) (i : I) : Finset C :=
  ((Finset.univ : Finset (X × K)).image fun z => e (i, z)) \ A

def badItems (e : I × (X × K) ↪ C) (A : Finset C) (L : ℕ) : Finset I :=
  Finset.univ.filter fun i => (survivingRows e A i).card < L

@[simp] theorem mem_survivingRows (e : I × (X × K) ↪ C) (A : Finset C)
    (i : I) (x : X) : x ∈ survivingRows e A i ↔ ∃ k, e (i, (x, k)) ∈ A := by
  simp [survivingRows]

@[simp] theorem mem_badItems (e : I × (X × K) ↪ C) (A : Finset C)
    (L : ℕ) (i : I) : i ∈ badItems e A L ↔ (survivingRows e A i).card < L := by
  simp [badItems]

/-- Removing every copy of an original row incurs its full copy multiplicity. -/
theorem missing_rows_charge (e : I × (X × K) ↪ C) (A : Finset C) (i : I) :
    (Fintype.card X - (survivingRows e A i).card) * Fintype.card K ≤
      (deletedItemCopies e A i).card := by
  let S := (Finset.univ \ survivingRows e A i) ×ˢ (Finset.univ : Finset K)
  have hinj : Function.Injective (fun z : X × K => e (i, z)) := by
    intro z z' h
    exact congrArg Prod.snd (e.injective h)
  have hsub : S.image (fun z => e (i, z)) ⊆ deletedItemCopies e A i := by
    intro c hc
    obtain ⟨⟨x, k⟩, hxk, rfl⟩ := Finset.mem_image.mp hc
    have hx : x ∉ survivingRows e A i := (Finset.mem_sdiff.mp
      (Finset.mem_product.mp hxk).1).2
    refine Finset.mem_sdiff.mpr ⟨Finset.mem_image.mpr
      ⟨(x, k), Finset.mem_univ _, rfl⟩, ?_⟩
    intro h
    exact hx ((mem_survivingRows ..).2 ⟨k, h⟩)
  have h := Finset.card_le_card hsub
  rw [Finset.card_image_of_injective _ hinj] at h
  simpa [S, Finset.card_sdiff_of_subset (Finset.subset_univ _)] using h

/-- Copies belonging to different graph items are disjoint actual inputs. -/
theorem deletedItemCopies_disjoint (e : I × (X × K) ↪ C) (A : Finset C)
    {i j : I} (hij : i ≠ j) :
    Disjoint (deletedItemCopies e A i) (deletedItemCopies e A j) := by
  rw [Finset.disjoint_left]
  intro c hc hd
  obtain ⟨x, _, hx⟩ := Finset.mem_image.mp (Finset.mem_sdiff.mp hc).1
  obtain ⟨y, _, hy⟩ := Finset.mem_image.mp (Finset.mem_sdiff.mp hd).1
  exact hij (congrArg Prod.fst (e.injective (hx.trans hy.symm)))

/-- Charges from any collection of items fit inside the global deletion. -/
theorem sum_deletedItemCopies_le (e : I × (X × K) ↪ C) (A : Finset C)
    (J : Finset I) :
    ∑ i ∈ J, (deletedItemCopies e A i).card ≤
      ((Finset.univ : Finset C) \ A).card := by
  rw [← Finset.card_biUnion (fun i _ j _ hij => deletedItemCopies_disjoint e A hij)]
  apply Finset.card_le_card
  intro c hc
  obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hc
  exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, (Finset.mem_sdiff.mp hi).2⟩

/-- A bad item loses at least half of its additional group. The strict
parameter margin can be weakened here since the global deletion gate is strict. -/
theorem bad_item_half_charge (e : I × (X × K) ↪ C) (A : Finset C)
    {L : ℕ} (hL : 0 < L) (hhalf : 2 * (L - 1) ≤ Fintype.card X)
    {i : I} (hi : i ∈ badItems e A L) :
    Fintype.card X * Fintype.card K ≤ 2 * (deletedItemCopies e A i).card := by
  have hs := Finset.card_le_univ (survivingRows e A i)
  have hbad := (mem_badItems ..).1 hi
  have hrow : Fintype.card X ≤ 2 * (Fintype.card X - (survivingRows e A i).card) := by
    omega
  have hmul := Nat.mul_le_mul_right (Fintype.card K) hrow
  have hcharge := missing_rows_charge e A i
  nlinarith

theorem bad_items_half_charge (e : I × (X × K) ↪ C) (A : Finset C)
    {L : ℕ} (hL : 0 < L) (hhalf : 2 * (L - 1) ≤ Fintype.card X) :
    (badItems e A L).card * (Fintype.card X * Fintype.card K) ≤
      2 * ((Finset.univ : Finset C) \ A).card := by
  have hsum := Finset.sum_le_sum (fun i hi => bad_item_half_charge e A hL hhalf hi)
  have htotal := sum_deletedItemCopies_le e A (badItems e A L)
  simp only [Finset.sum_const, smul_eq_mul, ← Finset.mul_sum] at hsum
  omega

/-- The deletion gate is on removed physical copies; the conclusion bounds
bad original items and can be used with the guarded graph-source theorem. -/
theorem bad_items_lt_of_deletion (e : I × (X × K) ↪ C) (A : Finset C)
    {L : ℕ} (hL : 0 < L) (hhalf : 2 * (L - 1) ≤ Fintype.card X)
    (hX : 0 < Fintype.card X) (hK : 0 < Fintype.card K) {b : ℚ}
    (hdel : 2 * (((Finset.univ : Finset C) \ A).card : ℚ) <
      b * (Fintype.card X * Fintype.card K : ℕ)) :
    ((badItems e A L).card : ℚ) < b := by
  have hc : ((badItems e A L).card : ℚ) *
      (Fintype.card X * Fintype.card K : ℕ) ≤
      2 * (((Finset.univ : Finset C) \ A).card : ℚ) := by
    exact_mod_cast bad_items_half_charge e A hL hhalf
  have hp : (0 : ℚ) < (Fintype.card X * Fintype.card K : ℕ) := by
    exact_mod_cast Nat.mul_pos hX hK
  exact (mul_lt_mul_iff_left₀ hp).mp (hc.trans_lt hdel)

/-- Choose one retained physical copy per surviving original row. -/
theorem exists_row_representatives [Nonempty K]
    (e : I × (X × K) ↪ C) (A : Finset C) (i : I) :
    ∃ rep : X → K, ∀ x ∈ survivingRows e A i, e (i, (x, rep x)) ∈ A := by
  let rep : X → K := fun x => if h : x ∈ survivingRows e A i then
    ((mem_survivingRows ..).1 h).choose else Classical.choice inferInstance
  exact ⟨rep, fun x hx => by
    dsimp [rep]
    rw [dif_pos hx]
    exact ((mem_survivingRows ..).1 hx).choose_spec⟩

/-- Pigeonhole on representatives of distinct original rows, using the actual
physical branch function. No desired witness set is assumed. -/
theorem branch_representatives [Nonempty K]
    (e : I × (X × K) ↪ C) (A : Finset C) (branch : C → Fin s)
    {t : ℕ} (ht : 0 < t) (i : I)
    (hi : s * (t - 1) + 1 ≤ (survivingRows e A i).card) :
    ∃ b : Fin s, ∃ Z : Finset X, ∃ rep : X → K,
      t ≤ Z.card ∧ Z ⊆ survivingRows e A i ∧
      ∀ x ∈ Z, e (i, (x, rep x)) ∈ A ∧ branch (e (i, (x, rep x))) = b := by
  obtain ⟨rep, hrep⟩ := exists_row_representatives e A i
  obtain ⟨b, _, hb⟩ := Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to
    (s := survivingRows e A i) (t := (Finset.univ : Finset (Fin s)))
    (f := fun x => branch (e (i, (x, rep x))))
    (fun _ _ => Finset.mem_univ _) (n := t - 1) (by simpa using hi)
  refine ⟨b, (survivingRows e A i).filter (fun x => branch (e (i, (x, rep x))) = b),
    rep, by omega, Finset.filter_subset _ _, ?_⟩
  intro x hx
  exact ⟨hrep x (Finset.mem_filter.mp hx).1, (Finset.mem_filter.mp hx).2⟩

/-- These item assignments are genuine branches of retained representatives.
Items below the threshold are not used and receive an arbitrary branch label. -/
theorem assign_surviving_items [Nonempty K]
    (e : I × (X × K) ↪ C) (A : Finset C) (branch : C → Fin s)
    (hs : 0 < s) {t : ℕ} (ht : 0 < t) :
    ∃ φ : I → Fin s, ∀ i ∉ badItems e A (s * (t - 1) + 1),
      ∃ Z : Finset X, ∃ rep : X → K,
      t ≤ Z.card ∧ Z ⊆ survivingRows e A i ∧
      ∀ x ∈ Z, e (i, (x, rep x)) ∈ A ∧ branch (e (i, (x, rep x))) = φ i := by
  have hall (i : I) : ∃ b : Fin s, i ∉ badItems e A (s * (t - 1) + 1) →
      ∃ Z : Finset X, ∃ rep : X → K,
      t ≤ Z.card ∧ Z ⊆ survivingRows e A i ∧
      ∀ x ∈ Z, e (i, (x, rep x)) ∈ A ∧ branch (e (i, (x, rep x))) = b := by
    by_cases hi : i ∈ badItems e A (s * (t - 1) + 1)
    · exact ⟨⟨0, hs⟩, fun h => False.elim (h hi)⟩
    · have hc : s * (t - 1) + 1 ≤ (survivingRows e A i).card := by
        simpa only [mem_badItems, not_lt] using hi
      obtain ⟨b, hb⟩ := branch_representatives e A branch ht i hc
      exact ⟨b, fun _ => hb⟩
  choose φ hφ using hall
  exact ⟨φ, hφ⟩

end Copies

section PhysicalGroups

variable {X : Type u} [Fintype X]

/-- Multiplicity in the additional vertex group (support label 2). -/
def vertexMultiplicity (s L nv nb : ℕ) : ℕ :=
  WeightedDuplication.copies
    (WeightedDuplication.rowSupport (RawRows s L nv nb X) (TemplateSupport.{u} s L)
      (VertexRows nv X) (AuxiliaryRows nb X)) WeightedDuplication.rowWeight 2

/-- Multiplicity in the additional auxiliary group (support label 3). -/
def auxiliaryMultiplicity (s L nv nb : ℕ) : ℕ :=
  WeightedDuplication.copies
    (WeightedDuplication.rowSupport (RawRows s L nv nb X) (TemplateSupport.{u} s L)
      (VertexRows nv X) (AuxiliaryRows nb X)) WeightedDuplication.rowWeight 3

/-- These are additional graph rows, not copies selected from the full group. -/
def vertexEmbedding (s L nv nb : ℕ) :
    Fin nv × (X × Fin (vertexMultiplicity (X := X) s L nv nb)) ↪
      ProtectedRows s L nv nb X where
  toFun z := ⟨2, ((z.1, z.2.1), z.2.2)⟩
  inj' := by
    rintro ⟨i, x, k⟩ ⟨j, y, l⟩ h
    have hh : ((i, x), k) = ((j, y), l) :=
      eq_of_heq (Sigma.mk.inj_iff.mp h).2
    cases hh
    rfl

def auxiliaryEmbedding (s L nv nb : ℕ) :
    Fin nb × (X × Fin (auxiliaryMultiplicity (X := X) s L nv nb)) ↪
      ProtectedRows s L nv nb X where
  toFun z := ⟨3, ((z.1, z.2.1), z.2.2)⟩
  inj' := by
    rintro ⟨i, x, k⟩ ⟨j, y, l⟩ h
    have hh : ((i, x), k) = ((j, y), l) :=
      eq_of_heq (Sigma.mk.inj_iff.mp h).2
    cases hh
    rfl

theorem vertexMultiplicity_pos [Nonempty X] (s L nv nb : ℕ)
    (hs : 0 < s) (hL : 0 < L) (hv : 0 < nv) (hb : 0 < nb) :
    0 < vertexMultiplicity (X := X) s L nv nb := by
  letI : Nonempty (Fin s) := ⟨⟨0, hs⟩⟩
  letI : Nonempty (Fin L) := ⟨⟨0, hL⟩⟩
  letI : Nonempty (Fin nv) := ⟨⟨0, hv⟩⟩
  letI : Nonempty (Fin nb) := ⟨⟨0, hb⟩⟩
  exact WeightedDuplication.copies_pos _ _ WeightedDuplication.rowWeight_pos
    (WeightedDuplication.rowSupport_card_pos _ _ _ _) 2

theorem auxiliaryMultiplicity_pos [Nonempty X] (s L nv nb : ℕ)
    (hs : 0 < s) (hL : 0 < L) (hv : 0 < nv) (hb : 0 < nb) :
    0 < auxiliaryMultiplicity (X := X) s L nv nb := by
  letI : Nonempty (Fin s) := ⟨⟨0, hs⟩⟩
  letI : Nonempty (Fin L) := ⟨⟨0, hL⟩⟩
  letI : Nonempty (Fin nv) := ⟨⟨0, hv⟩⟩
  letI : Nonempty (Fin nb) := ⟨⟨0, hb⟩⟩
  exact WeightedDuplication.copies_pos _ _ WeightedDuplication.rowWeight_pos
    (WeightedDuplication.rowSupport_card_pos _ _ _ _) 3

/-- Evaluating an additional vertex copy gives the intended graph entry on
the very same physical column. -/
@[simp] theorem protected_vertex_entry {Y : Type u} [Fintype Y]
    (R : X → Y → Bool) (a s q L nv nb : ℕ) (hs : 0 < s)
    (family : SecondFamily a q L X) (order : ItemOrder nv nb)
    (vectors : Fin (nv + nb) → Fin q → Bool)
    (cap : ∀ α, (activeItems vectors α).card ≤ s)
    (i : Fin nv) (x : X) (k : Fin (vertexMultiplicity (X := X) s L nv nb))
    (c : ProtectedColumns a s q Y) :
    protectedMatrix R a s q L nv nb hs family order vectors cap c
      (vertexEmbedding s L nv nb (i, (x, k))) =
    graphEntry R hs vectors cap (vertexIndex order i) x
      (WeightedDuplication.columnForget diagonal c) := rfl

@[simp] theorem protected_auxiliary_entry {Y : Type u} [Fintype Y]
    (R : X → Y → Bool) (a s q L nv nb : ℕ) (hs : 0 < s)
    (family : SecondFamily a q L X) (order : ItemOrder nv nb)
    (vectors : Fin (nv + nb) → Fin q → Bool)
    (cap : ∀ α, (activeItems vectors α).card ≤ s)
    (i : Fin nb) (x : X) (k : Fin (auxiliaryMultiplicity (X := X) s L nv nb))
    (c : ProtectedColumns a s q Y) :
    protectedMatrix R a s q L nv nb hs family order vectors cap c
      (auxiliaryEmbedding s L nv nb (i, (x, k))) =
    graphEntry R hs vectors cap (auxiliaryIndex order i) x
      (WeightedDuplication.columnForget diagonal c) := rfl

/-- The additional vertex group has exactly mass `2^-22` in the full
physical carrier; this multiplicative identity also covers zero carriers. -/
theorem vertex_group_card (s L nv nb : ℕ) :
    Fintype.card (ProtectedRows s L nv nb X) =
      2 ^ 22 * (nv * Fintype.card X * vertexMultiplicity (X := X) s L nv nb) := by
  let S := WeightedDuplication.rowSupport (RawRows s L nv nb X)
    (TemplateSupport.{u} s L) (VertexRows nv X) (AuxiliaryRows nb X)
  have hg := WeightedDuplication.card_group S WeightedDuplication.rowWeight 2
  let e : WeightedDuplication.Group S WeightedDuplication.rowWeight 2 ≃
      ((Fin nv × X) × Fin (vertexMultiplicity (X := X) s L nv nb)) := Equiv.refl _
  have hg' : nv * Fintype.card X * vertexMultiplicity (X := X) s L nv nb =
      ∏ i, Fintype.card (S i) := by
    calc
      _ = Fintype.card ((Fin nv × X) ×
          Fin (vertexMultiplicity (X := X) s L nv nb)) := by
        simp only [Fintype.card_prod, Fintype.card_fin]
      _ = Fintype.card (WeightedDuplication.Group S WeightedDuplication.rowWeight 2) :=
        (Fintype.card_congr e).symm
      _ = _ := by
        change Fintype.card (WeightedDuplication.Group S WeightedDuplication.rowWeight 2) =
          1 * (∏ i, Fintype.card (S i)) at hg
        simpa only [one_mul] using hg
  rw [hg']
  change Fintype.card (WeightedDuplication.Carrier S WeightedDuplication.rowWeight) = _
  rw [WeightedDuplication.card_carrier]
  norm_num [WeightedDuplication.rowWeight, Fin.sum_univ_succ]

theorem auxiliary_group_card (s L nv nb : ℕ) :
    Fintype.card (ProtectedRows s L nv nb X) =
      2 ^ 22 * (nb * Fintype.card X * auxiliaryMultiplicity (X := X) s L nv nb) := by
  let S := WeightedDuplication.rowSupport (RawRows s L nv nb X)
    (TemplateSupport.{u} s L) (VertexRows nv X) (AuxiliaryRows nb X)
  have hg := WeightedDuplication.card_group S WeightedDuplication.rowWeight 3
  let e : WeightedDuplication.Group S WeightedDuplication.rowWeight 3 ≃
      ((Fin nb × X) × Fin (auxiliaryMultiplicity (X := X) s L nv nb)) := Equiv.refl _
  have hg' : nb * Fintype.card X * auxiliaryMultiplicity (X := X) s L nv nb =
      ∏ i, Fintype.card (S i) := by
    calc
      _ = Fintype.card ((Fin nb × X) ×
          Fin (auxiliaryMultiplicity (X := X) s L nv nb)) := by
        simp only [Fintype.card_prod, Fintype.card_fin]
      _ = Fintype.card (WeightedDuplication.Group S WeightedDuplication.rowWeight 3) :=
        (Fintype.card_congr e).symm
      _ = _ := by
        change Fintype.card (WeightedDuplication.Group S WeightedDuplication.rowWeight 3) =
          1 * (∏ i, Fintype.card (S i)) at hg
        simpa only [one_mul] using hg
  rw [hg']
  change Fintype.card (WeightedDuplication.Carrier S WeightedDuplication.rowWeight) = _
  rw [WeightedDuplication.card_carrier]
  norm_num [WeightedDuplication.rowWeight, Fin.sum_univ_succ]

end PhysicalGroups

section ItemIndices

/-- Surviving items in the same finite indices used by the matrix's vectors. -/
def retainedIndices {nv nb : ℕ} (order : ItemOrder nv nb)
    (badV : Finset (Fin nv)) (badB : Finset (Fin nb)) : Finset (Fin (nv + nb)) :=
  ((Finset.univ \ badV).image (vertexIndex order)) ∪
    ((Finset.univ \ badB).image (auxiliaryIndex order))

@[simp] theorem vertex_mem_retainedIndices {nv nb : ℕ} (order : ItemOrder nv nb)
    (badV : Finset (Fin nv)) (badB : Finset (Fin nb)) (i : Fin nv) :
    vertexIndex order i ∈ retainedIndices order badV badB ↔ i ∉ badV := by
  simp only [retainedIndices, Finset.mem_union, Finset.mem_image,
    Finset.mem_sdiff, Finset.mem_univ, true_and]
  constructor
  · rintro (⟨j, hj, heq⟩ | ⟨j, _, heq⟩)
    · exact (vertexIndex_injective order heq) ▸ hj
    · exact False.elim (vertexIndex_ne_auxiliaryIndex order i j heq.symm)
  · intro hi
    exact Or.inl ⟨i, hi, rfl⟩

@[simp] theorem auxiliary_mem_retainedIndices {nv nb : ℕ} (order : ItemOrder nv nb)
    (badV : Finset (Fin nv)) (badB : Finset (Fin nb)) (i : Fin nb) :
    auxiliaryIndex order i ∈ retainedIndices order badV badB ↔ i ∉ badB := by
  simp only [retainedIndices, Finset.mem_union, Finset.mem_image,
    Finset.mem_sdiff, Finset.mem_univ, true_and]
  constructor
  · rintro (⟨j, _, heq⟩ | ⟨j, hj, heq⟩)
    · exact False.elim (vertexIndex_ne_auxiliaryIndex order j i heq)
    · exact (auxiliaryIndex_injective order heq) ▸ hj
  · intro hi
    exact Or.inr ⟨i, hi, rfl⟩

def combinedAssignment {nv nb s : ℕ} (order : ItemOrder nv nb)
    (φv : Fin nv → Fin s) (φb : Fin nb → Fin s) : Fin (nv + nb) → Fin s :=
  fun i => Fin.addCases φv φb (order.symm i)

@[simp] theorem combinedAssignment_vertex {nv nb s : ℕ} (order : ItemOrder nv nb)
    (φv : Fin nv → Fin s) (φb : Fin nb → Fin s) (i : Fin nv) :
    combinedAssignment order φv φb (vertexIndex order i) = φv i := by
  simp [combinedAssignment, vertexIndex]

@[simp] theorem combinedAssignment_auxiliary {nv nb s : ℕ} (order : ItemOrder nv nb)
    (φv : Fin nv → Fin s) (φb : Fin nb → Fin s) (i : Fin nb) :
    combinedAssignment order φv φb (auxiliaryIndex order i) = φb i := by
  simp [combinedAssignment, auxiliaryIndex]

end ItemIndices

/-- At least `t` distinct original rows have fixed retained physical copies
on the indicated branch. The representative is chosen before any column. -/
def HasRowRepresentatives {I X K C : Type*} [Fintype I] [Fintype X]
    [Fintype K] [Fintype C] (e : I × (X × K) ↪ C) (A : Finset C)
    (branch : C → Fin s) (t : ℕ) (i : I) (b : Fin s) : Prop :=
  ∃ Z : Finset X, ∃ rep : X → K,
    t ≤ Z.card ∧ Z ⊆ survivingRows e A i ∧
    ∀ x ∈ Z, e (i, (x, rep x)) ∈ A ∧ branch (e (i, (x, rep x))) = b

theorem assign_physical_graph_items {X : Type u} [Fintype X] [Nonempty X]
    (s L nv nb : ℕ) (hs : 0 < s) (hL : 0 < L) (hv : 0 < nv) (hb : 0 < nb)
    (order : ItemOrder nv nb) (A : Finset (ProtectedRows s L nv nb X))
    (branch : ProtectedRows s L nv nb X → Fin s) {t : ℕ} (ht : 0 < t) :
    ∃ φ : Fin (nv + nb) → Fin s,
      (∀ i ∉ badItems (vertexEmbedding s L nv nb) A (s * (t - 1) + 1),
        HasRowRepresentatives (vertexEmbedding s L nv nb) A branch t i
          (φ (vertexIndex order i))) ∧
      (∀ i ∉ badItems (auxiliaryEmbedding s L nv nb) A (s * (t - 1) + 1),
        HasRowRepresentatives (auxiliaryEmbedding s L nv nb) A branch t i
          (φ (auxiliaryIndex order i))) := by
  letI : Nonempty (Fin (vertexMultiplicity (X := X) s L nv nb)) :=
    ⟨⟨0, vertexMultiplicity_pos s L nv nb hs hL hv hb⟩⟩
  letI : Nonempty (Fin (auxiliaryMultiplicity (X := X) s L nv nb)) :=
    ⟨⟨0, auxiliaryMultiplicity_pos s L nv nb hs hL hv hb⟩⟩
  obtain ⟨φv, hφv⟩ := assign_surviving_items (vertexEmbedding s L nv nb) A branch hs ht
  obtain ⟨φb, hφb⟩ := assign_surviving_items (auxiliaryEmbedding s L nv nb) A branch hs ht
  refine ⟨combinedAssignment order φv φb, ?_, ?_⟩
  · intro i hi
    simpa only [HasRowRepresentatives, combinedAssignment_vertex] using hφv i hi
  · intro i hi
    simpa only [HasRowRepresentatives, combinedAssignment_auxiliary] using hφb i hi

section SourceWitnesses

open EthInapproximability.ParameterizedNP.GuardedSourceGraph
open EthInapproximability.ParameterizedNP.GuardedSourceSlab

/-- Allocate each existing witness coordinate to one of its witnessing
branches. The resulting sets are disjoint, so their total size is exactly the
source witness count rather than a count with repeated coordinates. -/
theorem disjoint_witness_partition {I Q : Type*} [Fintype I] [Fintype Q]
    (v : I → Q → Bool) (J : Finset I) (φ : I → Fin s) (hs : 0 < s) :
    ∃ U : Fin s → Finset Q,
      (∀ b, ∀ α ∈ U b, 2 ≤ (activeSet v J φ b α).card ∧
        ∃ i ∈ binOf J φ b, v i α = false) ∧
      (∀ b c, b ≠ c → Disjoint (U b) (U c)) ∧
      (∑ b, (U b).card) = (Wit v J φ).card := by
  let owner : Q → Fin s := fun α => if h : α ∈ Wit v J φ then
    ((mem_Wit ..).1 h).choose else ⟨0, hs⟩
  have howner (α : Q) (hα : α ∈ Wit v J φ) :
      2 ≤ (activeSet v J φ (owner α) α).card ∧
        ∃ i ∈ binOf J φ (owner α), v i α = false := by
    dsimp [owner]
    rw [dif_pos hα]
    exact ((mem_Wit ..).1 hα).choose_spec
  let U := fun b => (Wit v J φ).filter fun α => owner α = b
  refine ⟨U, ?_, ?_, ?_⟩
  · intro b α hα
    obtain ⟨hα, hownerα⟩ := Finset.mem_filter.mp hα
    simpa only [hownerα] using howner α hα
  · intro b c hbc
    rw [Finset.disjoint_left]
    intro α hb hc
    exact hbc ((Finset.mem_filter.mp hb).2.symm.trans (Finset.mem_filter.mp hc).2)
  · exact (Finset.card_eq_sum_card_fiberwise
      (s := Wit v J φ) (t := Finset.univ) (f := owner)
      (fun _ _ => Finset.mem_univ _)).symm

variable {V : Type u} {E : Type v} {X : Type w}
  [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
  [Fintype X] [Nonempty X]

/-- Source witness supply after actual physical deletions. Every retained
source item simultaneously has `t` original-row representatives on its assigned
physical branch. This does not claim that these branches form a protocol prefix;
the actual-prefix theorem supplies that interpretation of `branch`.

Both numerical deletion gates refer to the same physical deletion, charged
against the respective additional-group multiplicity. They will be discharged
from the paper's weighted-group masses and chosen tolerances. -/
theorem physical_witness_supply (G : EndpointGraph V E) {s : ℕ} (hs : 4 ≤ s)
    {Δ : ℕ} (hΔ : 0 < Δ) {γ : ℚ} (hγ0 : 0 < γ) (hγ1 : γ ≤ 1)
    (hdeg : ∀ v : V, G.degree v ≤ Δ) (hno : G.SourceNO γ)
    (L : ℕ) (hL : 0 < L) {t : ℕ} (ht : 0 < t)
    (hhalf : 2 * (s * (t - 1)) ≤ Fintype.card X)
    (A : Finset (ProtectedRows s L (GraphVectors.vertexCount V s)
      (GraphVectors.auxiliaryCount s) X))
    (branch : ProtectedRows s L (GraphVectors.vertexCount V s)
      (GraphVectors.auxiliaryCount s) X → Fin s)
    (hdelV : 2 * ((Finset.univ \ A).card : ℚ) <
      ((s : ℚ) / 2 * (G.deltaV γ Δ * Fintype.card V)) *
        (Fintype.card X * vertexMultiplicity (X := X) s L
          (GraphVectors.vertexCount V s) (GraphVectors.auxiliaryCount s) : ℕ))
    (hdelB : 2 * ((Finset.univ \ A).card : ℚ) <
      ((s : ℚ) / 2) *
        (Fintype.card X * auxiliaryMultiplicity (X := X) s L
          (GraphVectors.vertexCount V s) (GraphVectors.auxiliaryCount s) : ℕ)) :
    let badV := badItems (vertexEmbedding s L (GraphVectors.vertexCount V s)
      (GraphVectors.auxiliaryCount s)) A (s * (t - 1) + 1)
    let badB := badItems (auxiliaryEmbedding s L (GraphVectors.vertexCount V s)
      (GraphVectors.auxiliaryCount s)) A (s * (t - 1) + 1)
    let J := retainedIndices (GraphVectors.itemOrder G s) badV badB
    ∃ φ : Fin (GraphVectors.vertexCount V s + GraphVectors.auxiliaryCount s) → Fin s,
      (γ / 24) * (q2 G s : ℚ) ≤
        ((Wit (GraphVectors.vectors G s) J φ).card : ℚ) ∧
      (∀ i ∉ badV, HasRowRepresentatives
        (vertexEmbedding s L (GraphVectors.vertexCount V s) (GraphVectors.auxiliaryCount s))
        A branch t i (φ (vertexIndex (GraphVectors.itemOrder G s) i))) ∧
      (∀ i ∉ badB, HasRowRepresentatives
        (auxiliaryEmbedding s L (GraphVectors.vertexCount V s) (GraphVectors.auxiliaryCount s))
        A branch t i (φ (auxiliaryIndex (GraphVectors.itemOrder G s) i))) := by
  dsimp only
  let nv := GraphVectors.vertexCount V s
  let nb := GraphVectors.auxiliaryCount s
  have hv : 0 < nv := Nat.mul_pos (by omega) G.card_vertex_pos
  have hb : 0 < nb := Nat.mul_pos (by omega) (by omega)
  have hs0 : 0 < s := by omega
  have hhalf' : 2 * (s * (t - 1) + 1 - 1) ≤ Fintype.card X := by
    simpa only [Nat.add_sub_cancel] using hhalf
  have hvK := vertexMultiplicity_pos (X := X) s L nv nb hs0 hL hv hb
  have hbK := auxiliaryMultiplicity_pos (X := X) s L nv nb hs0 hL hv hb
  have hbadV := bad_items_lt_of_deletion (vertexEmbedding s L nv nb) A
    (b := (s : ℚ) / 2 * (G.deltaV γ Δ * Fintype.card V))
    (show 0 < s * (t - 1) + 1 by omega) hhalf' Fintype.card_pos
    (by simpa using hvK) (by
      simpa only [Finset.card_sdiff, Finset.inter_univ,
        Finset.card_univ, Fintype.card_fin, nv, nb] using hdelV)
  have hbadB := bad_items_lt_of_deletion (auxiliaryEmbedding s L nv nb) A
    (b := (s : ℚ) / 2)
    (show 0 < s * (t - 1) + 1 by omega) hhalf' Fintype.card_pos
    (by simpa using hbK) (by
      simpa only [Finset.card_sdiff, Finset.inter_univ,
        Finset.card_univ, Fintype.card_fin, nv, nb] using hdelB)
  obtain ⟨φ, hφv, hφb⟩ := assign_physical_graph_items s L nv nb hs0 hL hv hb
    (GraphVectors.itemOrder G s) A branch ht
  refine ⟨φ, ?_, hφv, hφb⟩
  apply GraphVectors.indexed_witness_of_sourceNO G hs hΔ hγ0 hγ1 hdeg hno
  · simpa only [vertex_mem_retainedIndices, not_not, Finset.filter_mem_eq_inter,
      Finset.univ_inter] using hbadV
  · simpa only [auxiliary_mem_retainedIndices, not_not, Finset.filter_mem_eq_inter,
      Finset.univ_inter] using hbadB

end SourceWitnesses

end EthInapproximability.CurrentPaper.ProtectedGraphItems
