import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Exact counting for a product of indexed families

Source: the third part of `lem:paper-product-extraction` in the locked v8
`A-stage4-details.tex`.  A product label chooses an independent label in each
factor.  A prescribed pattern therefore has exactly the product of the
numbers of local realizing labels.  This module proves that finite counting
identity only; no balancedness or communication lower bound is assumed.

Labels are counted with their multiplicity even when two labels determine
the same tuple.  Empty coordinate slices are retained, so their local event
is the full label set.
-/

namespace EthInapproximability.CurrentPaper.ProductFibreCount

open scoped BigOperators

variable {I Q C Y : Type*}
variable [Fintype I] [Fintype Q] [Fintype C]
variable [DecidableEq I] [DecidableEq Q] [DecidableEq C] [DecidableEq Y]

/-- The constrained coordinates in factor `i`. -/
def slice (J : Finset (I × Q)) (i : I) : Finset Q :=
  Finset.univ.filter fun q => (i, q) ∈ J

/-- Labels in factor `i` that realize its part of the prescribed pattern. -/
def localMatches (S : I → C → Q → Y) (J : Finset (I × Q))
    (a : I × Q → Y) (i : I) : Finset C :=
  Finset.univ.filter fun c => ∀ q ∈ slice J i, S i c q = a (i, q)

/-- Product labels realizing all prescribed coordinates. -/
def globalMatches (S : I → C → Q → Y) (J : Finset (I × Q))
    (a : I × Q → Y) : Finset (I → C) :=
  Finset.univ.filter fun f => ∀ p ∈ J, S p.1 (f p.1) p.2 = a p

omit [Fintype I] in
@[simp] theorem mem_slice (J : Finset (I × Q)) (i : I) (q : Q) :
    q ∈ slice J i ↔ (i, q) ∈ J := by
  simp [slice]

omit [Fintype I] [DecidableEq C] in
@[simp] theorem mem_localMatches (S : I → C → Q → Y)
    (J : Finset (I × Q)) (a : I × Q → Y) (i : I) (c : C) :
    c ∈ localMatches S J a i ↔ ∀ q ∈ slice J i, S i c q = a (i, q) := by
  simp [localMatches]

omit [DecidableEq C] in
@[simp] theorem mem_globalMatches (S : I → C → Q → Y)
    (J : Finset (I × Q)) (a : I × Q → Y) (f : I → C) :
    f ∈ globalMatches S J a ↔ ∀ p ∈ J, S p.1 (f p.1) p.2 = a p := by
  simp [globalMatches]

omit [DecidableEq C] in
/-- The global realization event is a literal Cartesian product of local events. -/
theorem globalMatches_eq_piFinset (S : I → C → Q → Y)
    (J : Finset (I × Q)) (a : I × Q → Y) :
    globalMatches S J a = Fintype.piFinset (localMatches S J a) := by
  ext f
  simp only [mem_globalMatches, Fintype.mem_piFinset, mem_localMatches, mem_slice]
  constructor
  · intro h i q hq
    exact h (i, q) hq
  · intro h p hp
    exact h p.1 p.2 hp

omit [DecidableEq C] in
/-- Exact factorization of the number of realizing indexed product labels. -/
theorem card_globalMatches (S : I → C → Q → Y)
    (J : Finset (I × Q)) (a : I × Q → Y) :
    (globalMatches S J a).card = ∏ i, (localMatches S J a i).card := by
  rw [globalMatches_eq_piFinset, Fintype.card_piFinset]

/-- Reinsert the common factor index into a local coordinate. -/
def pairEmbedding (i : I) : Q ↪ I × Q :=
  ⟨fun q => (i, q), fun _ _ h => Prod.mk.inj h |>.2⟩

omit [Fintype I] in
theorem map_slice (J : Finset (I × Q)) (i : I) :
    (slice J i).map (pairEmbedding i) = J.filter (fun p => p.1 = i) := by
  ext p
  rcases p with ⟨j, q⟩
  simp only [Finset.mem_map, mem_slice, Finset.mem_filter, pairEmbedding,
    Function.Embedding.coeFn_mk, Prod.mk.injEq]
  constructor
  · rintro ⟨q', hq', hi, rfl⟩
    exact ⟨hi ▸ hq', hi.symm⟩
  · rintro ⟨hq, rfl⟩
    exact ⟨q, hq, rfl, rfl⟩

omit [Fintype I] in
theorem card_slice_eq_card_filter (J : Finset (I × Q)) (i : I) :
    (slice J i).card = (J.filter fun p => p.1 = i).card := by
  rw [← map_slice, Finset.card_map]

/-- Every constrained coordinate belongs to exactly one factor. -/
theorem card_eq_sum_slice (J : Finset (I × Q)) :
    J.card = ∑ i, (slice J i).card := by
  simp_rw [card_slice_eq_card_filter]
  exact Finset.card_eq_sum_card_fiberwise (t := Finset.univ) (f := Prod.fst)
    (fun _ _ => Finset.mem_univ _)

omit [Fintype I] in
theorem card_slice_le (J : Finset (I × Q)) (i : I) :
    (slice J i).card ≤ J.card := by
  rw [card_slice_eq_card_filter]
  exact Finset.card_filter_le _ _

omit [Fintype I] [DecidableEq C] in
/-- An unused factor has every indexed label available. -/
theorem localMatches_of_slice_empty (S : I → C → Q → Y)
    (J : Finset (I × Q)) (a : I × Q → Y) (i : I) (h : slice J i = ∅) :
    localMatches S J a i = Finset.univ := by
  simp [localMatches, h]

/-- Factors touched by at least one prescribed coordinate. -/
def activeSlices (J : Finset (I × Q)) : Finset I :=
  Finset.univ.filter fun i => (slice J i).Nonempty

@[simp] theorem mem_activeSlices (J : Finset (I × Q)) (i : I) :
    i ∈ activeSlices J ↔ (slice J i).Nonempty := by
  simp [activeSlices]

/-- A query on `t` coordinates touches at most `t` factors, regardless of
the total number of factors. -/
theorem card_activeSlices_le (J : Finset (I × Q)) :
    (activeSlices J).card ≤ J.card := by
  calc
    (activeSlices J).card = ∑ _i ∈ activeSlices J, 1 := by simp
    _ ≤ ∑ i ∈ activeSlices J, (slice J i).card := by
      apply Finset.sum_le_sum
      intro i hi
      exact Finset.one_le_card.mpr (mem_activeSlices J i |>.mp hi)
    _ ≤ ∑ i, (slice J i).card := by
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun _ _ _ => Nat.zero_le _)
    _ = J.card := (card_eq_sum_slice J).symm

/-- Duplicate labels are counted independently: each of two factors has
two labels realizing `false`, hence the product has four such labels. -/
theorem duplicate_labels_regression :
    (globalMatches
      (fun (_ : Fin 2) (c : Fin 3) (_ : Fin 1) => decide (c.val = 2))
      Finset.univ (fun _ => false)).card = 4 := by
  decide

end EthInapproximability.CurrentPaper.ProductFibreCount
