import CurrentAdditive.V38Matrix
import EthInapproximability.CurrentPaper.EncodedGraph

/-!
Executable public indices for the edge-only source construction.
Source: v39 sections/construction.tex, definition def:source-matrix, Activity
and Raw entries; mathematical text identical to v38.
-/

namespace CurrentAdditive.LiteralEdgeEncoder

open EthInapproximability.CurrentPaper
open Paper2 SourceMatrix

abbrev Items (s n : ℕ) := EdgeSourceMatrix.Items s (Fin n)

def itemNumber (s n : ℕ) : Items s n ≃ Fin (4 * s * (n + (s - 3))) :=
  (Equiv.prodCongr (Equiv.refl _) finSumFinEquiv).trans finProdFinEquiv

def itemOrder (s n : ℕ) : Items s n ≃ Fin (Fintype.card (Items s n)) :=
  (itemNumber s n).trans (finCongr (by simp [Items, EdgeSourceMatrix.Items,
    EdgeSource.Item, SourceItems.Item, SourceItems.LocalItem]))

@[simp] theorem itemNumber_vertex (s n : ℕ) (g : Fin (4*s)) (v : Fin n) :
    (itemNumber s n (g, .inl v)).val = v.val + (n + (s-3))*g.val := rfl

@[simp] theorem itemNumber_auxiliary (s n : ℕ) (g : Fin (4*s)) (a : Fin (s-3)) :
    (itemNumber s n (g, .inr a)).val = n + a.val + (n + (s-3))*g.val := rfl

def edge (G : EncodedGraph.Graph) (hG : G.Valid) :
    Fin G.edges.length → Bool → Fin G.vertices := fun e b =>
  if b then ⟨(G.edges[e]).2, (hG _ (List.getElem_mem _)).2.1⟩
  else ⟨(G.edges[e]).1, (hG _ (List.getElem_mem _)).1⟩

theorem edge_loopless (G : EncodedGraph.Graph) (hG : G.Valid)
    (e : Fin G.edges.length) : edge G hG e false ≠ edge G hG e true := by
  intro he
  exact (hG _ (List.getElem_mem _)).2.2 (congrArg Fin.val he)

def paddedNumber (s m : ℕ) :
    SourcePadding.Padded (Fin (4*s) × Fin m)
      (EdgeSource.sourceQ0 (Fin (4*s)) (Fin m)) ≃
      Fin (EdgeSource.sourceQ0 (Fin (4*s)) (Fin m)) :=
  ((Equiv.sumCongr finProdFinEquiv (Equiv.refl _)).trans finSumFinEquiv).trans
    (finCongr (by
      have h := SourcePadding.le_powTwoCeil (4*s*m)
      simpa [EdgeSource.sourceQ0, EdgeSource.Coord] using Nat.add_sub_of_le h))

/-- Each padded coordinate is repeated in consecutive positions. -/
def coordinateNumber (s m r : ℕ) :
    EdgeSource.SourceCoord (Fin (4*s)) (Fin m) r ≃
      Fin (EdgeSource.sourceQ0 (Fin (4*s)) (Fin m) * r) :=
  (Equiv.prodCongr (paddedNumber s m) (Equiv.refl _)).trans finProdFinEquiv

@[simp] theorem coordinateNumber_val (s m r : ℕ)
    (c : EdgeSource.SourceCoord (Fin (4*s)) (Fin m) r) :
    (coordinateNumber s m r c).val = c.2.val + r * (paddedNumber s m c.1).val := rfl

@[simp] theorem coordinateNumber_symm_repeat (s m r : ℕ)
    (a : Fin (EdgeSource.sourceQ0 (Fin (4*s)) (Fin m) * r)) :
    ((coordinateNumber s m r).symm a).2.val = a.val % r := rfl

@[simp] theorem coordinateNumber_symm_base (s m r : ℕ)
    (a : Fin (EdgeSource.sourceQ0 (Fin (4*s)) (Fin m) * r)) :
    (paddedNumber s m ((coordinateNumber s m r).symm a).1).val = a.val / r := by
  exact congrArg Fin.val ((paddedNumber s m).apply_symm_apply _)

def active {s n m r : ℕ} (e : Fin m → Bool → Fin n)
    (a : Fin (EdgeSource.sourceQ0 (Fin (4*s)) (Fin m) * r))
    (i : Items s n) : Bool :=
  match ((coordinateNumber s m r).symm a).1 with
  | .inr _ => false
  | .inl c => decide (i.1 = c.1) &&
      match i.2 with
      | .inl v => decide (v = e c.2 false ∨ v = e c.2 true)
      | .inr _ => true

theorem active_eq {s n m r : ℕ} (e : Fin m → Bool → Fin n)
    (a : Fin (EdgeSource.sourceQ0 (Fin (4*s)) (Fin m) * r))
    (i : Items s n) :
    active e a i = true ↔ EdgeSource.sourceActive e r
      ((coordinateNumber s m r).symm a) i := by
  unfold active EdgeSource.sourceActive SourcePadding.repeatedActive
  cases hc : ((coordinateNumber s m r).symm a).1 with
  | inr j => simp [SourcePadding.paddedActive]
  | inl c =>
    cases hi : i.2 <;> simp [SourcePadding.paddedActive, EdgeSource.active, hi]

def activeLabels {s n m r : ℕ} (e : Fin m → Bool → Fin n)
    (a : Fin (EdgeSource.sourceQ0 (Fin (4*s)) (Fin m) * r)) :
    Finset (Fin (Fintype.card (Items s n))) :=
  Finset.univ.filter (fun j => active e a ((itemOrder s n).symm j) = true)

theorem activeLabels_eq {s n m r : ℕ} (e : Fin m → Bool → Fin n)
    (a : Fin (EdgeSource.sourceQ0 (Fin (4*s)) (Fin m) * r)) :
    activeLabels e a = EdgeSourceMatrix.activeLabels (itemOrder s n) e r
      ((coordinateNumber s m r).symm a) := by
  ext j
  simp [activeLabels, EdgeSourceMatrix.activeLabels, active_eq]

theorem activeLabels_card_le {s n m r : ℕ} [NeZero s] (hs : 3 ≤ s)
    (e : Fin m → Bool → Fin n)
    (a : Fin (EdgeSource.sourceQ0 (Fin (4*s)) (Fin m) * r)) :
    (activeLabels e a).card ≤ s := by
  rw [activeLabels_eq]
  exact EdgeSourceMatrix.activeLabels_card_le _ _ hs _ _

/-- The index in the sorted active-label list is the actual public rank. -/
def activity {s n m r : ℕ} [NeZero s] (hs : 3 ≤ s) (e : Fin m → Bool → Fin n)
    (i : Items s n)
    (a : Fin (EdgeSource.sourceQ0 (Fin (4*s)) (Fin m) * r)) : Option (Fin s) :=
  let A := activeLabels e a
  if hi : itemOrder s n i ∈ A then
    some ⟨A.sort.idxOf (itemOrder s n i),
      (by have h := List.idxOf_lt_length_iff.mpr ((Finset.mem_sort (α := Fin (Fintype.card (Items s n))) (· ≤ ·)).mpr hi)
          rw [Finset.length_sort] at h
          exact h.trans_le (activeLabels_card_le hs e a))⟩
  else none

theorem activity_eq_ordered {s n m r : ℕ} [NeZero s] (hs : 3 ≤ s)
    (e : Fin m → Bool → Fin n) (i : Items s n)
    (a : Fin (EdgeSource.sourceQ0 (Fin (4*s)) (Fin m) * r)) :
    activity hs e i a = EdgeSourceMatrix.orderedActivity (itemOrder s n) e hs r i
      ((coordinateNumber s m r).symm a) := by
  classical
  unfold activity EdgeSourceMatrix.orderedActivity
  simp only [activeLabels_eq]
  split <;> rfl

#print axioms itemOrder
#print axioms coordinateNumber
#print axioms edge_loopless
#print axioms active_eq
#print axioms activity_eq_ordered

end CurrentAdditive.LiteralEdgeEncoder
