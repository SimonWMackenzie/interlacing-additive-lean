import CurrentAdditive.EdgeMatrixProductionConjugacy

namespace CurrentAdditive.LiteralEdgeEncoder

open Paper2 SourceMatrix

def itemLaw (s n : ℕ) (hs : 4 ≤ s) (hn : 0 < n) :
    PositiveRationalLaw (Items s n) where
  weight i := match i.2 with
    | .inl _ => (1 : ℚ) / (2 * (4*s) * n)
    | .inr _ => (1 : ℚ) / (2 * (4*s) * ((s-3 : ℕ) : ℚ))
  positive i := by
    have hs' : (0 : ℚ) < s := by exact_mod_cast (by omega : 0 < s)
    have hn' : (0 : ℚ) < n := by exact_mod_cast hn
    have ha' : (0 : ℚ) < ((s-3 : ℕ) : ℚ) := by exact_mod_cast (by omega : 0 < s-3)
    cases i.2 <;> positivity
  total := by
    have hs' : (s : ℚ) ≠ 0 := by exact_mod_cast (by omega : s ≠ 0)
    have hn' : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
    have ha' : ((s-3 : ℕ) : ℚ) ≠ 0 := by exact_mod_cast (by omega : s-3 ≠ 0)
    simp only [Items, EdgeSourceMatrix.Items, EdgeSource.Item, SourceItems.Item]
    rw [Fintype.sum_prod_type]
    simp only [SourceItems.LocalItem, Fintype.sum_sum_type]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    simp only [Nat.cast_mul, Nat.cast_ofNat]
    field_simp
    <;> ring

/-- The actual public item law, with the same equal vertex/auxiliary split
as the conditional source-row law in def:source-matrix. -/
def indexedItemLaw (s n : ℕ) (hs : 4 ≤ s) (hn : 0 < n) :
    PositiveRationalLaw (Fin (4*s*(n+(s-3)))) where
  weight j := (itemLaw s n hs hn).weight ((itemNumber s n).symm j)
  positive j := (itemLaw s n hs hn).positive _
  total := ((itemNumber s n).symm.sum_comp (itemLaw s n hs hn).weight).trans
    (itemLaw s n hs hn).total

def indexedActivity {s n m r : ℕ} [NeZero s] (hs : 3 ≤ s)
    (e : Fin m → Bool → Fin n) :
    Fin (4*s*(n+(s-3))) → Fin (Width s m r) → Option (Fin s) :=
  fun i a => activity hs e ((itemNumber s n).symm i) a

noncomputable def indexedAssignment {s n : ℕ} (hs : 3 ≤ s) (colour : Fin n → Fin 3) :
    Fin (4*s*(n+(s-3))) → Fin s :=
  fun i => SourceItems.yesAssignment hs colour ((itemNumber s n).symm i)

theorem indexedActivity_collisionFree {s n m r : ℕ} [NeZero s]
    (hs : 3 ≤ s) (e : Fin m → Bool → Fin n) (colour : Fin n → Fin 3)
    (proper : ∀ j, colour (e j false) ≠ colour (e j true)) :
    CollisionFree (indexedAssignment hs colour) (indexedActivity (r := r) hs e) := by
  intro a i j b b' hi hj heq
  have hai := (EdgeSourceMatrix.orderedActivity_some_iff (itemOrder s n) e hs r
    ((itemNumber s n).symm i) ((coordinateNumber s m r).symm a)).mp
      ⟨b, (activity_eq_ordered hs e _ a).symm.trans hi⟩
  have haj := (EdgeSourceMatrix.orderedActivity_some_iff (itemOrder s n) e hs r
    ((itemNumber s n).symm j) ((coordinateNumber s m r).symm a)).mp
      ⟨b', (activity_eq_ordered hs e _ a).symm.trans hj⟩
  apply (itemNumber s n).symm.injective
  exact EdgeSource.source_yes e hs r colour proper _ hai haj heq

@[simp] theorem indexedItemLaw_vertex (s n : ℕ) (hs : 4 ≤ s) (hn : 0 < n)
    (g : Fin (4*s)) (v : Fin n) :
    (indexedItemLaw s n hs hn).weight (itemNumber s n (g,.inl v)) =
      (1 : ℚ) / (2*(4*s)*n) := by
  simp [indexedItemLaw, itemLaw]

@[simp] theorem indexedItemLaw_auxiliary (s n : ℕ) (hs : 4 ≤ s) (hn : 0 < n)
    (g : Fin (4*s)) (a : Fin (s-3)) :
    (indexedItemLaw s n hs hn).weight (itemNumber s n (g,.inr a)) =
      (1 : ℚ) / (2*(4*s)*((s-3 : ℕ) : ℚ)) := by
  simp [indexedItemLaw, itemLaw]

#print axioms indexedItemLaw
#print axioms indexedActivity_collisionFree

end CurrentAdditive.LiteralEdgeEncoder
