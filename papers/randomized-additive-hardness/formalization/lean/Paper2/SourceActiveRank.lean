import Paper2.SourceConstruction
import Paper2.CanonicalSourceLabels

/-!
Executable dense active positions for indexed graphs, relative to the same
item order and source coordinate as `SourceConstruction.orderedActivity`.
This does not alter the opaque coordinate equivalence in the owner.
-/

namespace Paper2.SourceActiveRank

open SourceConstruction CanonicalSourceLabels

private def activeDecision {s n m : ℕ} (edge : Fin m → Bool → Fin n)
    (r : ℕ) (c : SourceItems.SourceCoord (Fin (4 * s)) (Fin m) r)
    (i : Items s (Fin n)) : Decidable (SourceItems.sourceActive edge r c i) := by
  obtain ⟨pad, copy⟩ := c
  cases pad with
  | inr p =>
      dsimp [SourceItems.sourceActive, SourcePadding.repeatedActive,
        SourcePadding.paddedActive]
      infer_instance
  | inl core =>
      obtain ⟨g, e, o⟩ := core
      obtain ⟨ig, item⟩ := i
      cases item with
      | inr aux =>
          dsimp [SourceItems.sourceActive, SourcePadding.repeatedActive,
            SourcePadding.paddedActive, SourceItems.groupedActive, SourceItems.active]
          infer_instance
      | inl v =>
          cases o with
          | none =>
              dsimp [SourceItems.sourceActive, SourcePadding.repeatedActive,
                SourcePadding.paddedActive, SourceItems.groupedActive, SourceItems.active]
              infer_instance
          | some b =>
              dsimp [SourceItems.sourceActive, SourcePadding.repeatedActive,
                SourcePadding.paddedActive, SourceItems.groupedActive, SourceItems.active]
              infer_instance

private instance {s n m : ℕ} (edge : Fin m → Bool → Fin n) (r : ℕ)
    (c : SourceItems.SourceCoord (Fin (4 * s)) (Fin m) r)
    (i : Items s (Fin n)) : Decidable (SourceItems.sourceActive edge r c i) :=
  activeDecision edge r c i

/-- A bounded count of earlier active item indices.  The universe is exactly
the finite public item-index carrier; no choice of an ordering is hidden. -/
def earlierActive {s n m : ℕ} (edge : Fin m → Bool → Fin n) (r : ℕ)
    (i : Items s (Fin n))
    (c : SourceItems.SourceCoord (Fin (4 * s)) (Fin m) r) :
    Finset (Fin (Fintype.card (Items s (Fin n)))) :=
  Finset.univ.filter (fun j =>
    j < itemOrder s n i ∧
      SourceItems.sourceActive edge r c ((itemOrder s n).symm j))

/-- The scan returns `none` precisely on inactive items.  On an active item,
the count of earlier active indices is bounded by `s` using the source's
already-derived active-cardinality theorem. -/
def scanActivity {s n m : ℕ} [NeZero s]
    (edge : Fin m → Bool → Fin n) (hs : 3 ≤ s) (r : ℕ)
    (i : Items s (Fin n))
    (c : SourceItems.SourceCoord (Fin (4 * s)) (Fin m) r) : Option (Fin s) :=
  if h : SourceItems.sourceActive edge r c i then
    some ⟨(earlierActive edge r i c).card, by
      have hmem : itemOrder s n i ∈
          SourceConstruction.activeLabels (itemOrder s n) edge r c := by
        simp [SourceConstruction.activeLabels, h]
      have hproper : earlierActive edge r i c ⊂
          SourceConstruction.activeLabels (itemOrder s n) edge r c := by
        constructor
        · intro j hj
          simp only [earlierActive, Finset.mem_filter, Finset.mem_univ, true_and] at hj
          simp [SourceConstruction.activeLabels, hj.2]
        · intro hle
          have : itemOrder s n i ∈ earlierActive edge r i c := hle hmem
          simp [earlierActive] at this
      have hlt := Finset.card_lt_card hproper
      exact lt_of_lt_of_le hlt
        (SourceConstruction.activeLabels_card_le (itemOrder s n) edge hs r c)⟩
  else none

/-- For a finite linearly ordered active set, the inverse increasing ordinal
is the number of its members below the queried member. -/
private theorem rank_eq_earlier {N : ℕ} (A : Finset (Fin N)) (x : A) :
    (A.filter (· < x.val)).card = ((A.orderIsoOfFin rfl).symm x).val := by
  classical
  let e := A.orderIsoOfFin rfl
  let k := e.symm x
  have hcard : (A.filter (· < x.val)).card = (Finset.Iio k).card := by
    apply Finset.card_bij
      (fun a ha => e.symm ⟨a, (Finset.mem_filter.mp ha).1⟩)
    · intro a ha
      have hlt : (⟨a, (Finset.mem_filter.mp ha).1⟩ : A) < x :=
        (Finset.mem_filter.mp ha).2
      exact Finset.mem_Iio.mpr (e.symm.strictMono hlt)
    · intro a ha b hb he
      exact congrArg Subtype.val (e.symm.injective he)
    · intro b hb
      refine ⟨(e b).val, ?_, ?_⟩
      · apply Finset.mem_filter.mpr
        refine ⟨(e b).property, ?_⟩
        simpa [k] using e.strictMono (Finset.mem_Iio.mp hb)
      · simp
  simpa [k, Fin.card_Iio] using hcard

theorem scanActivity_eq_orderedActivity {s n m : ℕ} [NeZero s]
    (edge : Fin m → Bool → Fin n) (hs : 3 ≤ s) (r : ℕ)
    (i : Items s (Fin n))
    (c : SourceItems.SourceCoord (Fin (4 * s)) (Fin m) r) :
    scanActivity edge hs r i c =
      SourceConstruction.orderedActivity (itemOrder s n) edge hs r i c := by
  let A := SourceConstruction.activeLabels (itemOrder s n) edge r c
  by_cases h : SourceItems.sourceActive edge r c i
  · have hmem : itemOrder s n i ∈ A := by
      simp [A, SourceConstruction.activeLabels, h]
    have hscan : earlierActive edge r i c = A.filter (· < itemOrder s n i) := by
      ext j
      simp [earlierActive, A, SourceConstruction.activeLabels, and_comm]
    simp only [scanActivity, dif_pos h, SourceConstruction.orderedActivity]
    rw [dif_pos hmem]
    congr 1
    apply Fin.ext
    change (earlierActive edge r i c).card =
      ((A.orderIsoOfFin rfl).symm ⟨itemOrder s n i, hmem⟩).val
    exact (congrArg Finset.card hscan).trans
      (rank_eq_earlier A ⟨itemOrder s n i, hmem⟩)
  · have hnot : itemOrder s n i ∉ A := by
      simp [A, SourceConstruction.activeLabels, h]
    simp [scanActivity, h, SourceConstruction.orderedActivity, A, hnot]

/-- The checkable coordinate order is supplied separately, not equated to
the classically chosen owner `coordinateEquiv`. -/
def scanAtCanonical {s n m r q₂ : ℕ} [NeZero s]
    (edge : Fin m → Bool → Fin n) (hs : 3 ≤ s)
    (hq : q₂ = SourceItems.sourceQ0 (Fin (4 * s)) (Fin m) * r)
    (i : Items s (Fin n)) (a : Fin q₂) : Option (Fin s) :=
  scanActivity edge hs r i (coordOrder s m r q₂ hq a)

theorem scanAtCanonical_eq_orderedActivity {s n m r q₂ : ℕ} [NeZero s]
    (edge : Fin m → Bool → Fin n) (hs : 3 ≤ s)
    (hq : q₂ = SourceItems.sourceQ0 (Fin (4 * s)) (Fin m) * r)
    (i : Items s (Fin n)) (a : Fin q₂) :
    scanAtCanonical edge hs hq i a =
      SourceConstruction.orderedActivity (itemOrder s n) edge hs r i
        (coordOrder s m r q₂ hq a) :=
  scanActivity_eq_orderedActivity edge hs r i _

def parallelEdge : Fin 2 → Bool → Fin 2 := fun _ b => if b then 1 else 0

-- Two indexed parallel edge occurrences have different coordinate labels.
#eval scanAtCanonical parallelEdge (s := 4) (r := 1) (q₂ := 128)
  (by decide) (by decide) (⟨0, by decide⟩, .inl ⟨0, by decide⟩)
  ⟨0, by decide⟩
#eval scanAtCanonical parallelEdge (s := 4) (r := 1) (q₂ := 128)
  (by decide) (by decide) (⟨0, by decide⟩, .inl ⟨0, by decide⟩)
  ⟨3, by decide⟩
-- Padding, another group, and empty edge carrier are inactive.
#eval scanAtCanonical parallelEdge (s := 4) (r := 1) (q₂ := 128)
  (by decide) (by decide) (⟨0, by decide⟩, .inl ⟨0, by decide⟩)
  ⟨100, by decide⟩
#eval scanAtCanonical parallelEdge (s := 4) (r := 1) (q₂ := 128)
  (by decide) (by decide) (⟨0, by decide⟩, .inr ⟨0, by decide⟩)
  ⟨0, by decide⟩
#eval scanAtCanonical parallelEdge (s := 4) (r := 1) (q₂ := 128)
  (by decide) (by decide) (⟨1, by decide⟩, .inr ⟨0, by decide⟩)
  ⟨0, by decide⟩
#eval scanAtCanonical parallelEdge (s := 4) (r := 2) (q₂ := 256)
  (by decide) (by decide) (⟨0, by decide⟩, .inl ⟨0, by decide⟩)
  ⟨0, by decide⟩
#eval scanAtCanonical parallelEdge (s := 4) (r := 2) (q₂ := 256)
  (by decide) (by decide) (⟨0, by decide⟩, .inl ⟨0, by decide⟩)
  ⟨1, by decide⟩
#eval scanAtCanonical (s := 4) (n := 2) (m := 0) (r := 2) (q₂ := 2)
  (fun e _ => Fin.elim0 e) (by decide) (by decide)
  (⟨0, by decide⟩, .inr ⟨0, by decide⟩) ⟨0, by decide⟩

#print axioms scanActivity_eq_orderedActivity
#print axioms scanAtCanonical_eq_orderedActivity

end Paper2.SourceActiveRank
