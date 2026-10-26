import CurrentAdditive.CanonicalWriterCleanup

namespace CurrentAdditive.FiniteFieldConstructor.CanonicalTable

open Paper2.YaoLookup
open EthInapproximability.CurrentPaper.BitMachineClearBank

private theorem cleared_update_member {K : Type*} [DecidableEq K]
    {n : ℕ} (bank : Fin n → K) (S : K → List Bool)
    (a : K) (v : List Bool) (ha : ∃ i, bank i = a) :
    cleared bank (Function.update S a v) = cleared bank S := by
  funext k
  by_cases hk : ∃ i, bank i = k
  · simp [cleared, hk]
  · have hka : k ≠ a := by
      intro h
      obtain ⟨i, hi⟩ := ha
      exact hk ⟨i, hi.trans h.symm⟩
    simp [cleared, hk, hka]

private theorem cleared_update_foreign {K : Type*} [DecidableEq K]
    {n : ℕ} (bank : Fin n → K) (S : K → List Bool)
    (a : K) (v : List Bool) (ha : ∀ i, bank i ≠ a) :
    cleared bank (Function.update S a v) =
      Function.update (cleared bank S) a v := by
  funext k
  by_cases hka : k = a
  · subst k
    simp [cleared, ha]
  · simp [cleared, hka]

private theorem cleared_id_of_blank {K : Type*} [DecidableEq K]
    {n : ℕ} (bank : Fin n → K) (S : K → List Bool)
    (hblank : ∀ i, S (bank i) = []) :
    cleared bank S = S := by
  funext k
  by_cases hk : ∃ i, bank i = k
  · obtain ⟨i, hi⟩ := hk
    simp [cleared, show ∃ j, bank j = k from ⟨i, hi⟩, ← hi, hblank i]
  · simp [cleared, hk]

/-- After one entry is computed, clearing the six temporary coordinates
returns precisely the prepared writer bank with its answer cell filled. -/
theorem canonical_cleanup_bank {v e : ℕ} (t d modulus : ℕ)
    (edges : Fin e → Fin (2 ^ t * 2 ^ t) ↪ Fin v)
    (i : Fin (rowCount v (paddedEdgeBits e) t))
    (j : Fin (columnCount (paddedEdgeBits e) t d)) :
    cleared canonicalCleanupSlots
      (Function.update
        (canonicalCoordinateBank (paddedEdgeBits e) t d modulus
          (le_paddedEdgeCount e) edges i j)
        (.inr 2)
        [numericEntry (paddedEdgeBits e) t d modulus
          (le_paddedEdgeCount e) edges i j]) =
      Function.update
        (canonicalReady (paddedEdgeBits e) t d modulus edges i.val j.val)
        (.inr 2)
        [numericEntry (paddedEdgeBits e) t d modulus
          (le_paddedEdgeCount e) edges i j] := by
  have hanswer : ∀ k : Fin 6, canonicalCleanupSlots k ≠ (.inr 2 : CanonicalCell) := by
    intro k
    fin_cases k <;> decide
  rw [cleared_update_foreign canonicalCleanupSlots _ _ _ hanswer]
  have hmem (a : Fin 6) : ∃ k, canonicalCleanupSlots k = canonicalCleanupSlots a :=
    ⟨a, rfl⟩
  have hbase : cleared canonicalCleanupSlots
      (canonicalReady (paddedEdgeBits e) t d modulus edges i.val j.val) =
      canonicalReady (paddedEdgeBits e) t d modulus edges i.val j.val := by
    apply cleared_id_of_blank
    intro k
    fin_cases k <;> rfl
  unfold canonicalCoordinateBank canonicalDecodedBank
  rw [show canonicalCoordPlace 7 = canonicalCleanupSlots 5 from rfl,
    show canonicalIndexPlace 12 = canonicalCleanupSlots 4 from rfl,
    show canonicalIndexPlace 11 = canonicalCleanupSlots 3 from rfl,
    show canonicalIndexPlace 10 = canonicalCleanupSlots 2 from rfl,
    show canonicalIndexPlace 9 = canonicalCleanupSlots 1 from rfl,
    show canonicalIndexPlace 8 = canonicalCleanupSlots 0 from rfl]
  rw [cleared_update_member canonicalCleanupSlots _ _ _ (hmem 5),
    cleared_update_member canonicalCleanupSlots _ _ _ (hmem 4),
    cleared_update_member canonicalCleanupSlots _ _ _ (hmem 3),
    cleared_update_member canonicalCleanupSlots _ _ _ (hmem 2),
    cleared_update_member canonicalCleanupSlots _ _ _ (hmem 1),
    cleared_update_member canonicalCleanupSlots _ _ _ (hmem 0),
    hbase]

#print axioms canonical_cleanup_bank

end CurrentAdditive.FiniteFieldConstructor.CanonicalTable
