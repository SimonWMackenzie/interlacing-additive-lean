import CurrentAdditive.CodeDCompactJoinV2
import CurrentAdditive.SequentialCode
import CurrentAdditive.SequentialSourceCode
import CurrentAdditive.CodeDCanonicalSourceV2

/-!
The compactor's input consists of the actual post-elimination entries,
indexed by the original source positions. The theorem below identifies its
canonical output bytes with SequentialCode's indexed zero deletion. Equal
decoded words remain separate entries because both sides traverse positions.
-/

namespace CurrentAdditive.CodeDCompactSequentialBridge

open CodeDZeroCompactSpecV2 CodeDSourceCodecV2 CodeDCanonicalSourceV2
open SequentialCode
open SequentialSourceCode

def retainedSource {q : Nat} (source : Array ((Fin q → Nat) × ℚ))
    (updated : Array ℚ) : Array ((Fin q → Nat) × ℚ) :=
  ((positiveIndices updated).filterMap (fun i =>
    (source[i]?).map (fun e => (e.1, updated[i]?.getD 0)))).toArray

def updatedAt {q : Nat} (source : Array ((Fin q → Nat) × ℚ))
    (updated : Array ℚ) (i : Nat) : Option Entry :=
  (source[i]?).map (fun e => canonicalEntry (e.1, updated[i]?.getD 0))

def updatedEntries {q : Nat} (source : Array ((Fin q → Nat) × ℚ))
    (updated : Array ℚ) : List Entry :=
  (List.range updated.size).filterMap (updatedAt source updated)

private theorem selected_aux {q : Nat}
    (source : Array ((Fin q → Nat) × ℚ)) (updated : Array ℚ)
    (indices : List Nat) :
    ((indices.filterMap (updatedAt source updated)).filter
      CodeDZeroSelectionV2.keepPositive) =
    (indices.filter (fun i => decide (0 < updated[i]?.getD 0))).filterMap
      (updatedAt source updated) := by
  induction indices with
  | nil => rfl
  | cons i rest ih =>
      simp only [updatedAt] at ih
      cases hs : source[i]? with
      | none =>
          cases hp : decide (0 < updated[i]?.getD 0) <;>
            simp [updatedAt, hs, hp, ih]
      | some e =>
          have hkeep : CodeDZeroSelectionV2.keepPositive
              (canonicalEntry (e.1, updated[i]?.getD 0)) =
              decide (0 < updated[i]?.getD 0) := by
            simp [CodeDZeroSelectionV2.keepPositive,
              canonicalEntry, rawOfRat_value]
          cases hp : decide (0 < updated[i]?.getD 0) <;>
            simp [updatedAt, hs, hp, hkeep, ih]

private theorem mapped_aux {q : Nat}
    (source : Array ((Fin q → Nat) × ℚ)) (updated : Array ℚ)
    (indices : List Nat) :
    (indices.filterMap (fun i =>
      (source[i]?).map (fun e => (e.1, updated[i]?.getD 0)))).map
      canonicalEntry =
    indices.filterMap (updatedAt source updated) := by
  induction indices with
  | nil => rfl
  | cons i rest ih =>
      cases hs : source[i]? with
      | none => simp [updatedAt, hs, ih]
      | some e => simp [updatedAt, hs, ih]

theorem selected_updated_exact {q : Nat}
    (source : Array ((Fin q → Nat) × ℚ)) (updated : Array ℚ) :
    (updatedEntries source updated).filter
      CodeDZeroSelectionV2.keepPositive =
    canonicalSource (retainedSource source updated) := by
  unfold updatedEntries retainedSource canonicalSource
  rw [selected_aux]
  unfold positiveIndices
  simpa using
    (mapped_aux source updated
      ((List.range updated.size).filter
        (fun i => decide (0 < updated[i]?.getD 0)))).symm

theorem updated_entries_valid {q : Nat}
    (source : Array ((Fin q → Nat) × ℚ)) (updated : Array ℚ) :
    ∀ e ∈ updatedEntries source updated, e.weight.Valid := by
  intro e he
  obtain ⟨i, _, hi⟩ := List.mem_filterMap.mp he
  unfold updatedAt at hi
  cases hs : source[i]? with
  | none => simp [hs] at hi
  | some entry =>
      simp [hs] at hi
      subst e
      exact canonicalEntry_valid _

theorem updated_entries_nonneg {q : Nat}
    (source : Array ((Fin q → Nat) × ℚ)) (updated : Array ℚ)
    (hupdated : updated.all (fun w => decide (0 ≤ w)) = true) :
    ∀ e ∈ updatedEntries source updated, 0 ≤ e.weight.value := by
  intro e he
  obtain ⟨i, hi, hie⟩ := List.mem_filterMap.mp he
  have hidx : i < updated.size := List.mem_range.mp hi
  have hw := (Array.all_eq_true.mp hupdated) i hidx
  unfold updatedAt at hie
  cases hs : source[i]? with
  | none => simp [hs] at hie
  | some entry =>
      simp [hs] at hie
      subst e
      simpa [canonicalEntry, rawOfRat_value, hidx] using hw

theorem compact_updated_bytes {q : Nat}
    (source : Array ((Fin q → Nat) × ℚ)) (updated : Array ℚ)
    (hupdated : updated.all (fun w => decide (0 ≤ w)) = true) :
    CodeDCompactJoinV2.output
      ((updatedEntries source updated).map encodeEntry) =
    encodedSource (retainedSource source updated) := by
  rw [CodeDCompactJoinV2.output]
  rw [CodeDZeroCompactSpecV2.output_exact_positive
    (updatedEntries source updated)
    (updated_entries_valid source updated)
    (updated_entries_nonneg source updated hupdated)]
  rw [selected_updated_exact]
  rfl

theorem physical_compact_updated {q : Nat}
    (source : Array ((Fin q → Nat) × ℚ)) (updated : Array ℚ)
    (hupdated : updated.all (fun w => decide (0 ≤ w)) = true) :
    CodeDCompactJoinV2.machine.OutputsWithin
      (encodeSource (updatedEntries source updated))
      (encodedSource (retainedSource source updated))
      (CodeDCompactJoinV2.clock
        ((updatedEntries source updated).map encodeEntry)) := by
  have h := CodeDCompactJoinV2.outputs
    ((updatedEntries source updated).map encodeEntry)
  rw [compact_updated_bytes source updated hupdated] at h
  simpa only [encodeSource] using h

theorem materialized_success_updated {q n : Nat}
    (φ : (Fin q → Nat) → Fin n → ℚ)
    (source out : Array ((Fin q → Nat) × ℚ))
    (h : compressSourceOnceMaterialized n φ source = some out) :
    ∃ updated : Array ℚ,
      updated.all (fun w => decide (0 ≤ w)) = true ∧
      out = retainedSource source updated := by
  unfold compressSourceOnceMaterialized at h
  dsimp only at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · split at h
        · split at h
          · cases h
            refine ⟨_, ?_, rfl⟩
            simp_all [Bool.and_eq_true, Array.all_eq_true]
          · cases h
        · cases h
      · cases h

theorem physical_materialized_success {q n : Nat}
    (φ : (Fin q → Nat) → Fin n → ℚ)
    (source out : Array ((Fin q → Nat) × ℚ))
    (h : compressSourceOnceMaterialized n φ source = some out) :
    ∃ updated : Array ℚ,
      CodeDCompactJoinV2.machine.OutputsWithin
        (encodeSource (updatedEntries source updated))
        (encodedSource out)
        (CodeDCompactJoinV2.clock
          ((updatedEntries source updated).map encodeEntry)) := by
  obtain ⟨updated, hnonneg, hout⟩ :=
    materialized_success_updated φ source out h
  exact ⟨updated, hout ▸ physical_compact_updated source updated hnonneg⟩

#print axioms selected_updated_exact
#print axioms compact_updated_bytes
#print axioms physical_compact_updated
#print axioms materialized_success_updated
#print axioms physical_materialized_success

end CurrentAdditive.CodeDCompactSequentialBridge
