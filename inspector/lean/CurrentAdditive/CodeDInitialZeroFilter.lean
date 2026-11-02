import CurrentAdditive.CodeDCompactSequentialBridge

/-!
The actual compact-list machine discards zero weights before any dependence
test.  Its output is exactly the indexed positive-law deletion expression;
duplicate decoded words are preserved as separate list positions.
-/

namespace CurrentAdditive.CodeDInitialZeroFilter

open CodeDCanonicalSourceV2 CodeDCompactSequentialBridge CodeDSourceCodecV2
open SequentialCode SequentialSourceCode

theorem updatedEntries_self {q : Nat}
    (source : Array ((Fin q → Nat) × ℚ)) :
    updatedEntries source (source.map Prod.snd) = canonicalSource source := by
  let g : Nat → Entry := fun i => canonicalEntry (source[i]?.getD default)
  have hm : (List.range source.size).filterMap
      (updatedAt source (source.map Prod.snd)) =
      (List.range source.size).map g := by
    apply List.filterMap_eq_map_iff_forall_eq_some.mpr
    intro i hi
    have hb : i < source.size := List.mem_range.mp hi
    simp [updatedAt, g, hb]
  unfold updatedEntries
  simp only [Array.size_map]
  rw [hm]
  apply List.ext_getElem
  · simp [canonicalSource]
  · intro i hi hj
    have hb : i < source.size := by simpa using hi
    simp [canonicalSource, g, hb]

theorem output_exact {q : Nat}
    (source : Array ((Fin q → Nat) × ℚ))
    (hnonneg : source.all (fun e => decide (0 ≤ e.2)) = true) :
    CodeDCompactJoinV2.output ((canonicalSource source).map encodeEntry) =
      encodedSource
        (SequentialZeroDeletion.retainedSource source (source.map Prod.snd)) := by
  have hw : (source.map Prod.snd).all (fun w => decide (0 ≤ w)) = true := by
    simpa [Array.all_map] using hnonneg
  have h := compact_updated_bytes source (source.map Prod.snd) hw
  rw [updatedEntries_self] at h
  exact h

/-- A single fixed physical machine performs the initial zero deletion.
Every input bit, both compaction passes, and the fresh list header are
included in the displayed concrete clock. -/
theorem outputs {q : Nat}
    (source : Array ((Fin q → Nat) × ℚ))
    (hnonneg : source.all (fun e => decide (0 ≤ e.2)) = true) :
    CodeDCompactJoinV2.machine.OutputsWithin (encodedSource source)
      (encodedSource
        (SequentialZeroDeletion.retainedSource source (source.map Prod.snd)))
      (CodeDCompactJoinV2.clock ((canonicalSource source).map encodeEntry)) := by
  have h := CodeDCompactJoinV2.outputs ((canonicalSource source).map encodeEntry)
  rw [output_exact source hnonneg] at h
  exact h

#print axioms updatedEntries_self
#print axioms output_exact
#print axioms outputs

end CurrentAdditive.CodeDInitialZeroFilter
