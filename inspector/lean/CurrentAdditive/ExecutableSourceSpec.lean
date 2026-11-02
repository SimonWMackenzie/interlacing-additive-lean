import CurrentAdditive.ExecutableSources
import CurrentAdditive.SequentialResourceBridgeFixed

/-! Full finite source contract for the literal sequential program on its
explicit positive rational alphabet table. Physical time is separate. -/

namespace CurrentAdditive.ExecutableCodeSource

open Paper2 SequentialCode SequentialSourceCode SequentialSourceResource
  SequentialResourceBridgeFixed SequentialAppendMoments SequentialFiniteLaw
  SequentialDimensionPolynomialProduction

theorem sourceTable_full_spec {Y : Type} [Fintype Y] [DecidableEq Y]
    (D q : Nat) (μ : PositiveRationalLaw Y)
    (table : AlphabetTable Y μ) :
    ∃ (out : Array ((Fin q → Y) × ℚ)) (count : Nat)
      (hpositive : SourcePositive out) (hmass : sourceMass out = 1),
      sequentialMaterializedCount D table.entries q = some (out, count) ∧
      sequentialMaterialized D table.entries q = some out ∧
      IsDWise D (indexedLaw out hpositive hmass).toFiniteLaw
        (fun i => out[i].1) μ.toFiniteLaw ∧
      out.size ≤ (∑ k ∈ Finset.range (min D q + 1),
        q.choose k * table.entries.size ^ k) ∧
      (∑ k ∈ Finset.range (min D q + 1),
        q.choose k * table.entries.size ^ k) ≤
          (1 + q * table.entries.size) ^ D ∧
      count ≤ q * table.entries.size *
        (∑ k ∈ Finset.range (min D q + 1),
          q.choose k * table.entries.size ^ k) := by
  obtain ⟨out, count, hcount, hpositive, hsize, hcalls⟩ :=
    sequentialMaterializedCount_total D table.entries table.positive q
  have hsource : sequentialMaterialized D table.entries q = some out := by
    have heq := sequentialMaterializedCount_iff D table.entries q
    simpa [hcount] using heq.symm
  have hmass : sourceMass out = 1 :=
    sequentialMaterialized_mass D table.entries table.normalized q out hsource
  refine ⟨out, count, hpositive, hmass, hcount, hsource, ?_, hsize, ?_, hcalls⟩
  · exact sequential_indexed_dwise D table.entries table.normalized
      table.covers μ table.pointMass q out hsource hpositive hmass
  · exact momentCount_le_polynomial q D table.entries.size

#print axioms sourceTable_full_spec

end CurrentAdditive.ExecutableCodeSource
