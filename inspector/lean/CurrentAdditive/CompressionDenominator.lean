import CurrentAdditive.RetainedDenominator

set_option maxHeartbeats 1000000

namespace CurrentAdditive.RationalCandidateCompletion

open CurrentAdditive.SequentialCode
open CurrentAdditive.SequentialArrayBridge
open CurrentAdditive.SequentialSourceCode
open CurrentAdditive.SequentialZeroDeletion
open CurrentAdditive.SequentialCompressionTotality
open CurrentAdditive.MaterializedGauss
open CurrentAdditive.RationalBitBounds

/-- A successful call of the actual source compression routine preserves a
common denominator through its physical zero deletion, with the same
manuscript-scale one-step increment. -/
theorem compressSourceOnceMaterialized_denominator {α : Type*}
    (n : Nat) (φ : α → Fin n → ℚ)
    (source out : Array (α × ℚ))
    (hn : 0 < n)
    (hφ : ∀ x j, φ x j = 0 ∨ φ x j = 1)
    (h : compressSourceOnceMaterialized n φ source = some out)
    (enc : CommonDenominator
      (fun i : Fin (source.map Prod.snd).size =>
        (source.map Prod.snd)[i])) :
    ∃ next : CommonDenominator
        (fun j : Fin out.size => out[j].2),
      next.denominator ≤ enc.denominator *
        2 ^ (4 * n * Nat.size (n + 1)) := by
  let matrix := featureRows n φ source
  let weights := source.map Prod.snd
  have h01 : ∀ i : Fin matrix.size, ∀ j : Fin (columnCount matrix),
      matrixOfArray matrix i j = 0 ∨ matrixOfArray matrix i j = 1 := by
    simpa [matrix] using featureRows_zero_one n φ source hφ
  have hweights : weights.size = columnCount matrix := by
    simpa [matrix, weights] using
      (featureRows_columnCount n φ source hn).symm
  unfold compressSourceOnceMaterialized at h
  dsimp only at h
  cases hcert : certifiedMaterializedDependence matrix with
  | none => simp [matrix, hcert] at h
  | some cert =>
      cases hstep : eliminateWeights weights cert.val with
      | none => simp [matrix, weights, hcert, hstep] at h
      | some updated =>
          obtain ⟨encUpdated, hupdatedSize, hbound⟩ :=
            certified_materialized_update_bound matrix weights updated
              h01 hweights cert hcert hstep enc
          have hretained : out = retainedSource source updated := by
            simp only [matrix, weights, hcert, hstep] at h
            split_ifs at h <;> try cases h
            · rfl
          subst out
          let encUpdated' : CommonDenominator
              (fun i : Fin updated.size => updated[i]) :=
            { denominator := encUpdated.denominator
              positive := encUpdated.positive
              numerator := fun i =>
                encUpdated.numerator ⟨i.val, by omega⟩
              represents := by
                intro i
                have hp := encUpdated.represents ⟨i.val, by omega⟩
                simpa [i.isLt] using hp }
          let encRetained :=
            retainedSource_commonDenominator source updated
              encUpdated'
          refine ⟨encRetained, ?_⟩
          have hden : encUpdated'.denominator = encUpdated.denominator := rfl
          change encUpdated'.denominator ≤ enc.denominator *
            2 ^ (4 * n * Nat.size (n + 1))
          rw [hden]
          simpa [matrix, featureRows] using hbound

#print axioms compressSourceOnceMaterialized_denominator

end CurrentAdditive.RationalCandidateCompletion
