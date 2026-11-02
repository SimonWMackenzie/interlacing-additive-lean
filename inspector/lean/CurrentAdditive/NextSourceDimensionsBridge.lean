import CurrentAdditive.NextSourceDimensions

noncomputable section

namespace CurrentAdditive.FiniteFieldConstructor.CanonicalAmbient

open Turing EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineStackEmbedding
open CurrentAdditive.SmallBias
open CurrentAdditive.FiniteFieldConstructor.CanonicalTable
open Paper2.YaoMachine Paper2.YaoLookup Paper2.YaoSourceCodec

theorem sourceDimensionsOutput_foreign {t : ℕ} (x : YaoSource t)
    (u : ℕ) (j : Cell t 16)
    (h : ¬ ∃ i : Fin 11, dimensionsEmbed t 16 i = j) :
    sourceDimensionsOutput x u j = sourceFieldOutput x u j := by
  rw [sourceDimensionsOutput,
    bank_outside (dimensionsEmbed t 16) _ _ j h]
  have h4 : j ≠ .dimensions 4 := by
    intro he; exact h ⟨4, by simpa [dimensionsEmbed] using he.symm⟩
  have hjobs : ∀ job ∈ dimensionJobs t, j ∉ job.2 := by
    intro job hj
    simp [dimensionJobs] at hj
    rcases hj with (rfl|rfl|rfl|rfl) <;>
      simp only [List.mem_singleton, not_and, not_false_eq_true] <;>
      intro he <;> exact h ⟨_, by simpa [dimensionsEmbed] using he.symm⟩
  simp [dimensionPrepared, h4,
    CopyFill.fill_off (dimensionJobs t) (sourceFieldOutput x u) j hjobs]

theorem sourceDimensionsOutput_counts {t : ℕ} (x : YaoSource t)
    (u : ℕ) :
    let b := paddedEdgeBits x.2.1
    let d := publicFieldDegree b t
    sourceDimensionsOutput x u (.dimensions 5) =
      List.replicate (rowCount x.1 b t) true ∧
    sourceDimensionsOutput x u (.dimensions 7) =
      List.replicate (columnCount b t d) true := by
  dsimp only
  let b := paddedEdgeBits x.2.1
  let H := paddedEdgeCount x.2.1
  let d := publicFieldDegree b t
  let cap := H^(2^(t-1))
  let R2 := (2^d)^2
  constructor
  · have h := bank_at (dimensionsEmbed t 16)
      (dimensionPrepared t x.1 cap H R2 (sourceFieldOutput x u))
      (Function.update (Function.update (Function.update
        (CanonicalDimensionsMultiply.initial x.1 cap H R2 (2^(t-1))) 5
        (List.replicate (x.1*cap) true)) 6
        (List.replicate ((2^(t-1))*H) true)) 7
        (List.replicate ((2^(t-1))*H*R2) true)) (5 : Fin 11)
    simpa [sourceDimensionsOutput, rowCount,
      paddedEdgeCount, b, H, d, cap, R2] using h
  · have h := bank_at (dimensionsEmbed t 16)
      (dimensionPrepared t x.1 cap H R2 (sourceFieldOutput x u))
      (Function.update (Function.update (Function.update
        (CanonicalDimensionsMultiply.initial x.1 cap H R2 (2^(t-1))) 5
        (List.replicate (x.1*cap) true)) 6
        (List.replicate ((2^(t-1))*H) true)) 7
        (List.replicate ((2^(t-1))*H*R2) true)) (7 : Fin 11)
    simpa [sourceDimensionsOutput, columnCount,
      paddedEdgeCount, b, H, d, cap, R2] using h

theorem sourceDimensionsOutput_threshold_input {t : ℕ}
    (x : YaoSource t) (u : ℕ) :
    sourceDimensionsOutput x u (.source (sN 5)) =
      List.replicate (paddedEdgeBits x.2.1) true ∧
    (∀ i : Fin 3, sourceDimensionsOutput x u (.threshold i) = []) ∧
    sourceDimensionsOutput x u (.copyScratch 0) = [] := by
  obtain ⟨_, _, _, hb, _, _, _, _, _⟩ := sourceFieldOutput_public x u
  obtain ⟨_, ht, _, _, hc⟩ := sourceFieldOutput_later_blank x u
  refine ⟨?_, ?_, ?_⟩
  · rw [sourceDimensionsOutput_foreign x u (.source (sN 5))
      (by intro ⟨i, hi⟩; cases hi)]
    exact hb
  · intro i
    rw [sourceDimensionsOutput_foreign x u (.threshold i)
      (by intro ⟨j, hj⟩; cases hj)]
    exact ht i
  · rw [sourceDimensionsOutput_foreign x u (.copyScratch 0)
      (by intro ⟨j, hj⟩; cases hj)]
    exact hc

#print axioms sourceDimensionsOutput_foreign
#print axioms sourceDimensionsOutput_counts
#print axioms sourceDimensionsOutput_threshold_input

end CurrentAdditive.FiniteFieldConstructor.CanonicalAmbient
