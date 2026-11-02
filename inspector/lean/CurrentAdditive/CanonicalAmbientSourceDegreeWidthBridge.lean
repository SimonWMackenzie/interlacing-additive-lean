import CurrentAdditive.CanonicalAmbientWriterHeaderFull

/-! The width multiplication preserves every previously prepared source and
degree cell and leaves the next ambient summands blank. -/

noncomputable section

namespace CurrentAdditive.FiniteFieldConstructor.CanonicalAmbient

open Turing EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineStackEmbedding
open Paper2.YaoMachine Paper2.YaoLookup Paper2.YaoSourceCodec

theorem sourceDegreeWidthOutput_foreign {t : ℕ} (x : YaoSource t)
    (j : Cell t 16) (hwidth : ¬ ∃ i : Fin 8, widthEmbed t 16 i = j) :
    sourceDegreeWidthOutput x j = sourceDegreeOutput x j := by
  rw [sourceDegreeWidthOutput,
    bank_outside (widthEmbed t 16) _ _ j hwidth]
  have h0 : j ≠ .width 0 := by
    intro he; exact hwidth ⟨0, by simpa [widthEmbed] using he.symm⟩
  have h1 : j ≠ .width 1 := by
    intro he; exact hwidth ⟨1, by simpa [widthEmbed] using he.symm⟩
  simp [widthInputBank, h0, h1]

theorem sourceDegreeWidthOutput_width {t : ℕ} (x : YaoSource t) :
    sourceDegreeWidthOutput x (.width 3) =
      List.replicate
        (paddedEdgeCount x.2.1 * (arity t + 1)) true := by
  simpa [sourceDegreeWidthOutput, MatrixTableWriter.Data.contents] using
    (bank_at (widthEmbed t 16)
      (widthInputBank t 16 (paddedEdgeCount x.2.1) (arity t)
        (sourceDegreeOutput x))
      (Function.update (Function.update
        (CanonicalWidthMultiply.initial (paddedEdgeCount x.2.1) (arity t)) 2
        (List.replicate (arity t+1) true)) 3
        (List.replicate (paddedEdgeCount x.2.1*(arity t+1)) true))
      (3 : Fin 8))

theorem sourceDegreeWidthOutput_public {t : ℕ} (x : YaoSource t) :
    sourceDegreeWidthOutput x (.degree 3) =
      List.replicate
        (CurrentAdditive.SmallBias.publicFieldDegree
          (paddedEdgeBits x.2.1) t) true ∧
    sourceDegreeWidthOutput x (.source (sN 6)) =
      List.replicate (paddedEdgeCount x.2.1) true ∧
    sourceDegreeWidthOutput x (.source (sN 9)) =
      List.replicate (arity t) true := by
  obtain ⟨_, hH, hK⟩ := sourceDegreeOutput_public x
  refine ⟨?_, ?_, ?_⟩
  · rw [sourceDegreeWidthOutput_foreign x (.degree 3)
      (by intro ⟨i, hi⟩; cases hi)]
    exact sourceDegreeOutput_degree x
  · rw [sourceDegreeWidthOutput_foreign x (.source (sN 6))
      (by intro ⟨i, hi⟩; cases hi)]
    exact hH
  · rw [sourceDegreeWidthOutput_foreign x (.source (sN 9))
      (by intro ⟨i, hi⟩; cases hi)]
    exact hK

theorem sourceDegreeWidthOutput_next_blank {t : ℕ} (x : YaoSource t) :
    (∀ i : Fin 12, sourceDegreeWidthOutput x (.selector i) = []) ∧
    (∀ i : Fin 9, sourceDegreeWidthOutput x (.square i) = []) ∧
    (∀ i : Fin 11, sourceDegreeWidthOutput x (.dimensions i) = []) ∧
    (∀ i : Fin 3, sourceDegreeWidthOutput x (.threshold i) = []) ∧
    sourceDegreeWidthOutput x (.copyScratch 0) = [] := by
  obtain ⟨_, hs, hq, hd, ht, hc⟩ :=
    sourceDegreeOutput_foreign_blank x
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro i
    rw [sourceDegreeWidthOutput_foreign x (.selector i)
      (by intro ⟨j, hj⟩; cases hj)]
    exact hs i
  · intro i
    rw [sourceDegreeWidthOutput_foreign x (.square i)
      (by intro ⟨j, hj⟩; cases hj)]
    exact hq i
  · intro i
    rw [sourceDegreeWidthOutput_foreign x (.dimensions i)
      (by intro ⟨j, hj⟩; cases hj)]
    exact hd i
  · intro i
    rw [sourceDegreeWidthOutput_foreign x (.threshold i)
      (by intro ⟨j, hj⟩; cases hj)]
    exact ht i
  · rw [sourceDegreeWidthOutput_foreign x (.copyScratch 0)
      (by intro ⟨j, hj⟩; cases hj)]
    exact hc

#print axioms sourceDegreeWidthOutput_foreign
#print axioms sourceDegreeWidthOutput_width
#print axioms sourceDegreeWidthOutput_next_blank

end CurrentAdditive.FiniteFieldConstructor.CanonicalAmbient
