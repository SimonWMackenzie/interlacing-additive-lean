import CurrentAdditive.NextDimensionsThresholdLocal

noncomputable section

namespace CurrentAdditive.FiniteFieldConstructor.CanonicalAmbient

open Turing EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineStackEmbedding
open CurrentAdditive.FiniteFieldConstructor.CanonicalTable
open Paper2.YaoMachine Paper2.YaoLookup Paper2.YaoSourceCodec

theorem sourceThresholdOutput_foreign {t : ℕ} (x : YaoSource t)
    (u : ℕ) (j : Cell t 16)
    (h : ¬ ∃ i : Fin 3, thresholdEmbed t 16 i = j) :
    sourceThresholdOutput x u j = sourceDimensionsOutput x u j := by
  rw [sourceThresholdOutput,
    bank_outside (thresholdEmbed t 16) _ _ j h]
  have h0 : j ≠ .threshold 0 := by
    intro he; exact h ⟨0, by simpa [thresholdEmbed] using he.symm⟩
  simp [thresholdInputBank, h0]

theorem sourceThresholdOutput_thr {t : ℕ} (x : YaoSource t)
    (u : ℕ) :
    sourceThresholdOutput x u (.threshold 1) =
      List.replicate (2*paddedEdgeBits x.2.1+4*t+2) true := by
  let b := paddedEdgeBits x.2.1
  simpa [sourceThresholdOutput, b] using
    (bank_at (thresholdEmbed t 16)
      (thresholdInputBank t 16 b (sourceDimensionsOutput x u))
      (Function.update (CanonicalThreshold.initial b) 1
        (List.replicate (2*b+4*t+2) true)) (1 : Fin 3))

theorem sourceThresholdOutput_writer_inputs {t : ℕ} (x : YaoSource t)
    (u : ℕ) :
    let b := paddedEdgeBits x.2.1
    let d := CurrentAdditive.SmallBias.publicFieldDegree b t
    let H := paddedEdgeCount x.2.1
    let n := H*(arity t+1)
    sourceThresholdOutput x u (.selector 1) =
      List.replicate (H^(2^(t-1))) true ∧
    sourceThresholdOutput x u (.square 3) =
      List.replicate ((2^d)^2) true ∧
    sourceThresholdOutput x u (.source (sN 6)) =
      List.replicate H true ∧
    sourceThresholdOutput x u (.source (sN 1)) =
      Paper2.UnaryFieldListParserScratch.tokens
        (List.ofFn (flatten x.2.2)) ∧
    sourceThresholdOutput x u (.source (sN 9)) =
      List.replicate (arity t) true ∧
    sourceThresholdOutput x u (.width 3) =
      List.replicate n true ∧
    sourceThresholdOutput x u (.dimensions 5) =
      List.replicate (rowCount x.1 b t) true ∧
    sourceThresholdOutput x u (.dimensions 7) =
      List.replicate (columnCount b t d) true := by
  dsimp only
  obtain ⟨_, hn, _, _, hH, hK, hbody, hcap, hR2⟩ :=
    sourceFieldOutput_public x u
  obtain ⟨hrows, hcols⟩ := sourceDimensionsOutput_counts x u
  have hthrough (j : Cell t 16)
      (hth : ¬ ∃ i : Fin 3, thresholdEmbed t 16 i = j)
      (hdim : ¬ ∃ i : Fin 11, dimensionsEmbed t 16 i = j) :
      sourceThresholdOutput x u j = sourceFieldOutput x u j := by
    rw [sourceThresholdOutput_foreign x u j hth,
      sourceDimensionsOutput_foreign x u j hdim]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hthrough (.selector 1)
      (by intro ⟨i, hi⟩; cases hi)
      (by intro ⟨i, hi⟩; cases hi)]
    exact hcap
  · rw [hthrough (.square 3)
      (by intro ⟨i, hi⟩; cases hi)
      (by intro ⟨i, hi⟩; cases hi)]
    exact hR2
  · rw [hthrough (.source (sN 6))
      (by intro ⟨i, hi⟩; cases hi)
      (by intro ⟨i, hi⟩; cases hi)]
    exact hH
  · rw [hthrough (.source (sN 1))
      (by intro ⟨i, hi⟩; cases hi)
      (by intro ⟨i, hi⟩; cases hi)]
    exact hbody
  · rw [hthrough (.source (sN 9))
      (by intro ⟨i, hi⟩; cases hi)
      (by intro ⟨i, hi⟩; cases hi)]
    exact hK
  · rw [hthrough (.width 3)
      (by intro ⟨i, hi⟩; cases hi)
      (by intro ⟨i, hi⟩; cases hi)]
    exact hn
  · rw [sourceThresholdOutput_foreign x u (.dimensions 5)
      (by intro ⟨i, hi⟩; cases hi)]
    exact hrows
  · rw [sourceThresholdOutput_foreign x u (.dimensions 7)
      (by intro ⟨i, hi⟩; cases hi)]
    exact hcols

theorem sourceThresholdOutput_writer_blank {t : ℕ}
    (x : YaoSource t) (u : ℕ) :
    (∀ i : MatrixTableWriter.Stack 60,
      sourceThresholdOutput x u (.writer i) = []) ∧
    (∀ i : Paper2.HeaderA.HB,
      sourceThresholdOutput x u (.header i) = []) ∧
    sourceThresholdOutput x u (.copyScratch 0) = [] := by
  obtain ⟨_, _, hw, hh, hc⟩ := sourceFieldOutput_later_blank x u
  have hthrough (j : Cell t 16)
      (hth : ¬ ∃ i : Fin 3, thresholdEmbed t 16 i = j)
      (hdim : ¬ ∃ i : Fin 11, dimensionsEmbed t 16 i = j) :
      sourceThresholdOutput x u j = sourceFieldOutput x u j := by
    rw [sourceThresholdOutput_foreign x u j hth,
      sourceDimensionsOutput_foreign x u j hdim]
  refine ⟨?_, ?_, ?_⟩
  · intro i
    rw [hthrough (.writer i)
      (by intro ⟨j, hj⟩; cases hj)
      (by intro ⟨j, hj⟩; cases hj)]
    exact hw i
  · intro i
    rw [hthrough (.header i)
      (by intro ⟨j, hj⟩; cases hj)
      (by intro ⟨j, hj⟩; cases hj)]
    exact hh i
  · rw [hthrough (.copyScratch 0)
      (by intro ⟨j, hj⟩; cases hj)
      (by intro ⟨j, hj⟩; cases hj)]
    exact hc

#print axioms sourceThresholdOutput_foreign
#print axioms sourceThresholdOutput_thr
#print axioms sourceThresholdOutput_writer_inputs
#print axioms sourceThresholdOutput_writer_blank

end CurrentAdditive.FiniteFieldConstructor.CanonicalAmbient
