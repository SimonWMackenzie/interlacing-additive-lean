import CurrentAdditive.NextSourceField

noncomputable section

namespace CurrentAdditive.FiniteFieldConstructor.CanonicalAmbient

open Turing EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineStackEmbedding
open CurrentAdditive.SmallBias
open CurrentAdditive.FiniteFieldConstructor.CanonicalSourcePrelude
open Paper2.YaoMachine Paper2.YaoLookup Paper2.YaoSourceCodec

theorem sourceFieldOutput_foreign {t : ℕ} (x : YaoSource t) (u : ℕ)
    (j : Cell t 16)
    (h : ¬ ∃ i : CurrentAdditive.FieldSearchCompletion.FieldUnaryUnifiedMachine.Stack,
      fieldCombinedEmbed t 16 i = j) :
    sourceFieldOutput x u j = sourceSquareOutput x j := by
  rw [sourceFieldOutput,
    bank_outside (fieldCombinedEmbed t 16) _ _ j h]
  have h0 : j ≠ .fieldInit 0 := by
    intro he; exact h ⟨.inl 0, by simpa [fieldCombinedEmbed] using he.symm⟩
  have h1 : j ≠ .fieldInit 1 := by
    intro he; exact h ⟨.inl 1, by simpa [fieldCombinedEmbed] using he.symm⟩
  simp [fieldInputBank, h0, h1]

theorem sourceFieldOutput_public {t : ℕ} (x : YaoSource t) (u : ℕ) :
    let d := publicFieldDegree (paddedEdgeBits x.2.1) t
    let H := paddedEdgeCount x.2.1
    let n := H*(arity t+1)
    sourceFieldOutput x u (.degree 3) = List.replicate d true ∧
    sourceFieldOutput x u (.width 3) = List.replicate n true ∧
    sourceFieldOutput x u (.source (sN 3)) =
      List.replicate x.1 true ∧
    sourceFieldOutput x u (.source (sN 5)) =
      List.replicate (paddedEdgeBits x.2.1) true ∧
    sourceFieldOutput x u (.source (sN 6)) =
      List.replicate H true ∧
    sourceFieldOutput x u (.source (sN 9)) =
      List.replicate (arity t) true ∧
    sourceFieldOutput x u (.source (sN 1)) =
      Paper2.UnaryFieldListParserScratch.tokens
        (List.ofFn (flatten x.2.2)) ∧
    sourceFieldOutput x u (.selector 1) =
      List.replicate (H^(2^(t-1))) true ∧
    sourceFieldOutput x u (.square 3) =
      List.replicate ((2^d)^2) true := by
  dsimp only
  obtain ⟨hd, hn, hH, hK, hcap⟩ := sourceSquareOutput_public x
  obtain ⟨hbody, hv, _, hb, _, _⟩ := sourceReady_public_cells x
  have hR2 := sourceSquareOutput_R2 x
  have hforeign (j : Cell t 16)
      (h : ¬ ∃ i : CurrentAdditive.FieldSearchCompletion.FieldUnaryUnifiedMachine.Stack,
        fieldCombinedEmbed t 16 i = j) :=
    sourceFieldOutput_foreign x u j h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hforeign (.degree 3) (by intro ⟨i, hi⟩; cases i <;> cases hi)]
    exact hd
  · rw [hforeign (.width 3) (by intro ⟨i, hi⟩; cases i <;> cases hi)]
    exact hn
  · rw [hforeign (.source (sN 3))
      (by intro ⟨i, hi⟩; cases i <;> cases hi),
      sourceSquareOutput_source x 3]
    exact hv
  · rw [hforeign (.source (sN 5))
      (by intro ⟨i, hi⟩; cases i <;> cases hi),
      sourceSquareOutput_source x 5]
    exact hb
  · rw [hforeign (.source (sN 6))
      (by intro ⟨i, hi⟩; cases i <;> cases hi)]
    exact hH
  · rw [hforeign (.source (sN 9))
      (by intro ⟨i, hi⟩; cases i <;> cases hi)]
    exact hK
  · rw [hforeign (.source (sN 1))
      (by intro ⟨i, hi⟩; cases i <;> cases hi),
      sourceSquareOutput_source x 1]
    exact hbody
  · rw [hforeign (.selector 1)
      (by intro ⟨i, hi⟩; cases i <;> cases hi)]
    exact hcap
  · rw [hforeign (.square 3)
      (by intro ⟨i, hi⟩; cases i <;> cases hi)]
    exact hR2

theorem sourceFieldOutput_later_blank {t : ℕ} (x : YaoSource t)
    (u : ℕ) :
    (∀ i : Fin 11, sourceFieldOutput x u (.dimensions i) = []) ∧
    (∀ i : Fin 3, sourceFieldOutput x u (.threshold i) = []) ∧
    (∀ i : MatrixTableWriter.Stack 60,
      sourceFieldOutput x u (.writer i) = []) ∧
    (∀ i : Paper2.HeaderA.HB,
      sourceFieldOutput x u (.header i) = []) ∧
    sourceFieldOutput x u (.copyScratch 0) = [] := by
  obtain ⟨hd, ht, hw, hh⟩ := sourceSquareOutput_later_blank x
  have hc := (sourceSquareOutput_fieldBlank x).2
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro i
    rw [sourceFieldOutput_foreign x u (.dimensions i)
      (by intro ⟨j, hj⟩; cases j <;> cases hj)]
    exact hd i
  · intro i
    rw [sourceFieldOutput_foreign x u (.threshold i)
      (by intro ⟨j, hj⟩; cases j <;> cases hj)]
    exact ht i
  · intro i
    rw [sourceFieldOutput_foreign x u (.writer i)
      (by intro ⟨j, hj⟩; cases j <;> cases hj)]
    exact hw i
  · intro i
    rw [sourceFieldOutput_foreign x u (.header i)
      (by intro ⟨j, hj⟩; cases j <;> cases hj)]
    exact hh i
  · rw [sourceFieldOutput_foreign x u (.copyScratch 0)
      (by intro ⟨j, hj⟩; cases j <;> cases hj)]
    exact hc

#print axioms sourceFieldOutput_foreign
#print axioms sourceFieldOutput_public
#print axioms sourceFieldOutput_later_blank

end CurrentAdditive.FiniteFieldConstructor.CanonicalAmbient
