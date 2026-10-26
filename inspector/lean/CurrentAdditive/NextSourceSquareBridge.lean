import CurrentAdditive.CanonicalAmbientSourceSquare

noncomputable section

namespace CurrentAdditive.FiniteFieldConstructor.CanonicalAmbient

open Turing EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineStackEmbedding
open CurrentAdditive.SmallBias
open CurrentAdditive.FieldSearchCompletion
open Paper2.YaoMachine Paper2.YaoLookup Paper2.YaoSourceCodec

theorem sourceSquareOutput_foreign {t : ℕ} (x : YaoSource t)
    (j : Cell t 16) (h : ¬ ∃ i : Fin 9, squareEmbed t 16 i = j) :
    sourceSquareOutput x j = sourceSelectorOutput x j := by
  rw [sourceSquareOutput,
    bank_outside (squareEmbed t 16) _ _ j h]
  have h0 : j ≠ .square 0 := by
    intro he; exact h ⟨0, by simpa [squareEmbed] using he.symm⟩
  simp [squareInputBank, h0]

theorem sourceSquareOutput_R2 {t : ℕ} (x : YaoSource t) :
    let d := publicFieldDegree (paddedEdgeBits x.2.1) t
    sourceSquareOutput x (.square 3) =
      List.replicate ((2^d)^2) true := by
  dsimp only
  let d := publicFieldDegree (paddedEdgeBits x.2.1) t
  simpa [sourceSquareOutput, d] using
    (bank_at (squareEmbed t 16)
      (squareInputBank t 16 d (sourceSelectorOutput x))
      (Function.update (Function.update
        (CanonicalFieldSquare.initial d) 2
        (List.replicate 4 true)) 3
        (List.replicate ((2^d)^2) true)) (3 : Fin 9))

theorem sourceSquareOutput_public {t : ℕ} (x : YaoSource t) :
    let d := publicFieldDegree (paddedEdgeBits x.2.1) t
    let n := paddedEdgeCount x.2.1*(arity t+1)
    sourceSquareOutput x (.degree 3) = List.replicate d true ∧
    sourceSquareOutput x (.width 3) = List.replicate n true ∧
    sourceSquareOutput x (.source (sN 6)) =
      List.replicate (paddedEdgeCount x.2.1) true ∧
    sourceSquareOutput x (.source (sN 9)) =
      List.replicate (arity t) true ∧
    sourceSquareOutput x (.selector 1) =
      List.replicate
        ((paddedEdgeCount x.2.1)^(2^(t-1))) true := by
  dsimp only
  obtain ⟨hd, hH, hK⟩ := sourceDegreeWidthOutput_public x
  have hn := sourceDegreeWidthOutput_width x
  have hcap := sourceSelectorOutput_cap x
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [sourceSquareOutput_foreign x (.degree 3)
      (by intro ⟨i, hi⟩; cases hi),
      sourceSelectorOutput_foreign x (.degree 3)
      (by intro ⟨i, hi⟩; cases hi)]
    exact hd
  · rw [sourceSquareOutput_foreign x (.width 3)
      (by intro ⟨i, hi⟩; cases hi),
      sourceSelectorOutput_foreign x (.width 3)
      (by intro ⟨i, hi⟩; cases hi)]
    exact hn
  · rw [sourceSquareOutput_foreign x (.source (sN 6))
      (by intro ⟨i, hi⟩; cases hi),
      sourceSelectorOutput_foreign x (.source (sN 6))
      (by intro ⟨i, hi⟩; cases hi)]
    exact hH
  · rw [sourceSquareOutput_foreign x (.source (sN 9))
      (by intro ⟨i, hi⟩; cases hi),
      sourceSelectorOutput_foreign x (.source (sN 9))
      (by intro ⟨i, hi⟩; cases hi)]
    exact hK
  · rw [sourceSquareOutput_foreign x (.selector 1)
      (by intro ⟨i, hi⟩; cases hi)]
    exact hcap

theorem sourceSquareOutput_fieldBlank {t : ℕ} (x : YaoSource t) :
    (∀ i : FieldUnaryUnifiedMachine.Stack,
      sourceSquareOutput x (fieldCombinedEmbed t 16 i) = []) ∧
    sourceSquareOutput x (.copyScratch 0) = [] := by
  have hforeign (j : Cell t 16)
      (hsource : ¬ ∃ i : WStack t 0, sourceEmbed t 16 i = j)
      (hdegree : ¬ ∃ i : Fin 16, degreeEmbed t 16 i = j)
      (hwidth : ¬ ∃ i : Fin 8, widthEmbed t 16 i = j)
      (hselector : ¬ ∃ i : Fin 12, selectorEmbed t 16 i = j)
      (hsquare : ¬ ∃ i : Fin 9, squareEmbed t 16 i = j) :
      sourceSquareOutput x j = [] := by
    rw [sourceSquareOutput_foreign x j hsquare,
      sourceSelectorOutput_foreign x j hselector,
      sourceDegreeWidthOutput_foreign x j hwidth,
      sourceDegreeOutput_foreign x j hdegree]
    exact bank_outside (sourceEmbed t 16) (blank t 16)
      (CurrentAdditive.FiniteFieldConstructor.CanonicalSourcePrelude.sourceReady x)
      j hsource
  constructor
  · intro i
    rcases i with i | i
    · apply hforeign (.fieldInit i)
      <;> intro ⟨j, hj⟩ <;> cases hj
    · apply hforeign (.field i)
      <;> intro ⟨j, hj⟩ <;> cases hj
  · apply hforeign (.copyScratch 0)
    <;> intro ⟨j, hj⟩ <;> cases hj

theorem sourceSquareOutput_source {t : ℕ} (x : YaoSource t)
    (i : Fin 40) :
    sourceSquareOutput x (.source (sN i)) =
      CurrentAdditive.FiniteFieldConstructor.CanonicalSourcePrelude.sourceReady x
        (sN i) := by
  rw [sourceSquareOutput_foreign x (.source (sN i))
      (by intro ⟨j, hj⟩; cases hj),
    sourceSelectorOutput_foreign x (.source (sN i))
      (by intro ⟨j, hj⟩; cases hj),
    sourceDegreeWidthOutput_foreign x (.source (sN i))
      (by intro ⟨j, hj⟩; cases hj)]
  exact sourceDegreeOutput_source x i

theorem sourceSquareOutput_unallocated {t : ℕ} (x : YaoSource t)
    (j : Cell t 16)
    (hsource : ¬ ∃ i : WStack t 0, sourceEmbed t 16 i = j)
    (hdegree : ¬ ∃ i : Fin 16, degreeEmbed t 16 i = j)
    (hwidth : ¬ ∃ i : Fin 8, widthEmbed t 16 i = j)
    (hselector : ¬ ∃ i : Fin 12, selectorEmbed t 16 i = j)
    (hsquare : ¬ ∃ i : Fin 9, squareEmbed t 16 i = j) :
    sourceSquareOutput x j = [] := by
  rw [sourceSquareOutput_foreign x j hsquare,
    sourceSelectorOutput_foreign x j hselector,
    sourceDegreeWidthOutput_foreign x j hwidth,
    sourceDegreeOutput_foreign x j hdegree]
  exact bank_outside (sourceEmbed t 16) (blank t 16)
    (CurrentAdditive.FiniteFieldConstructor.CanonicalSourcePrelude.sourceReady x)
    j hsource

theorem sourceSquareOutput_later_blank {t : ℕ} (x : YaoSource t) :
    (∀ i : Fin 11, sourceSquareOutput x (.dimensions i) = []) ∧
    (∀ i : Fin 3, sourceSquareOutput x (.threshold i) = []) ∧
    (∀ i : MatrixTableWriter.Stack 60,
      sourceSquareOutput x (.writer i) = []) ∧
    (∀ i : Paper2.HeaderA.HB,
      sourceSquareOutput x (.header i) = []) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i
    apply sourceSquareOutput_unallocated x (.dimensions i)
    <;> intro ⟨j, hj⟩ <;> cases hj
  · intro i
    apply sourceSquareOutput_unallocated x (.threshold i)
    <;> intro ⟨j, hj⟩ <;> cases hj
  · intro i
    apply sourceSquareOutput_unallocated x (.writer i)
    <;> intro ⟨j, hj⟩ <;> cases hj
  · intro i
    apply sourceSquareOutput_unallocated x (.header i)
    <;> intro ⟨j, hj⟩ <;> cases hj

#print axioms sourceSquareOutput_foreign
#print axioms sourceSquareOutput_R2
#print axioms sourceSquareOutput_fieldBlank
#print axioms sourceSquareOutput_source
#print axioms sourceSquareOutput_later_blank

end CurrentAdditive.FiniteFieldConstructor.CanonicalAmbient
