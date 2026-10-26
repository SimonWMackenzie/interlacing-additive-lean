import CurrentAdditive.CanonicalAmbientSourceSelector

noncomputable section

namespace CurrentAdditive.FiniteFieldConstructor.CanonicalAmbient

open Turing EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineStackEmbedding
open CurrentAdditive.SmallBias
open Paper2.YaoMachine Paper2.YaoLookup Paper2.YaoSourceCodec

theorem sourceSelectorOutput_foreign {t : ℕ} (x : YaoSource t)
    (j : Cell t 16) (h : ¬ ∃ i : Fin 12, selectorEmbed t 16 i = j) :
    sourceSelectorOutput x j = sourceDegreeWidthOutput x j := by
  rw [sourceSelectorOutput,
    bank_outside (selectorEmbed t 16) _ _ j h]
  have h6 : j ≠ .selector 6 := by
    intro he; exact h ⟨6, by simpa [selectorEmbed] using he.symm⟩
  simp [selectorInputBank, h6]

theorem sourceSelectorOutput_cap {t : ℕ} (x : YaoSource t) :
    sourceSelectorOutput x (.selector 1) =
      List.replicate
        ((paddedEdgeCount x.2.1)^(2^(t-1))) true := by
  simpa [sourceSelectorOutput] using
    (bank_at (selectorEmbed t 16)
      (selectorInputBank t 16 (paddedEdgeCount x.2.1)
        (sourceDegreeWidthOutput x))
      (Function.update
        (CanonicalSelectorBankPower.initial (paddedEdgeCount x.2.1)) 1
        (List.replicate
          ((paddedEdgeCount x.2.1)^(2^(t-1))) true)) (1 : Fin 12))

theorem sourceSelectorOutput_square_input {t : ℕ} (x : YaoSource t) :
    sourceSelectorOutput x (.degree 3) =
      List.replicate (publicFieldDegree (paddedEdgeBits x.2.1) t) true ∧
    (∀ i : Fin 9, sourceSelectorOutput x (.square i) = []) ∧
    sourceSelectorOutput x (.copyScratch 0) = [] := by
  obtain ⟨hd, _, _⟩ := sourceDegreeWidthOutput_public x
  obtain ⟨_, hs, _, _, hc⟩ := sourceDegreeWidthOutput_next_blank x
  refine ⟨?_, ?_, ?_⟩
  · rw [sourceSelectorOutput_foreign x (.degree 3)
      (by intro ⟨i, hi⟩; cases hi)]
    exact hd
  · intro i
    rw [sourceSelectorOutput_foreign x (.square i)
      (by intro ⟨j, hj⟩; cases hj)]
    exact hs i
  · rw [sourceSelectorOutput_foreign x (.copyScratch 0)
      (by intro ⟨j, hj⟩; cases hj)]
    exact hc

#print axioms sourceSelectorOutput_foreign
#print axioms sourceSelectorOutput_cap
#print axioms sourceSelectorOutput_square_input

end CurrentAdditive.FiniteFieldConstructor.CanonicalAmbient
