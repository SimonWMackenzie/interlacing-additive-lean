import CurrentAdditive.RoundedCodeDraw

namespace EthInapproximability.CurrentPaper.RoundedCodeDraw

open Turing BitMachineEncoding BitMachineStackEmbedding
noncomputable section

private theorem slot_publicA : includeDraw RoundedPrepare.publicA = .inl oldAlphabet := by
  simp [includeDraw, slot]

private theorem slot_publicB : includeDraw RoundedPrepare.publicB = .inl oldWidth := by
  simp [includeDraw, slot, RoundedPrepare.publicA, RoundedPrepare.publicB]

private theorem slot_tape : includeDraw RoundedPrepare.tape = .inl oldTape := by
  simp [includeDraw, slot, RoundedPrepare.publicA, RoundedPrepare.publicB,
    RoundedPrepare.tape]

private theorem slot_result : includeDraw RoundedPrepare.output = .inl oldResult := by
  simp [includeDraw, slot, RoundedPrepare.publicA, RoundedPrepare.publicB,
    RoundedPrepare.tape, RoundedPrepare.output,
    RoundedCleanDraw.tape, RoundedCleanDraw.output]

theorem result_tape (S : OldStack → List Bool) (a b : ℕ)
    (input suffix result : List Bool) :
    resultBank S a b input suffix result (.inl oldTape) = suffix := by
  rw [resultBank, ← slot_tape, bank_at]
  change bank RoundedLoadedDraw.drawEmbed _ _
    (RoundedLoadedDraw.drawEmbed RoundedCleanDraw.tape) = _
  rw [bank_at]
  simp [RoundedCleanDraw.cleanBank]

theorem result_word (S : OldStack → List Bool) (a b : ℕ)
    (input suffix result : List Bool) :
    resultBank S a b input suffix result (.inl oldResult) = result := by
  rw [resultBank, ← slot_result, bank_at]
  change bank RoundedLoadedDraw.drawEmbed _ _
    (RoundedLoadedDraw.drawEmbed RoundedCleanDraw.output) = _
  rw [bank_at]
  simp [RoundedCleanDraw.cleanBank, RoundedCleanDraw.tape, RoundedCleanDraw.output]

private theorem final_public (a b : ℕ) (input suffix result : List Bool)
    (i : Fin 3) :
    RoundedLoadedDraw.finalBank a b input suffix result (.inr (.inr i)) =
      if i = 0 then List.replicate a true else if i = 1 then List.replicate b true else [] := by
  rw [RoundedLoadedDraw.finalBank, bank_outside]
  · unfold RoundedPrepare.finalBank
    simp only [Function.update_of_ne (show (.inr (.inr i) : LocalStack) ≠ RoundedPrepare.output by
      simp [RoundedPrepare.output]), Function.update_of_ne
        (show (.inr (.inr i) : LocalStack) ≠ RoundedPrepare.alphabet by simp [RoundedPrepare.alphabet])]
    rw [RoundedPrepare.converted_public]
    fin_cases i <;> simp [RoundedPrepare.fueledBank, RoundedPrepare.initialBank,
      RoundedPrepare.fuel, RoundedPrepare.cap, RoundedPrepare.count,
      RoundedPrepare.publicA, RoundedPrepare.publicB, RoundedPrepare.tape]
  · rintro ⟨j, h⟩
    cases h

theorem result_alphabet (S : OldStack → List Bool) (a b : ℕ)
    (input suffix result : List Bool) :
    resultBank S a b input suffix result (.inl oldAlphabet) = List.replicate a true := by
  rw [resultBank, ← slot_publicA, bank_at]
  exact final_public a b input suffix result 0

theorem result_width (S : OldStack → List Bool) (a b : ℕ)
    (input suffix result : List Bool) :
    resultBank S a b input suffix result (.inl oldWidth) = List.replicate b true := by
  rw [resultBank, ← slot_publicB, bank_at]
  exact final_public a b input suffix result 1

theorem result_other_old (S : OldStack → List Bool) (a b : ℕ)
    (input suffix result : List Bool) (k : OldStack)
    (hA : k ≠ oldAlphabet) (hB : k ≠ oldWidth)
    (hT : k ≠ oldTape) (hR : k ≠ oldResult) :
    resultBank S a b input suffix result (.inl k) = S k := by
  rw [resultBank, bank_outside]
  · rfl
  · rintro ⟨j, h⟩
    change slot j = .inl k at h
    unfold slot at h
    split_ifs at h <;> simp_all

theorem result_old_preserved (S : OldStack → List Bool) (a b : ℕ)
    (input suffix result : List Bool) (k : OldStack)
    (hA : S oldAlphabet = List.replicate a true)
    (hB : S oldWidth = List.replicate b true)
    (hT : k ≠ oldTape) (hR : k ≠ oldResult) :
    resultBank S a b input suffix result (.inl k) = S k := by
  by_cases hkA : k = oldAlphabet
  · subst k
    exact (result_alphabet S a b input suffix result).trans hA.symm
  · by_cases hkB : k = oldWidth
    · subst k
      exact (result_width S a b input suffix result).trans hB.symm
    · exact result_other_old S a b input suffix result k hkA hkB hT hR

#print axioms result_old_preserved

end
end EthInapproximability.CurrentPaper.RoundedCodeDraw
