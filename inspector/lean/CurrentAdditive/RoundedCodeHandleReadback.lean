import CurrentAdditive.RoundedCodeHandle
import CurrentAdditive.RoundedCodeCanonical

namespace EthInapproximability.CurrentPaper.RoundedCodeHandle

open BitMachineStackEmbedding
noncomputable section

theorem framed_output_value (S : Stack → List Bool) (c : Paper2.CodeDrawOutput.Config) :
    (framedOutput S c).stk RoundedCodeReset.output = c.stk 1 := by
  change bank outputEmbed S c.stk (outputEmbed 1) = _
  exact bank_at outputEmbed S c.stk 1

theorem framed_output_other (S : Stack → List Bool) (c : Paper2.CodeDrawOutput.Config)
    (k : Stack) (hi : k ≠ .inl RoundedCodeDraw.oldResult)
    (ho : k ≠ RoundedCodeReset.output) : (framedOutput S c).stk k = S k := by
  apply bank_outside
  rintro ⟨i, h⟩
  fin_cases i
  · exact hi h.symm
  · exact ho h.symm

theorem ticket_reset_bank (S : RoundedCodeDraw.OldStack → List Bool)
    (a b : ℕ) (input suffix word : List Bool) (cs : List Paper2.GeneratorCode.Code) (out : List Bool)
    (hCode : S (Paper2.CodeHeaderDraw.h 0) = Paper2.CodeAdminNormalization.todoWord cs) :
    RoundedCodeReset.resetBank
      (framedOutput (RoundedCodeDraw.resultBank S a b input suffix word)
        (Paper2.CodeDrawOutput.cfg none none [] (word.reverse ++ out.reverse))).stk =
      (RoundedCodeAdmin.start ⟨cs, out ++ word⟩ suffix b).stk := by
  let T := RoundedCodeDraw.resultBank S a b input suffix word
  let c := Paper2.CodeDrawOutput.cfg none none [] (word.reverse ++ out.reverse)
  apply RoundedCodeCanonical.reset_bank
  · rw [framed_output_other T c RoundedCodeReset.code]
    · change RoundedCodeDraw.resultBank S a b input suffix word
        (.inl (Paper2.CodeHeaderDraw.h 0)) = Paper2.CodeAdminNormalization.todoWord cs
      rw [RoundedCodeDraw.result_other_old S a b input suffix word (Paper2.CodeHeaderDraw.h 0)]
      · exact hCode
      all_goals simp [RoundedCodeDraw.oldAlphabet, RoundedCodeDraw.oldWidth,
        RoundedCodeDraw.oldTape, RoundedCodeDraw.oldResult,
        Paper2.CodeHeaderDraw.h, Paper2.CodeHeaderDraw.d]
    all_goals simp [RoundedCodeReset.code, RoundedCodeReset.output,
      RoundedCodeDraw.oldResult, Paper2.CodeHeaderDraw.h, Paper2.CodeHeaderDraw.d,
      Paper2.CodeHeaderDraw.output]
  · rw [framed_output_value]
    simp [c, Paper2.CodeDrawOutput.cfg, Paper2.CodeDrawOutput.bank, List.reverse_append]
  · rw [framed_output_other T c RoundedCodeReset.tape]
    · exact RoundedCodeDraw.result_tape S a b input suffix word
    all_goals simp [RoundedCodeReset.tape, RoundedCodeReset.output,
      RoundedCodeDraw.oldTape, RoundedCodeDraw.oldResult,
      Paper2.CodeHeaderDraw.h, Paper2.CodeHeaderDraw.d, Paper2.CodeHeaderDraw.output]
  · rw [framed_output_other T c RoundedCodeReset.width]
    · exact RoundedCodeDraw.result_width S a b input suffix word
    all_goals simp [RoundedCodeReset.width, RoundedCodeReset.output,
      RoundedCodeDraw.oldWidth, RoundedCodeDraw.oldResult,
      Paper2.CodeHeaderDraw.h, Paper2.CodeHeaderDraw.d, Paper2.CodeHeaderDraw.output]

#print axioms ticket_reset_bank

end
end EthInapproximability.CurrentPaper.RoundedCodeHandle
