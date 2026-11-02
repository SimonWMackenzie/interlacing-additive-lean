import CurrentAdditive.RoundedCodeReset

namespace EthInapproximability.CurrentPaper.RoundedCodeCanonical

open Turing BitMachineEncoding BitMachineStackEmbedding
open Paper2.GeneratorCode
noncomputable section

abbrev Stack := RoundedCodeDraw.Stack

def bank (s : State) (bits : List Bool) (b : ℕ) : Stack → List Bool :=
  fun k => if k = RoundedCodeReset.code then Paper2.CodeAdminNormalization.todoWord s.todo else
    if k = RoundedCodeReset.output then s.output.reverse else
    if k = RoundedCodeReset.tape then bits else
    if k = RoundedCodeReset.width then List.replicate b true else []

theorem start_bank (s : State) (bits : List Bool) (b : ℕ) :
    (RoundedCodeAdmin.start s bits b).stk = bank s bits b := by
  funext k
  rcases k with ((i | i) | (i | i)) | i
  · change BitMachineStackEmbedding.bank RoundedCodeAdmin.adminEmbed _ _ _ = _
    rw [bank_outside]
    · fin_cases i <;> simp [bank, RoundedCodeReset.code, RoundedCodeReset.output,
        RoundedCodeReset.tape, RoundedCodeReset.width, RoundedCodeDraw.oldTape,
        RoundedCodeDraw.oldWidth, Paper2.CodeHeaderDraw.h, Paper2.CodeHeaderDraw.d,
        Paper2.CodeHeaderDraw.output, RoundedCodeAdmin.foreign,
        RoundedCodeAdmin.oldForeign, RoundedCodeDraw.inputBank,
        Paper2.DrawParameterLoader.initialBank, Paper2.DrawParameterLoader.mainBank]
    · rintro ⟨j, h⟩
      cases h
  · change BitMachineStackEmbedding.bank RoundedCodeAdmin.adminEmbed _ _ _ = _
    rw [bank_outside]
    · simp [bank, RoundedCodeReset.code, RoundedCodeReset.output,
        RoundedCodeReset.tape, RoundedCodeReset.width, RoundedCodeDraw.oldTape,
        RoundedCodeDraw.oldWidth, Paper2.CodeHeaderDraw.h, Paper2.CodeHeaderDraw.d,
        Paper2.CodeHeaderDraw.output, RoundedCodeAdmin.foreign,
        RoundedCodeAdmin.oldForeign, RoundedCodeDraw.inputBank,
        Paper2.DrawParameterLoader.initialBank, Paper2.DrawParameterLoader.mainBank]
    · rintro ⟨j, h⟩
      cases h
  · change BitMachineStackEmbedding.bank RoundedCodeAdmin.adminEmbed _ _
      (RoundedCodeAdmin.adminEmbed (.inl i)) = _
    rw [bank_at]
    fin_cases i <;> simp [bank, RoundedCodeReset.code, RoundedCodeReset.output,
      RoundedCodeReset.tape, RoundedCodeReset.width, RoundedCodeDraw.oldTape,
      RoundedCodeDraw.oldWidth, Paper2.CodeHeaderDraw.h, Paper2.CodeHeaderDraw.d,
      Paper2.CodeHeaderDraw.output, Paper2.CodeAdminNormalization.stateCfg,
      Paper2.CodeAdminMachine.ready, Paper2.CodeAdminMachine.cfg,
      Paper2.CodeScanner.bank, Paper2.CodeHeaderMachine.contents, BitMachineInline.cfg]
  · change BitMachineStackEmbedding.bank RoundedCodeAdmin.adminEmbed _ _
      (RoundedCodeAdmin.adminEmbed (.inr i)) = _
    rw [bank_at]
    fin_cases i <;> simp [bank, RoundedCodeReset.code, RoundedCodeReset.output,
      RoundedCodeReset.tape, RoundedCodeReset.width, RoundedCodeDraw.oldTape,
      RoundedCodeDraw.oldWidth, Paper2.CodeHeaderDraw.h, Paper2.CodeHeaderDraw.d,
      Paper2.CodeHeaderDraw.output, Paper2.CodeAdminNormalization.stateCfg,
      Paper2.CodeAdminMachine.ready, Paper2.CodeAdminMachine.cfg,
      Paper2.CodeScanner.bank, Paper2.CodeHeaderMachine.contents, BitMachineInline.cfg]
  · change BitMachineStackEmbedding.bank RoundedCodeAdmin.adminEmbed _ _ _ = _
    rw [bank_outside]
    · simp [bank, RoundedCodeReset.code, RoundedCodeReset.output,
        RoundedCodeReset.tape, RoundedCodeReset.width, RoundedCodeAdmin.foreign,
        RoundedCodeDraw.inputBank]
    · rintro ⟨j, h⟩
      cases h

theorem reset_bank (S : Stack → List Bool) (s : State) (bits : List Bool) (b : ℕ)
    (hC : S RoundedCodeReset.code = Paper2.CodeAdminNormalization.todoWord s.todo)
    (hO : S RoundedCodeReset.output = s.output.reverse)
    (hT : S RoundedCodeReset.tape = bits)
    (hB : S RoundedCodeReset.width = List.replicate b true) :
    RoundedCodeReset.resetBank S = (RoundedCodeAdmin.start s bits b).stk := by
  rw [start_bank]
  funext k
  by_cases hc : k = RoundedCodeReset.code
  · subst k
    simp [RoundedCodeReset.resetBank, RoundedCodeReset.keep, bank, hC]
  · by_cases ho : k = RoundedCodeReset.output
    · subst k
      simp [RoundedCodeReset.resetBank, RoundedCodeReset.keep, bank, hO,
        RoundedCodeReset.output, RoundedCodeReset.code, Paper2.CodeHeaderDraw.output,
        Paper2.CodeHeaderDraw.h]
      exact hO
    · by_cases ht : k = RoundedCodeReset.tape
      · subst k
        simp [RoundedCodeReset.resetBank, RoundedCodeReset.keep, bank, hT,
          RoundedCodeReset.tape, RoundedCodeReset.output, RoundedCodeReset.code,
          RoundedCodeDraw.oldTape, Paper2.CodeHeaderDraw.d, Paper2.CodeHeaderDraw.output,
          Paper2.CodeHeaderDraw.h]
        exact hT
      · by_cases hb : k = RoundedCodeReset.width
        · subst k
          simp [RoundedCodeReset.resetBank, RoundedCodeReset.keep, bank, hB,
            RoundedCodeReset.width, RoundedCodeReset.tape, RoundedCodeReset.output,
            RoundedCodeReset.code, RoundedCodeDraw.oldWidth, RoundedCodeDraw.oldTape,
            Paper2.CodeHeaderDraw.d, Paper2.CodeHeaderDraw.output, Paper2.CodeHeaderDraw.h]
          exact hB
        · simp [RoundedCodeReset.resetBank, RoundedCodeReset.keep, bank, hc, ho, ht, hb]

theorem initial_private_blank (s : State) (bits : List Bool) (b : ℕ)
    (i : Fin RoundedCodeReset.clearCount) :
    ((RoundedCodeAdmin.start s bits b).stk (RoundedCodeReset.slot i)) = [] := by
  rw [start_bank]
  have h := RoundedCodeReset.slot_not_keep i
  have hc : RoundedCodeReset.slot i ≠ RoundedCodeReset.code := fun he => h (Or.inl he)
  have ho : RoundedCodeReset.slot i ≠ RoundedCodeReset.output := fun he => h (Or.inr (Or.inl he))
  have ht : RoundedCodeReset.slot i ≠ RoundedCodeReset.tape := fun he => h (Or.inr (Or.inr (Or.inl he)))
  have hb : RoundedCodeReset.slot i ≠ RoundedCodeReset.width := fun he => h (Or.inr (Or.inr (Or.inr he)))
  simp [bank, hc, ho, ht, hb]

#print axioms start_bank
#print axioms reset_bank
#print axioms initial_private_blank

end
end EthInapproximability.CurrentPaper.RoundedCodeCanonical
