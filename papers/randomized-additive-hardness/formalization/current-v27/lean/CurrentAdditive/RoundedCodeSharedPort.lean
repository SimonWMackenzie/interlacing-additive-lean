import CurrentAdditive.RoundedCodeFramed

namespace EthInapproximability.CurrentPaper.RoundedCodeOutput

open Turing BitMachineEncoding BitMachineStackEmbedding
open Paper2.GeneratorCode Paper2.GeneratorPositive Paper2.GeneratorSerialization
open CurrentAdditive.RoundedDraw
noncomputable section
set_option maxHeartbeats 1000000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false

variable {J : Type*} [DecidableEq J]

abbrev SharedBank (J : Type*) := J ⊕ {k : Stack // k ≠ resultPort}

instance sharedDecidableEq : DecidableEq (SharedBank J) := by
  classical
  infer_instance

def sharedSlots (source : J) : Stack ↪ SharedBank J where
  toFun k := if hk : k = resultPort then .inl source else .inr ⟨k, hk⟩
  inj' := by
    intro k l he
    dsimp only at he
    split_ifs at he <;> simp_all

def freshBank (tape : List Bool) (b : ℕ) (k : {k : Stack // k ≠ resultPort}) : List Bool :=
  if k.val = tapePort then tape else if k.val = widthPort then List.replicate b true else []

def sharedInitial (F : J → List Bool) (tape : List Bool) (b : ℕ) : SharedBank J → List Bool :=
  Sum.elim F (freshBank tape b)

def sharedFinal (source : J) (F : J → List Bool) (out tape : List Bool) (b : ℕ) :
    SharedBank J → List Bool :=
  Sum.elim (fun j => if j = source then out else F j) (freshBank tape b)

theorem shared_input (source : J) (F : J → List Bool) (c : Code)
    (hc : F source = encodeCode c) (tape : List Bool) (b : ℕ) (k : Stack) :
    sharedInitial F tape b (sharedSlots source k) = (start c tape b).stk k := by
  change _ = (RoundedCodeAdmin.start (Paper2.GeneratorCode.initial c) tape b).stk k
  rw [RoundedCodeCanonical.start_bank]
  by_cases hk : k = resultPort
  · subst k
    simpa [sharedSlots, sharedInitial, RoundedCodeCanonical.bank,
      Paper2.GeneratorCode.initial, resultPort, Paper2.CodeAdminNormalization.todoWord] using hc
  · change k ≠ RoundedCodeReset.code at hk
    by_cases ho : k = outputPort
    · subst k
      simp [sharedSlots, sharedInitial, freshBank, RoundedCodeCanonical.bank,
        resultPort, outputPort, tapePort, widthPort, RoundedCodeReset.code,
        RoundedCodeReset.output, RoundedCodeReset.tape, RoundedCodeReset.width,
        RoundedCodeDraw.oldTape, RoundedCodeDraw.oldWidth, Paper2.GeneratorCode.initial,
        Paper2.CodeHeaderDraw.h, Paper2.CodeHeaderDraw.d, Paper2.CodeHeaderDraw.output]
    · change k ≠ RoundedCodeReset.output at ho
      simp [sharedSlots, sharedInitial, freshBank, RoundedCodeCanonical.bank,
        resultPort, tapePort, widthPort, hk, ho, Paper2.GeneratorCode.initial] <;> rfl

theorem shared_final_bank (source : J) (F : J → List Bool)
    (input out tape : List Bool) (b : ℕ) :
    bank (sharedSlots source) (sharedInitial F input b) (finalBank out tape b) =
      sharedFinal source F out tape b := by
  funext k
  rcases k with j | k
  · by_cases hj : j = source
    · subst j
      change bank (sharedSlots source) _ _ (sharedSlots source resultPort) = _
      rw [bank_at]
      simp [finalBank, sharedFinal]
    · rw [bank_outside]
      · simp [sharedFinal, sharedInitial, hj]
      · rintro ⟨i, hi⟩
        dsimp [sharedSlots] at hi
        split_ifs at hi <;> simp_all
  · have hk : sharedSlots source k.val = .inr k := by simp [sharedSlots, k.property]
    rw [← hk]
    rw [bank_at]
    simp [finalBank, sharedFinal, freshBank, sharedSlots, k.property]

theorem physical_shared {A : ℕ} (source : J) (F : J → List Bool)
    (c : Code) (hc : Positive c) (hcode : F source = encodeCode c) (b N : ℕ)
    (hA : (meaning c).maxAlphabet ≤ A) (hN : (meaning c).maxDraws ≤ N)
    (bits : BitBlocks b N) (suffix : List Bool) :
    ∃ t ≤ RoundedCodeLoop.interpreterCoefficient * (N + 1) * (codeSize c + b + 3) ^ 2 +
        codeSize c + 2,
      ((BitMachineEncoding.advance (embeddedProgram (sharedSlots source)))^[t])
        (⟨some (BitMachineRawSequence.leftLabel (.inl RoundedCodeLoop.entry)), initial,
          sharedInitial F (RoundedCodeLoop.tapeWord b N bits ++ suffix) b⟩ :
            TM2.Cfg (fun _ : SharedBank J => Bool) Label Control) =
        ⟨none, initial, sharedFinal source F
          (CurrentAdditive.RoundedProgram.runProgram b N ⟨meaning c, hA⟩ hN bits)
          ((RoundedCodeLoop.execute b N (Paper2.GeneratorCode.initial c) bits).2 ++ suffix) b⟩ := by
  obtain ⟨t, ht, hr⟩ := physical_from_bank (sharedSlots source)
    (sharedInitial F (RoundedCodeLoop.tapeWord b N bits ++ suffix) b)
    c hc b N hA hN bits suffix (shared_input source F c hcode _ b)
  exact ⟨t, ht, by simpa only [shared_final_bank] using hr⟩

#print axioms physical_shared

end
end EthInapproximability.CurrentPaper.RoundedCodeOutput
