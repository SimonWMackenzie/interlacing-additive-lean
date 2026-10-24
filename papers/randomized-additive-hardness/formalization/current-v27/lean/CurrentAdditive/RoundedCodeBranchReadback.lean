import CurrentAdditive.RoundedCodeHandleReadback

namespace EthInapproximability.CurrentPaper.RoundedCodeHandle

open Turing BitMachineEncoding BitMachineStackEmbedding
open Paper2.GeneratorCode Paper2.GeneratorSerialization
noncomputable section
set_option maxHeartbeats 1000000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false

theorem branch_from_bank (S : Stack → List Bool)
    (n out : List Bool) (i a b : ℕ) (first second third : Code) (rest : List Bool)
    (hbank : (Paper2.CodeBranchAdapter.initial successBase (fun k => S (.inl k))
      n out i a b first second third rest).stk = fun k => S (.inl k)) :
    ∃ t ≤ 1 + 70 *
      (i + a + b + (Paper2.BranchSelection.inputWord first second third rest).length + 1),
      run t (start .branch3 S) =
        framedBranch S (Paper2.CodeBranchAdapter.final successBase (fun k => S (.inl k))
          n out i a b first second third rest) := by
  let old := fun k : Paper2.CodeBranchAdapter.Stack => S (.inl k)
  let priv := fun k : RoundedLoadedDraw.Stack => S (.inr k)
  have hsum : Sum.elim old priv = S := by
    funext k
    rcases k with k | k <;> rfl
  obtain ⟨t, ht, hr⟩ := branch_run old priv n out i a b first second third rest
  rw [hsum] at hr
  have hstart : framedBranch S (Paper2.CodeBranchAdapter.initial successBase old
      n out i a b first second third rest) =
      ⟨some (.branch (.inr .route)), initial, S⟩ := by
    have hb : bank branchEmbed S (Paper2.CodeBranchAdapter.initial successBase old
        n out i a b first second third rest).stk = S := by
      apply bank_eq_self
      intro k
      exact congrFun hbank k
    change (⟨some (.branch (.inr .route)), initial,
      bank branchEmbed S (Paper2.CodeBranchAdapter.initial successBase old
        n out i a b first second third rest).stk⟩ : Config) = _
    rw [hb]
  rw [hstart] at hr
  have hroute : run 1 (start .branch3 S) =
      ⟨some (.branch (.inr .route)), initial, S⟩ := by
    simp [run, start, program, BitMachineEncoding.advance, TM2.step, TM2.stepAux]
  refine ⟨1 + t, by omega, ?_⟩
  have hjoin : run (1 + t) (start .branch3 S) = run t (run 1 (start .branch3 S)) := by
    rw [run, Nat.add_comm 1 t, Function.iterate_add_apply]
    rfl
  rw [hjoin, hroute]
  exact hr

theorem current_branch_initial (a b cut₁ cut₂ : ℕ) (q : Fin a)
    (first second third : Code) (cs : List Code) (out input suffix : List Bool) :
    let head := Code.branch3 a cut₁ cut₂ first second third
    let S := RoundedCodeAdmin.readyOldBank ⟨head :: cs, out⟩ input b
    let T := RoundedCodeDraw.resultBank S a b input suffix
      ((Paper2.RecursiveLabelCodecScratch.finCodec a).encode q)
    (Paper2.CodeBranchAdapter.initial successBase (fun k => T (.inl k))
      (List.replicate a true) out.reverse q.val cut₁ cut₂ first second third
      (Paper2.CodeAdminNormalization.todoWord cs)).stk = fun k => T (.inl k) := by
  dsimp only
  funext k
  rcases k with ((i | i) | (i | i))
  · fin_cases i
    all_goals simp [Paper2.CodeBranchAdapter.initial, Paper2.CodeBranchAdapter.phaseCfg,
      Paper2.CodeBranchAdapter.framedBank, RoundedCodeDraw.result_tape,
      RoundedCodeDraw.result_word, RoundedCodeDraw.result_alphabet,
      RoundedCodeDraw.result_width, RoundedCodeDraw.result_other_old,
      RoundedCodeDraw.oldAlphabet, RoundedCodeDraw.oldWidth, RoundedCodeDraw.oldTape,
      RoundedCodeDraw.oldResult, RoundedCodeAdmin.readyOldBank,
      Paper2.CodeAdminReady.stopped, Paper2.CodeAdminMachine.cfg, Paper2.CodeScanner.bank,
      Paper2.CodeHeaderMachine.contents, Paper2.CodeHeaderMachine.headerN,
      Paper2.CodeHeaderMachine.headerA, Paper2.CodeHeaderMachine.headerB,
      Paper2.CodeHeaderMachine.headerTail, Paper2.CodeHeaderMachine.headerWord,
      Paper2.DrawParameterLoader.initialBank, Paper2.DrawParameterLoader.mainBank,
      Paper2.CodeHeaderDraw.d, Paper2.CodeHeaderDraw.h,
      Paper2.RecursiveLabelCodecScratch.finCodec]
    all_goals exact (RoundedCodeDraw.result_word _ a b input suffix _).symm
  · rfl
  · fin_cases i
    all_goals simp [Paper2.CodeBranchAdapter.initial, Paper2.CodeBranchAdapter.phaseCfg,
      Paper2.CodeBranchAdapter.framedBank, RoundedCodeDraw.result_tape,
      RoundedCodeDraw.result_word, RoundedCodeDraw.result_alphabet,
      RoundedCodeDraw.result_width, RoundedCodeDraw.result_other_old,
      RoundedCodeDraw.oldAlphabet, RoundedCodeDraw.oldWidth, RoundedCodeDraw.oldTape,
      RoundedCodeDraw.oldResult, RoundedCodeAdmin.readyOldBank,
      Paper2.CodeAdminReady.stopped, Paper2.CodeAdminMachine.cfg, Paper2.CodeScanner.bank,
      Paper2.CodeHeaderMachine.contents, Paper2.CodeHeaderMachine.headerN,
      Paper2.CodeHeaderMachine.headerA, Paper2.CodeHeaderMachine.headerB,
      Paper2.CodeHeaderMachine.headerTail, Paper2.CodeHeaderMachine.headerWord,
      Paper2.DrawParameterLoader.initialBank, Paper2.DrawParameterLoader.mainBank,
      Paper2.CodeHeaderDraw.d, Paper2.CodeHeaderDraw.h,
      Paper2.BranchSelection.inputWord, Paper2.RecursiveLabelCodecScratch.finCodec]
    all_goals exact (RoundedCodeDraw.result_alphabet _ a b input suffix _).symm
  · fin_cases i
    simp [Paper2.CodeBranchAdapter.initial, Paper2.CodeBranchAdapter.phaseCfg,
      Paper2.CodeBranchAdapter.framedBank, RoundedCodeDraw.result_other_old,
      RoundedCodeDraw.oldAlphabet, RoundedCodeDraw.oldWidth, RoundedCodeDraw.oldTape,
      RoundedCodeDraw.oldResult, RoundedCodeAdmin.readyOldBank,
      Paper2.CodeAdminReady.stopped, Paper2.CodeAdminMachine.cfg, Paper2.CodeScanner.bank,
      Paper2.CodeHeaderDraw.output, Paper2.CodeHeaderDraw.d, Paper2.CodeHeaderDraw.h]

theorem branch_reset_bank (T : Stack → List Bool)
    (a b cut₁ cut₂ : ℕ) (i : ℕ) (first second third : Code)
    (cs : List Code) (out suffix : List Bool)
    (hT : T (.inl RoundedCodeDraw.oldTape) = suffix)
    (hB : T (.inl RoundedCodeDraw.oldWidth) = List.replicate b true) :
    let selected := if i < cut₁ then first else if i < cut₂ then second else third
    RoundedCodeReset.resetBank
      (framedBranch T (Paper2.CodeBranchAdapter.final successBase (fun k => T (.inl k))
        (List.replicate a true) out.reverse i cut₁ cut₂ first second third
        (Paper2.CodeAdminNormalization.todoWord cs))).stk =
      (RoundedCodeAdmin.start ⟨selected :: cs, out⟩ suffix b).stk := by
  dsimp only
  apply RoundedCodeCanonical.reset_bank
  · change bank branchEmbed T _ (branchEmbed (Paper2.CodeHeaderDraw.h 0)) = _
    rw [bank_at]
    simp only [BitMachineInline.cfg]
    simpa [Paper2.CodeAdminNormalization.todoWord, Paper2.CodeBranchAdapter.h,
      Paper2.CodeHeaderDraw.h] using Paper2.CodeBranchAdapter.final_code successBase
        (fun k => T (.inl k)) (List.replicate a true) out.reverse i cut₁ cut₂
        first second third (Paper2.CodeAdminNormalization.todoWord cs)
  · change bank branchEmbed T _ (branchEmbed Paper2.CodeHeaderDraw.output) = _
    rw [bank_at]
    simp only [BitMachineInline.cfg]
    exact Paper2.CodeBranchAdapter.final_output successBase
      (fun k => T (.inl k)) (List.replicate a true) out.reverse i cut₁ cut₂
      first second third (Paper2.CodeAdminNormalization.todoWord cs)
  · change bank branchEmbed T _ (branchEmbed RoundedCodeDraw.oldTape) = _
    rw [bank_at]
    simp only [BitMachineInline.cfg]
    exact (Paper2.CodeBranchAdapter.final_tape successBase
      (fun k => T (.inl k)) (List.replicate a true) out.reverse i cut₁ cut₂
      first second third (Paper2.CodeAdminNormalization.todoWord cs)).trans hT
  · change bank branchEmbed T _ (branchEmbed RoundedCodeDraw.oldWidth) = _
    rw [bank_at]
    exact hB

#print axioms current_branch_initial
#print axioms branch_reset_bank

end
end EthInapproximability.CurrentPaper.RoundedCodeHandle
