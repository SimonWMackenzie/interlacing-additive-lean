import EthInapproximability.CurrentPaper.SourceCSPGlobalDecisionProgram

/-!
# Charged in-bank retention of the raw CSP row suffix

At the row handoff the global table copies the literal unread suffix into the
fifth row-outer cell, which is foreign to the corrected validator's Fin4 bank.
The temporary third copy cell is a row-outer work cell and is cleared before
the validator starts.
-/

namespace EthInapproximability.CurrentPaper.SourceCSPGlobalRetentionRun

open Turing BitMachineEncoding BitMachineStackEmbedding

theorem copy_framed (a q : Nat)
    (before : SourceCSPGlobalDecisionProgram.Stack q → List Bool)
    (word : List Bool)
    (hsource : before SourceCSPHeaderRowBridge.source = word)
    (hsaved : before SourceCSPGlobalDecisionProgram.savedSource = [])
    (hwork : before SourceCSPGlobalDecisionProgram.copyWork = []) :
    ∃ t S, t ≤ 2 * word.length + 2 ∧
      ((advance (SourceCSPGlobalDecisionProgram.program a q))^[t])
        (⟨some (.rowCopy .scan), .rowCopy none, before⟩ :
          TM2.Cfg (fun _ : SourceCSPGlobalDecisionProgram.Stack q => Bool)
            (SourceCSPGlobalDecisionProgram.Label a q)
            (SourceCSPGlobalDecisionProgram.Control a q)) =
        ⟨some .rowBegin, .rowCopy none, S⟩ ∧
      S SourceCSPHeaderRowBridge.source = word ∧
      S SourceCSPGlobalDecisionProgram.savedSource = word ∧
      S SourceCSPGlobalDecisionProgram.copyWork = [] ∧
      (∀ k, k ≠ SourceCSPHeaderRowBridge.source →
        k ≠ SourceCSPGlobalDecisionProgram.savedSource →
        k ≠ SourceCSPGlobalDecisionProgram.copyWork → S k = before k) := by
  let ι := SourceCSPGlobalDecisionProgram.retentionEmbedding (q := q)
  let localCfg := BitMachineCopy.cfg (some .scan) none word [] []
  have hlocal : ((advance BitMachineCopy.program)^[2 * word.length + 2])
      localCfg = BitMachineCopy.cfg none none word word [] := by
    simpa only [BitMachineCopy.run, localCfg, List.append_nil] using
      BitMachineCopy.run_correct none word []
  have hhalt : (((advance BitMachineCopy.program)^[2 * word.length + 2])
      localCfg).l = none := by rw [hlocal]; rfl
  let read : SourceCSPGlobalDecisionProgram.Control a q → Option Bool :=
    fun x => match x with
      | .rowCopy v => v
      | _ => none
  have hleft : Function.LeftInverse read
      SourceCSPGlobalDecisionProgram.Control.rowCopy := by
    intro v
    rfl
  obtain ⟨t, ht, hr⟩ := outputs ι before
    SourceCSPGlobalDecisionProgram.Label.rowCopy
    SourceCSPGlobalDecisionProgram.Control.rowCopy
    read hleft (some .rowBegin)
    BitMachineCopy.program (SourceCSPGlobalDecisionProgram.program a q)
    (fun _ => rfl) localCfg (2 * word.length + 2) hhalt
  have hstart : BitMachineStackEmbedding.cfg ι before
      SourceCSPGlobalDecisionProgram.Label.rowCopy
      SourceCSPGlobalDecisionProgram.Control.rowCopy
      (some .rowBegin) localCfg =
      (⟨some (.rowCopy .scan), .rowCopy none, before⟩ :
        TM2.Cfg (fun _ : SourceCSPGlobalDecisionProgram.Stack q => Bool)
          (SourceCSPGlobalDecisionProgram.Label a q)
          (SourceCSPGlobalDecisionProgram.Control a q)) := by
    simp only [BitMachineStackEmbedding.cfg, stackCfg,
      BitMachineInline.cfg, localCfg, BitMachineCopy.cfg]
    congr 1
    apply bank_eq_self
    intro k
    fin_cases k <;> simp [ι,
      SourceCSPGlobalDecisionProgram.retentionEmbedding,
      BitMachineCopy.stackContents]
    · exact hsource.symm
    · exact hsaved
    · exact hwork
  rw [hstart, hlocal] at hr
  let S := bank ι before (BitMachineCopy.stackContents word word [])
  refine ⟨t, S, ht, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [S, BitMachineStackEmbedding.cfg, stackCfg,
      BitMachineInline.cfg, id_eq, Option.map_none] using hr
  · change bank ι before _ (ι 0) = _
    rw [bank_at]
    rfl
  · change bank ι before _ (ι 1) = _
    rw [bank_at]
    rfl
  · change bank ι before _ (ι 2) = _
    rw [bank_at]
    rfl
  · intro k hk0 hk1 hk2
    apply bank_outside
    rintro ⟨i, hi⟩
    fin_cases i <;> simp [ι,
      SourceCSPGlobalDecisionProgram.retentionEmbedding] at hi
    · exact hk0 hi.symm
    · exact hk1 hi.symm
    · exact hk2 hi.symm

theorem retained_handoff (a q : Nat)
    (c : SourceCSPGlobalDecisionProgram.Control a q)
    (before : SourceCSPGlobalDecisionProgram.Stack q → List Bool)
    (word : List Bool)
    (hsource : before SourceCSPHeaderRowBridge.source = word)
    (hsaved : before SourceCSPGlobalDecisionProgram.savedSource = [])
    (hwork : before SourceCSPGlobalDecisionProgram.copyWork = []) :
    ∃ t S, t ≤ 2 * word.length + 4 ∧
      ((advance (SourceCSPGlobalDecisionProgram.program a q))^[t])
        (⟨some .rowHandoff, c, before⟩ :
          TM2.Cfg (fun _ : SourceCSPGlobalDecisionProgram.Stack q => Bool)
            (SourceCSPGlobalDecisionProgram.Label a q)
            (SourceCSPGlobalDecisionProgram.Control a q)) =
        ⟨some (.row (SourceCSPRowLoopController.adminLabel .check)),
          .row SourceCSPRowLoopController.initialControl, S⟩ ∧
      S SourceCSPHeaderRowBridge.source = word ∧
      S SourceCSPGlobalDecisionProgram.savedSource = word ∧
      S SourceCSPGlobalDecisionProgram.copyWork = [] ∧
      (∀ k, k ≠ SourceCSPHeaderRowBridge.source →
        k ≠ SourceCSPGlobalDecisionProgram.savedSource →
        k ≠ SourceCSPGlobalDecisionProgram.copyWork → S k = before k) := by
  obtain ⟨u, S, hu, hcopy, hsrc, hdst, hscr, hother⟩ :=
    copy_framed a q before word hsource hsaved hwork
  have henter : advance (SourceCSPGlobalDecisionProgram.program a q)
      (⟨some .rowHandoff, c, before⟩ :
        TM2.Cfg (fun _ : SourceCSPGlobalDecisionProgram.Stack q => Bool)
          (SourceCSPGlobalDecisionProgram.Label a q)
          (SourceCSPGlobalDecisionProgram.Control a q)) =
      ⟨some (.rowCopy .scan), .rowCopy none, before⟩ := by rfl
  have hbegin : advance (SourceCSPGlobalDecisionProgram.program a q)
      (⟨some .rowBegin, .rowCopy none, S⟩ :
        TM2.Cfg (fun _ : SourceCSPGlobalDecisionProgram.Stack q => Bool)
          (SourceCSPGlobalDecisionProgram.Label a q)
          (SourceCSPGlobalDecisionProgram.Control a q)) =
      ⟨some (.row (SourceCSPRowLoopController.adminLabel .check)),
        .row SourceCSPRowLoopController.initialControl, S⟩ := by rfl
  refine ⟨u + 2, S, by omega, ?_, hsrc, hdst, hscr, hother⟩
  change ((advance (SourceCSPGlobalDecisionProgram.program a q))^[u + 2]) _ = _
  rw [show u + 2 = 1 + u + 1 by omega,
    Function.iterate_add_apply]
  simp only [Function.iterate_one]
  rw [show 1 + u = u + 1 by omega,
    Function.iterate_succ_apply', henter, hcopy, hbegin]

end EthInapproximability.CurrentPaper.SourceCSPGlobalRetentionRun
