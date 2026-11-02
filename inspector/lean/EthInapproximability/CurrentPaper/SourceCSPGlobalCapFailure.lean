import EthInapproximability.CurrentPaper.SourceCSPGlobalCapFromLiteral

/-!
# Physical rejecting output after a failed CSP vertex cap

The header and cap stages are existing checked programs. This file closes only
the failed-cap arm of their common global instruction table.
-/

namespace EthInapproximability.CurrentPaper.SourceCSPGlobalDecisionProgram

open Turing BitMachineEncoding BitMachineStackEmbedding

def outputSlot {q : Nat} : Stack q :=
  inputEmbedding SourceCSPRejectWriterFrame.outputSlot

/-- A failed physical cap check executes the same global program's literal
rejecting-CNF writer, clearing any previous output word first. -/
theorem cap_failure_reject (a q : Nat)
    (v : Unit × SourceCSPPositiveCapEntry.CapControl)
    (before : Stack q → List Bool)
    (hcap : (before SourceCSPHeaderRowBridge.capSource).head? ≠ some true) :
    ∃ (t : Nat) (after : Stack q → List Bool),
      t ≤ (before outputSlot).length + 4 ∧
      ((advance (program a q))^[t])
        (⟨some .capCheck, .cap v, before⟩ :
          TM2.Cfg (fun _ : Stack q => Bool) (Label a q) (Control a q)) =
        ⟨none, .writer none, after⟩ ∧
      after outputSlot = SourceCSPRejectFormula.bits ∧
      (∀ k : Stack q, k ≠ outputSlot → after k = before k) := by
  let emb : SourceCSPInputFrame.Stack ↪ Stack q := inputEmbedding
  let B : SourceCSPInputFrame.Stack → List Bool := fun k => before (emb k)
  obtain ⟨tw, W, htw, hrw, hout, hforeign⟩ :=
    SourceCSPRejectWriterFrame.reject_run B
  let localCfg : TM2.Cfg (fun _ : SourceCSPInputFrame.Stack => Bool)
      SourceCSPRejectWriter.Label (Option Bool) :=
    ⟨some .clear, none, B⟩
  have hhalt : (((advance SourceCSPRejectWriterFrame.program)^[tw])
      localCfg).l = none := by
    rw [show ((advance SourceCSPRejectWriterFrame.program)^[tw]) localCfg =
      (⟨none, none, W⟩ : TM2.Cfg
        (fun _ : SourceCSPInputFrame.Stack => Bool)
        SourceCSPRejectWriter.Label (Option Bool)) from hrw]
  let read : Control a q → Option Bool := fun x => match x with
    | .writer w => w
    | _ => none
  have hleft : Function.LeftInverse read Control.writer := by
    intro w
    rfl
  obtain ⟨u, hu, hrun⟩ := outputs emb before Label.rejectWriter
    Control.writer read hleft none SourceCSPRejectWriterFrame.program
    (program a q) (fun _ => rfl) localCfg tw hhalt
  have hstart : cfg emb before Label.rejectWriter Control.writer none
      localCfg =
      (⟨some (.rejectWriter .clear), .writer none, before⟩ :
        TM2.Cfg (fun _ : Stack q => Bool) (Label a q) (Control a q)) := by
    simp only [cfg, stackCfg, BitMachineInline.cfg, localCfg, B, emb]
    congr 1
    apply bank_eq_self
    intro k
    rfl
  rw [hstart, hrw] at hrun
  let after := bank emb before W
  have hwriter : ((advance (program a q))^[u])
      (⟨some (.rejectWriter .clear), .writer none, before⟩ :
        TM2.Cfg (fun _ : Stack q => Bool) (Label a q) (Control a q)) =
      ⟨none, .writer none, after⟩ := by
    simpa only [after, cfg, stackCfg, BitMachineInline.cfg,
      Option.map_none] using hrun
  refine ⟨u + 1, after, ?_, ?_, ?_, ?_⟩
  · have : (B SourceCSPRejectWriterFrame.outputSlot).length =
        (before outputSlot).length := rfl
    omega
  · rw [Function.iterate_succ_apply, cap_check_bad a q v before hcap]
    exact hwriter
  · exact (bank_at emb before W
      SourceCSPRejectWriterFrame.outputSlot).trans hout
  · intro k hk
    by_cases himage : ∃ j, emb j = k
    · obtain ⟨j, rfl⟩ := himage
      have hj : j ≠ SourceCSPRejectWriterFrame.outputSlot := by
        intro heq
        apply hk
        simp only [outputSlot, emb, heq]
      exact (bank_at emb before W j).trans (hforeign j hj)
    · exact bank_outside emb before W k himage

end EthInapproximability.CurrentPaper.SourceCSPGlobalDecisionProgram

namespace EthInapproximability.CurrentPaper.SourceCSPGlobalCapFromLiteral

open Turing BitMachineEncoding

/-- A raw bitstring classified positive, but failing the actual vertex cap,
continues through the global table to the fixed unsatisfiable 3CNF output.
The terminal bound charges the physical output word that the writer clears. -/
theorem raw_positive_cap_failure (a q : Nat) (input : List Bool) :
    ∃ (tp : Nat) (v : SourceCSPGuardOutputCombined.PrefixControl)
      (Sp : SourceCSPInputFrame.Stack → List Bool),
      tp ≤ SourceCSPGuardDispatchSequence.bound a q input.length ∧
      ((advance (SourceCSPGuardOutputCombined.program a q))^[tp])
        (SourceCSPGuardOutputCombined.initial a q input) =
          (⟨some .route, (v, none), Sp⟩ :
            TM2.Cfg (fun _ : SourceCSPInputFrame.Stack => Bool)
              (SourceCSPGuardOutputCombined.Label a q)
              SourceCSPGuardOutputCombined.Control) ∧
      (v.2.2 = some .positive →
        ∃ (n m tcap : Nat) (rest : List Bool)
          (S : SourceCSPGlobalDecisionProgram.Stack q → List Bool)
          (c : Unit × SourceCSPPositiveCapEntry.CapControl),
          input = SourceCSPHeaderParse.header n m a q ++ rest ∧
          m ≤ input.length ∧
          tcap ≤ SourceCSPGuardDispatchSequence.bound a q input.length + 2 +
            capBound q input.length input.length ∧
          ((advance (SourceCSPGlobalDecisionProgram.program a q))^[tcap])
            (SourceCSPGlobalDecisionProgram.initial a q input) =
              (⟨some .capCheck, .cap c, S⟩ :
                TM2.Cfg (fun _ : SourceCSPGlobalDecisionProgram.Stack q => Bool)
                  (SourceCSPGlobalDecisionProgram.Label a q)
                  (SourceCSPGlobalDecisionProgram.Control a q)) ∧
          (¬ (0 < n ∧ n ≤ q * m) →
            ∃ (t : Nat)
              (T : SourceCSPGlobalDecisionProgram.Stack q → List Bool),
              t ≤ tcap + (S SourceCSPGlobalDecisionProgram.outputSlot).length + 4 ∧
              ((advance (SourceCSPGlobalDecisionProgram.program a q))^[t])
                (SourceCSPGlobalDecisionProgram.initial a q input) =
                  (⟨none, .writer none, T⟩ :
                    TM2.Cfg (fun _ : SourceCSPGlobalDecisionProgram.Stack q => Bool)
                      (SourceCSPGlobalDecisionProgram.Label a q)
                      (SourceCSPGlobalDecisionProgram.Control a q)) ∧
              T SourceCSPGlobalDecisionProgram.outputSlot =
                SourceCSPRejectFormula.bits ∧
              T SourceCSPGlobalDecisionProgram.outputSlot ∉
                EncodedCNF.Language ∧
              (∀ k : SourceCSPGlobalDecisionProgram.Stack q,
                k ≠ SourceCSPGlobalDecisionProgram.outputSlot → T k = S k))) := by
  obtain ⟨tp, v, Sp, htp, hrp, hpositive⟩ := raw_positive_cap a q input
  refine ⟨tp, v, Sp, htp, hrp, ?_⟩
  intro hv
  obtain ⟨n, m, tcap, rest, S, c, hinput, hm, htcap, hcapRun, hbit⟩ :=
    hpositive hv
  refine ⟨n, m, tcap, rest, S, c, hinput, hm, htcap, hcapRun, ?_⟩
  intro hfail
  have hbad : (S SourceCSPHeaderRowBridge.capSource).head? ≠
      some true := by
    rw [hbit]
    simp [hfail]
  obtain ⟨tw, T, htw, hwriter, hout, hforeign⟩ :=
    SourceCSPGlobalDecisionProgram.cap_failure_reject a q c S hbad
  refine ⟨tcap + tw, T, by omega, ?_, hout, ?_, hforeign⟩
  · rw [show tcap + tw = tw + tcap by omega,
      Function.iterate_add_apply, hcapRun]
    exact hwriter
  · rw [hout]
    exact SourceCSPRejectFormula.bits_not_language

end EthInapproximability.CurrentPaper.SourceCSPGlobalCapFromLiteral


