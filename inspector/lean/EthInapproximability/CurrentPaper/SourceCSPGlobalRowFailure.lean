import EthInapproximability.CurrentPaper.SourceCSPGlobalPositiveRows
import EthInapproximability.CurrentPaper.SourceCSPGlobalCapFailure

/-!
# Physical rejecting output after a failed CSP row validation

The existing row validator decides whether the retained literal suffix is
exactly a typed row list. This file closes only its negative result on the
same global instruction table; it does not emit clauses for accepted rows.
-/

namespace EthInapproximability.CurrentPaper.SourceCSPGlobalDecisionProgram

open Turing BitMachineEncoding BitMachineStackEmbedding

/-- A failed physical row decision executes the global program's literal
rejecting-CNF writer, clearing any existing output word first. -/
theorem row_failure_reject (a q : Nat)
    (v : SourceCSPRowLoopController.QueryControl ×
      SourceCSPRowLoopController.ResetControl)
    (before : Stack q → List Bool) :
    ∃ (t : Nat) (after : Stack q → List Bool),
      t ≤ (before outputSlot).length + 4 ∧
      ((advance (program a q))^[t])
        (⟨some .afterRow, .row (v, some false), before⟩ :
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
  · rw [Function.iterate_succ_apply, after_row_failure a q v before]
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

namespace EthInapproximability.CurrentPaper.SourceCSPGlobalPositiveRows

open Turing BitMachineEncoding

def physicalRowBound (a q L : Nat) : Nat :=
  SourceCSPGuardDispatchSequence.bound a q L + 2 +
    SourceCSPGlobalCapFromLiteral.capBound q L L +
    (1 + 2 * L + 4 * (q * L) + 2 * L + 13) +
    (2 * L + 4) +
    SourceCSPRowLoopTotalPolynomial.loopCoefficient q (a ^ q) *
      (L + 1) ^ 3

/-- For every raw positive-tag input, a physically successful vertex cap
followed by a suffix that fails exact typed-row decoding produces the fixed
rejecting 3CNF on the same global program. The rejected semantic condition
is computed from the actual retained suffix, with no supplied row oracle. -/
theorem raw_positive_rows_failure (a q : Nat) (input : List Bool) :
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
        ∃ (n m : Nat) (rest : List Bool),
          input = SourceCSPHeaderParse.header n m a q ++ rest ∧
          (0 < n ∧ n ≤ q * m →
            (¬ ∃ rows : Fin m → SourceCSPCodec.Row n a q,
              SourceCSPCodec.readFn (SourceCSPCodec.readRow n a q) m rest =
                some (rows, [])) →
            ∃ (trow t : Nat)
              (S T : SourceCSPGlobalDecisionProgram.Stack q → List Bool)
              (vr : SourceCSPRowLoopController.QueryControl ×
                SourceCSPRowLoopController.ResetControl),
              trow ≤ physicalRowBound a q input.length ∧
              ((advance (SourceCSPGlobalDecisionProgram.program a q))^[trow])
                (SourceCSPGlobalDecisionProgram.initial a q input) =
                  (⟨some .afterRow, .row (vr, some false), S⟩ :
                    TM2.Cfg
                      (fun _ : SourceCSPGlobalDecisionProgram.Stack q => Bool)
                      (SourceCSPGlobalDecisionProgram.Label a q)
                      (SourceCSPGlobalDecisionProgram.Control a q)) ∧
              t ≤ trow +
                (S SourceCSPGlobalDecisionProgram.outputSlot).length + 4 ∧
              ((advance (SourceCSPGlobalDecisionProgram.program a q))^[t])
                (SourceCSPGlobalDecisionProgram.initial a q input) =
                  (⟨none, .writer none, T⟩ :
                    TM2.Cfg
                      (fun _ : SourceCSPGlobalDecisionProgram.Stack q => Bool)
                      (SourceCSPGlobalDecisionProgram.Label a q)
                      (SourceCSPGlobalDecisionProgram.Control a q)) ∧
              T SourceCSPGlobalDecisionProgram.outputSlot =
                SourceCSPRejectFormula.bits ∧
              T SourceCSPGlobalDecisionProgram.outputSlot ∉
                EncodedCNF.Language ∧
              (∀ k : SourceCSPGlobalDecisionProgram.Stack q,
                k ≠ SourceCSPGlobalDecisionProgram.outputSlot → T k = S k))) := by
  obtain ⟨tp, v, Sp, htp, hrp, hpositive⟩ :=
    raw_positive_rows a q input
  refine ⟨tp, v, Sp, htp, hrp, ?_⟩
  intro hv
  obtain ⟨n, m, rest, hinput, hrows⟩ := hpositive hv
  refine ⟨n, m, rest, hinput, ?_⟩
  intro hn hbad
  obtain ⟨trow, S, vr, b, htrow, hrowrun, hsem, _, _⟩ := hrows hn
  have hb : b = false := by
    cases b with
    | false => rfl
    | true => exact False.elim (hbad (hsem.mp rfl))
  subst b
  obtain ⟨tw, T, htw, hwriter, hout, hforeign⟩ :=
    SourceCSPGlobalDecisionProgram.row_failure_reject a q vr S
  refine ⟨trow, trow + tw, S, T, vr, ?_, hrowrun,
    by omega, ?_, hout, ?_, hforeign⟩
  · exact htrow
  · rw [show trow + tw = tw + trow by omega,
      Function.iterate_add_apply, hrowrun]
    exact hwriter
  · rw [hout]
    exact SourceCSPRejectFormula.bits_not_language

end EthInapproximability.CurrentPaper.SourceCSPGlobalPositiveRows


