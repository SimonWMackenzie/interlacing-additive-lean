import EthInapproximability.CurrentPaper.SourceCSPRejectWriterFrame

/-!
# Physical output routing after guarded CSP branch classification

The finite selector passes its outcome in control. Rejection clears the
former unary-count stack and writes the fixed canonical unsatisfiable CNF;
the zero-vertex/zero-row case writes the encoded empty CNF; a positive tag
halts here for a later cap-and-row-loop continuation. This router does not
itself classify source strings or claim positive output correctness.
-/

namespace EthInapproximability.CurrentPaper.SourceCSPGuardOutputRouter

open Turing BitMachineEncoding BitMachineInline

abbrev Stack := SourceCSPInputFrame.Stack

inductive Label where
  | route | rejectWriter (l : SourceCSPRejectWriter.Label)
  | zeroOne | zeroTwo | positive
  deriving DecidableEq, Fintype

abbrev Control := Option SourceCSPGuardDispatch.Outcome × Option Bool
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

def outputSlot : Stack := SourceCSPRejectWriterFrame.outputSlot

def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .route =>
      .branch (fun v => v.1 == some .reject)
        (.goto (fun _ => .rejectWriter .clear))
        (.branch (fun v => v.1 == some .zero)
          (.goto (fun _ => .zeroOne))
          (.goto (fun _ => .positive)))
  | .rejectWriter l =>
      stmt Label.rejectWriter
        (fun w => (some .reject, w)) Prod.snd none
        (SourceCSPRejectWriterFrame.program l)
  | .zeroOne =>
      .push outputSlot (fun _ => false) (.goto (fun _ => .zeroTwo))
  | .zeroTwo => .push outputSlot (fun _ => false) .halt
  | .positive => .halt

def run (t : Nat) (outcome : SourceCSPGuardDispatch.Outcome)
    (S : Stack → List Bool) : Config :=
  ((advance program)^[t])
    ⟨some .route, (some outcome, none), S⟩

theorem zero_run (S : Stack → List Bool)
    (houtput : S outputSlot = []) :
    run 3 .zero S =
      ⟨none, (some .zero, none),
        Function.update S outputSlot [false, false]⟩ := by
  have hr : (SourceCSPGuardDispatch.Outcome.zero ==
      SourceCSPGuardDispatch.Outcome.reject) = false := by decide
  change S SourceCSPRejectWriterFrame.outputSlot = [] at houtput
  simp [run, Function.iterate_succ_apply', advance, TM2.step,
    TM2.stepAux, program, outputSlot, houtput, hr]

theorem positive_run (S : Stack → List Bool) :
    run 2 .positive S = ⟨none, (some .positive, none), S⟩ := by
  have hr : (SourceCSPGuardDispatch.Outcome.positive ==
      SourceCSPGuardDispatch.Outcome.reject) = false := by decide
  have hz : (SourceCSPGuardDispatch.Outcome.positive ==
      SourceCSPGuardDispatch.Outcome.zero) = false := by decide
  simp [run, Function.iterate_succ_apply', advance, TM2.step,
    TM2.stepAux, program, hr, hz]

/-- A rejected raw source writes the literal fixed unsatisfiable formula.
The writer clears any count word left on the output slot first. -/
theorem reject_run (S : Stack → List Bool) :
    ∃ t T, t ≤ (S outputSlot).length + 4 ∧
      run t .reject S = ⟨none, (some .reject, none), T⟩ ∧
      T outputSlot = SourceCSPRejectFormula.bits ∧
      (∀ k : Stack, k ≠ outputSlot → T k = S k) := by
  obtain ⟨tw, Tw, htw, hrw, hout, hforeign⟩ :=
    SourceCSPRejectWriterFrame.reject_run S
  have hhalt : (((advance SourceCSPRejectWriterFrame.program)^[tw])
      (⟨some .clear, none, S⟩ :
        TM2.Cfg (fun _ : Stack => Bool)
          SourceCSPRejectWriter.Label (Option Bool))).l = none := by
    rw [hrw]
  obtain ⟨u, hu, hru⟩ := BitMachineInline.outputs
    Label.rejectWriter (fun w => (some .reject, w)) Prod.snd
    (fun _ => rfl) none SourceCSPRejectWriterFrame.program program
    (fun _ => rfl)
    (⟨some .clear, none, S⟩ :
      TM2.Cfg (fun _ : Stack => Bool)
        SourceCSPRejectWriter.Label (Option Bool)) tw hhalt
  rw [hrw] at hru
  have hroute : advance program
      (⟨some .route, (some .reject, none), S⟩ : Config) =
      ⟨some (.rejectWriter .clear), (some .reject, none), S⟩ := by
    simp [advance, TM2.step, TM2.stepAux, program]
  have htw' : tw ≤ (S outputSlot).length + 3 := htw
  refine ⟨u + 1, Tw, by omega, ?_, hout, hforeign⟩
  change ((advance program)^[u + 1]) _ = _
  rw [Function.iterate_succ_apply, hroute]
  simpa only [BitMachineInline.cfg, id_eq, Option.map_none] using hru

end EthInapproximability.CurrentPaper.SourceCSPGuardOutputRouter
