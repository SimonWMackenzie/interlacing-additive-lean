import CurrentAdditive.RoundedCodeTicketStep
import CurrentAdditive.RoundedCodeBitStep
import CurrentAdditive.RoundedCodeBranchStep
import CurrentAdditive.RoundedCodeDoneStep

/-! One fixed finite controller repeats the checked rounded source step.
The sole continuation tests the finite done flag; it never inspects or
silently resets a stack. Each re-entry uses the complete canonical bank
proved by the source-step theorem. -/

namespace EthInapproximability.CurrentPaper.RoundedCodeLoop

open Turing Turing.TM2.Stmt BitMachineEncoding
open Paper2.GeneratorCode
noncomputable section
set_option linter.unusedSimpArgs false

abbrev Stack := RoundedCodeStep.Stack
abbrev Control := RoundedCodeStep.Control
abbrev Label := RoundedCodeStep.Label ⊕ Unit
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

def entry : RoundedCodeStep.Label :=
  (RoundedCodeStep.start ⟨[], []⟩ [] 0).l.get (by rfl)

def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .inl l => BitMachineInline.stmt Sum.inl id id (some (.inr ()))
      (RoundedCodeStep.program l)
  | .inr _ => branch (fun v => v.1.2.2) halt
      (load (fun _ => RoundedCodeStep.initial) (goto (fun _ => .inl entry)))

def run (t : ℕ) (c : Config) : Config := ((advance program)^[t]) c

def frame (c : RoundedCodeStep.Config) : Config :=
  BitMachineInline.cfg Sum.inl id (some (.inr ())) c

def start (s : State) (tape : List Bool) (b : ℕ) : Config :=
  frame (RoundedCodeStep.start s tape b)

theorem join_run {c d : Config} {u : ℕ} (h : run u c = d) (v : ℕ) :
    run (u + v) c = run v d := by
  rw [Nat.add_comm u v]
  simp only [run, Function.iterate_add_apply] at h ⊢
  rw [h]

theorem step_to_route (c : RoundedCodeStep.Config) (t : ℕ)
    (done : Bool) (S : Stack → List Bool)
    (hr : RoundedCodeStep.run t c = ⟨none, RoundedCodeStep.finalControl done, S⟩) :
    ∃ u ≤ t, run u (frame c) =
      ⟨some (.inr ()), RoundedCodeStep.finalControl done, S⟩ := by
  have hh : (((advance RoundedCodeStep.program)^[t]) c).l = none := by
    change (RoundedCodeStep.run t c).l = none
    rw [hr]
  obtain ⟨u, hu, hur⟩ := BitMachineInline.outputs Sum.inl id id (by intro v; rfl)
    (some (.inr ())) RoundedCodeStep.program program (by intro l; rfl) c t hh
  change run u (frame c) = BitMachineInline.cfg Sum.inl id (some (.inr ()))
    (RoundedCodeStep.run t c) at hur
  rw [hr] at hur
  exact ⟨u, hu, by simpa [BitMachineInline.cfg] using hur⟩

theorem route_again (s : State) (tape : List Bool) (b : ℕ) :
    run 1 ⟨some (.inr ()), RoundedCodeStep.finalControl false,
      (RoundedCodeAdmin.start s tape b).stk⟩ = start s tape b := by
  simp [run, BitMachineEncoding.advance, TM2.step, TM2.stepAux, program, start, frame,
    BitMachineInline.cfg, RoundedCodeStep.finalControl, RoundedCodeStep.initial,
    RoundedCodeStep.start, RoundedCodeStep.adminCfg, RoundedCodeAdmin.start,
    BitMachineStackEmbedding.cfg, BitMachineStackEmbedding.stackCfg, entry,
    Paper2.CodeAdminNormalization.stateCfg, Paper2.CodeAdminMachine.ready,
    Paper2.CodeAdminMachine.cfg, RoundedCodeStep.adminLift,
    RoundedCodeAdmin.initial, RoundedCodeAdmin.adminInitial]

theorem route_stop (S : Stack → List Bool) :
    run 1 ⟨some (.inr ()), RoundedCodeStep.finalControl true, S⟩ =
      ⟨none, RoundedCodeStep.finalControl true, S⟩ := by
  simp [run, BitMachineEncoding.advance, TM2.step, TM2.stepAux, program, RoundedCodeStep.finalControl]

theorem source_again (s next : State) (tape suffix : List Bool) (b bound : ℕ)
    (hs : ∃ t ≤ bound, RoundedCodeStep.run t (RoundedCodeStep.start s tape b) =
      ⟨none, RoundedCodeStep.finalControl false, (RoundedCodeAdmin.start next suffix b).stk⟩) :
    ∃ t ≤ bound + 1, run t (start s tape b) = start next suffix b := by
  obtain ⟨t, ht, hr⟩ := hs
  obtain ⟨u, hu, hur⟩ := step_to_route _ t false _ hr
  exact ⟨u + 1, by omega, (join_run hur 1).trans (route_again next suffix b)⟩

theorem source_stop (s : State) (out tape : List Bool) (b bound : ℕ)
    (hs : ∃ t ≤ bound, RoundedCodeStep.run t (RoundedCodeStep.start s tape b) =
      ⟨none, RoundedCodeStep.finalControl true, (RoundedCodeAdmin.start ⟨[], out⟩ tape b).stk⟩) :
    ∃ t ≤ bound + 1, run t (start s tape b) =
      ⟨none, RoundedCodeStep.finalControl true, (RoundedCodeAdmin.start ⟨[], out⟩ tape b).stk⟩ := by
  obtain ⟨t, ht, hr⟩ := hs
  obtain ⟨u, hu, hur⟩ := step_to_route _ t true _ hr
  exact ⟨u + 1, by omega, (join_run hur 1).trans (route_stop _)⟩

#print axioms route_again
#print axioms source_again

end
end EthInapproximability.CurrentPaper.RoundedCodeLoop
