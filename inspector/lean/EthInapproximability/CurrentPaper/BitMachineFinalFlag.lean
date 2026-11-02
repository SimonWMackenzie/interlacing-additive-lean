import EthInapproximability.CurrentPaper.BitMachineSubroutine

/-!
# Returning one finite terminal-control bit

Source: frozen v8 `05-iteration.tex`, bounded cutoff runs, and
`06-eth.tex`, deterministic bit-machine convention. This finite compiler
adds a single instruction after a source machine halts. It pushes the chosen
Boolean function of the terminal finite control onto the actual output stack.
No source stack, running-time bound, or halting decision is provided for free.
-/

namespace EthInapproximability.CurrentPaper.BitMachineFinalFlag

open Turing Turing.TM2.Stmt
open BitMachine BitMachineEncoding BitMachineComposition BitMachineSubroutine

variable (M : Machine) (flag : Fin M.controlCount → Bool)

abbrev Stack := Fin M.stackCount ⊕ Unit
abbrev Label := Fin M.labelCount ⊕ Unit
abbrev Control := Fin M.controlCount × Unit
abbrev Config := TM2.Cfg (fun _ : Stack M => Bool) (Label M) (Control M)

def program : Label M → TM2.Stmt (fun _ : Stack M => Bool) (Label M) (Control M)
  | .inl l => liftStmt (some ()) (M.program l)
  | .inr () => push (.inl M.output) (fun v => flag v.1) halt

def embed (c : M.Config) : Config M := liftCfg (some ()) () (fun _ => []) c

def finished (c : M.Config) : Config M :=
  ⟨none, (c.var, ()), Sum.elim
    (Function.update c.stk M.output (flag c.var :: c.stk M.output)) (fun _ => [])⟩

theorem finish_step (c : M.Config) (hc : c.l = none) :
    advance (program M flag) (embed M c) = finished M flag c := by
  rcases c with ⟨l, v, S⟩
  change l = none at hc
  subst l
  simp [advance, program, embed, liftCfg, finished, TM2.step, TM2.stepAux, sum_update,
    -Sum.elim_update_left]

theorem run_finish (c : M.Config) (bound : ℕ) (hc : (M.run bound c).l = none) :
    ∃ t ≤ bound + 1,
      ((advance (program M flag))^[t]) (embed M c) = finished M flag (M.run bound c) := by
  obtain ⟨n, hn, heq⟩ := lift_outputs M.program (program M flag) (some ())
    (fun _ => rfl) () (fun _ => []) c bound hc
  change ((advance (program M flag))^[n]) (embed M c) = embed M (M.run bound c) at heq
  refine ⟨n + 1, by omega, ?_⟩
  rw [Function.iterate_succ_apply', heq]
  exact finish_step M flag _ hc

noncomputable def machine : Machine :=
  ofFinite (.inl M.input) (.inl M.output) (.inl M.start)
    (M.initial, ()) (program M flag)

noncomputable def encode (c : Config M) : (machine M flag).Config :=
  renameCfg (Fintype.equivFin (Stack M)) (Fintype.equivFin (Label M))
    (Fintype.equivFin (Control M)) c

theorem machine_init (input : List Bool) :
    (machine M flag).init input = encode M flag (embed M (M.init input)) := by
  have hi := ofFinite_init (.inl M.input : Stack M) (.inl M.output)
    (.inl M.start : Label M) (M.initial, ()) (program M flag) input
  change (machine M flag).init input = _ at hi
  rw [hi]
  unfold encode
  congr 1
  unfold embed liftCfg rawInit Machine.init
  congr 1
  funext k
  rcases k with k | k <;> simp

theorem machine_run (c : Config M) (n : ℕ) :
    (machine M flag).run n (encode M flag c) =
      encode M flag (((advance (program M flag))^[n]) c) :=
  ofFinite_run _ _ _ _ _ c n

/-- The extra output bit costs one actual transition after the original
computation; the source's stated bound may exceed its first halting time. -/
theorem outputs (input : List Bool) (bound : ℕ)
    (hc : (M.run bound (M.init input)).l = none) :
    (machine M flag).OutputsWithin input
      (flag (M.run bound (M.init input)).var ::
        (M.run bound (M.init input)).stk M.output) (bound + 1) := by
  obtain ⟨t, ht, heq⟩ := run_finish M flag (M.init input) bound hc
  refine ⟨t, ht, ?_, ?_⟩ <;> rw [machine_init, machine_run, heq]
  · rfl
  · simp only [encode, renameCfg, finished, machine, ofFinite]
    exact (congrArg (Sum.elim
      (Function.update (M.run bound (M.init input)).stk M.output
        (flag (M.run bound (M.init input)).var :: (M.run bound (M.init input)).stk M.output))
      (fun _ : Unit => []))
      ((Fintype.equivFin (Stack M)).symm_apply_apply (.inl M.output))).trans
        (Function.update_self _ _ _)

end EthInapproximability.CurrentPaper.BitMachineFinalFlag
