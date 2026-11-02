import EthInapproximability.CurrentPaper.BitMachineComposition

/-!
# Framed execution of concrete finite stack subroutines

Source: frozen v8 `06-eth.tex` and `B-effectivity-details.tex`, composition
of fixed bit-machine algorithms. These statements transport actual TM2
instruction execution. Foreign stacks and finite control are unchanged;
only the chosen halt continuation is substituted.
-/

namespace EthInapproximability.CurrentPaper.BitMachineSubroutine

open Turing
open BitMachineEncoding BitMachineComposition

variable {K J L I V W : Type*} [DecidableEq K] [DecidableEq J]

theorem advance_halted (P : L → TM2.Stmt (fun _ : K => Bool) L V)
    (c : TM2.Cfg (fun _ : K => Bool) L V) (hc : c.l = none) : advance P c = c := by
  rcases c with ⟨l, v, S⟩
  cases l with
  | none => rfl
  | some l => contradiction

theorem run_halted (P : L → TM2.Stmt (fun _ : K => Bool) L V)
    (c : TM2.Cfg (fun _ : K => Bool) L V) (hc : c.l = none) (n : ℕ) :
    ((advance P)^[n]) c = c := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ih, advance_halted P c hc]

theorem first_halt_cfg (P : L → TM2.Stmt (fun _ : K => Bool) L V)
    (c : TM2.Cfg (fun _ : K => Bool) L V) (bound : ℕ)
    (hhalt : (((advance P)^[bound]) c).l = none) :
    ∃ n ≤ bound, (((advance P)^[n]) c).l = none ∧
      ((advance P)^[n]) c = ((advance P)^[bound]) c ∧
      ∀ k < n, (((advance P)^[k]) c).l ≠ none := by
  classical
  have hex : ∃ n, (((advance P)^[n]) c).l = none := ⟨bound, hhalt⟩
  let n := Nat.find hex
  have hn : n ≤ bound := Nat.find_min' hex hhalt
  have hh : (((advance P)^[n]) c).l = none := Nat.find_spec hex
  refine ⟨n, hn, hh, ?_, fun k hk => Nat.find_min hex hk⟩
  conv_rhs => rw [← Nat.sub_add_cancel hn, Function.iterate_add_apply]
  rw [run_halted P _ hh]

theorem lift_step (P : L → TM2.Stmt (fun _ : K => Bool) L V)
    (Q : L ⊕ I → TM2.Stmt (fun _ : K ⊕ J => Bool) (L ⊕ I) (V × W))
    (halt : Option I) (hQ : ∀ l, Q (.inl l) = liftStmt halt (P l))
    (w : W) (T : J → List Bool) (c : TM2.Cfg (fun _ : K => Bool) L V)
    (hc : c.l ≠ none) :
    advance Q (liftCfg halt w T c) = liftCfg halt w T (advance P c) := by
  rcases c with ⟨l, v, S⟩
  cases l with
  | none => exact (hc rfl).elim
  | some l =>
      simpa only [advance, liftCfg, TM2.step, hQ, Option.getD_some] using
        lift_stepAux halt (P l) v w S T

/-- The local run is transported until its first halt, with no hidden
transition overhead and no change to any foreign stack. -/
theorem lift_run_until (P : L → TM2.Stmt (fun _ : K => Bool) L V)
    (Q : L ⊕ I → TM2.Stmt (fun _ : K ⊕ J => Bool) (L ⊕ I) (V × W))
    (halt : Option I) (hQ : ∀ l, Q (.inl l) = liftStmt halt (P l))
    (w : W) (T : J → List Bool) (c : TM2.Cfg (fun _ : K => Bool) L V)
    (n : ℕ) (h : ∀ k < n, (((advance P)^[k]) c).l ≠ none) :
    ((advance Q)^[n]) (liftCfg halt w T c) =
      liftCfg halt w T (((advance P)^[n]) c) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih (fun k hk => h k (by omega)),
        lift_step P Q halt hQ w T _ (h n (by omega)), Function.iterate_succ_apply']

/-- A bounded actual halting computation runs as a subroutine in at most
the same number of transitions, reaching exactly its terminal local state
with the selected continuation label and the unchanged foreign state.
The input witness need not name the first halting time. -/
theorem lift_outputs (P : L → TM2.Stmt (fun _ : K => Bool) L V)
    (Q : L ⊕ I → TM2.Stmt (fun _ : K ⊕ J => Bool) (L ⊕ I) (V × W))
    (halt : Option I) (hQ : ∀ l, Q (.inl l) = liftStmt halt (P l))
    (w : W) (T : J → List Bool) (c : TM2.Cfg (fun _ : K => Bool) L V)
    (bound : ℕ) (hhalt : (((advance P)^[bound]) c).l = none) :
    ∃ n ≤ bound, ((advance Q)^[n]) (liftCfg halt w T c) =
      liftCfg halt w T (((advance P)^[bound]) c) := by
  obtain ⟨n, hn, _, heq, hfirst⟩ := first_halt_cfg P c bound hhalt
  exact ⟨n, hn, (lift_run_until P Q halt hQ w T c n hfirst).trans (congrArg _ heq)⟩

end EthInapproximability.CurrentPaper.BitMachineSubroutine
