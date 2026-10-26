import EthInapproximability.CurrentPaper.BitMachineSubroutine

/-!
# Framed stack subroutines under finite renaming

Source: fixed bit-machine implementation in frozen v8 `06-eth.tex` and
`B-effectivity-details.tex`. The ambient controller need only match the
renamed local statements at the corresponding labels. Foreign state is
preserved and no simulation transition is added by relabelling.
-/

namespace EthInapproximability.CurrentPaper.BitMachineSubroutineRenaming

open Turing
open BitMachineEncoding BitMachineComposition BitMachineSubroutine

variable {K J L I V W K' L' V' : Type*}
  [DecidableEq K] [DecidableEq J] [DecidableEq K']

theorem lift_step_renamed
    (ek : K ⊕ J ≃ K') (el : L ⊕ I ≃ L') (ev : V × W ≃ V')
    (P : L → TM2.Stmt (fun _ : K => Bool) L V)
    (Q : L' → TM2.Stmt (fun _ : K' => Bool) L' V')
    (halt : Option I)
    (hQ : ∀ l, Q (el (.inl l)) = renameStmt ek el ev (liftStmt halt (P l)))
    (w : W) (T : J → List Bool) (c : TM2.Cfg (fun _ : K => Bool) L V)
    (hc : c.l ≠ none) :
    advance Q (renameCfg ek el ev (liftCfg halt w T c)) =
      renameCfg ek el ev (liftCfg halt w T (advance P c)) := by
  rcases c with ⟨l, v, S⟩
  cases l with
  | none => exact (hc rfl).elim
  | some l =>
      have hs := rename_stepAux ek el ev (liftStmt halt (P l)) (v, w) (Sum.elim S T)
      rw [lift_stepAux] at hs
      simpa only [advance, renameCfg, liftCfg, Option.map_some, TM2.step,
        hQ, Option.getD_some] using hs

theorem lift_run_until_renamed
    (ek : K ⊕ J ≃ K') (el : L ⊕ I ≃ L') (ev : V × W ≃ V')
    (P : L → TM2.Stmt (fun _ : K => Bool) L V)
    (Q : L' → TM2.Stmt (fun _ : K' => Bool) L' V')
    (halt : Option I)
    (hQ : ∀ l, Q (el (.inl l)) = renameStmt ek el ev (liftStmt halt (P l)))
    (w : W) (T : J → List Bool) (c : TM2.Cfg (fun _ : K => Bool) L V)
    (n : ℕ) (h : ∀ k < n, (((advance P)^[k]) c).l ≠ none) :
    ((advance Q)^[n]) (renameCfg ek el ev (liftCfg halt w T c)) =
      renameCfg ek el ev (liftCfg halt w T (((advance P)^[n]) c)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih (fun k hk => h k (by omega)),
        lift_step_renamed ek el ev P Q halt hQ w T _ (h n (by omega)),
        Function.iterate_succ_apply']

/-- The controller executes the exact local terminal computation, with
arbitrary finite coordinate/control renaming and unchanged foreign banks. -/
theorem lift_outputs_renamed
    (ek : K ⊕ J ≃ K') (el : L ⊕ I ≃ L') (ev : V × W ≃ V')
    (P : L → TM2.Stmt (fun _ : K => Bool) L V)
    (Q : L' → TM2.Stmt (fun _ : K' => Bool) L' V')
    (halt : Option I)
    (hQ : ∀ l, Q (el (.inl l)) = renameStmt ek el ev (liftStmt halt (P l)))
    (w : W) (T : J → List Bool) (c : TM2.Cfg (fun _ : K => Bool) L V)
    (bound : ℕ) (hhalt : (((advance P)^[bound]) c).l = none) :
    ∃ n ≤ bound, ((advance Q)^[n]) (renameCfg ek el ev (liftCfg halt w T c)) =
      renameCfg ek el ev (liftCfg halt w T (((advance P)^[bound]) c)) := by
  obtain ⟨n, hn, _, heq, hfirst⟩ := first_halt_cfg P c bound hhalt
  refine ⟨n, hn, ?_⟩
  rw [lift_run_until_renamed ek el ev P Q halt hQ w T c n hfirst, heq]

end EthInapproximability.CurrentPaper.BitMachineSubroutineRenaming
