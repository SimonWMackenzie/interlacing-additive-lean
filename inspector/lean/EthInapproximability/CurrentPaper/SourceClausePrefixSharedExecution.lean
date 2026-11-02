import EthInapproximability.CurrentPaper.SourceClausePrefixSharedClear

/-!
Exact transition-preserving embedding of a terminating local clause routine into
the common prefix bank. This changes stack addresses only; it does not prepare
inputs, clear scratch, or compute source-dependent data.
-/

namespace EthInapproximability.CurrentPaper.SourceBooleanPrefix.PrefixSharedExecution

open Turing BitMachineEncoding BitMachineStackEmbedding
open scoped Classical

variable {K L V : Type*} [DecidableEq K] [DecidableEq PrefixSharedCore.Stack]

noncomputable def liftedProgram (ι : K ↪ PrefixSharedCore.Stack)
    (P : L → TM2.Stmt (fun _ : K => Bool) L V) :
    L → TM2.Stmt (fun _ : PrefixSharedCore.Stack => Bool) L V :=
  fun l => stmt ι id id id none (P l)

theorem lifted_run (ι : K ↪ PrefixSharedCore.Stack)
    (foreign : PrefixSharedCore.Stack → List Bool)
    (P : L → TM2.Stmt (fun _ : K => Bool) L V)
    (start finish : TM2.Cfg (fun _ : K => Bool) L V)
    (bound : ℕ)
    (hrun : ((advance P)^[bound]) start = finish)
    (hhalt : finish.l = none) :
    ∃ t ≤ bound,
      ((advance (liftedProgram ι P))^[t])
        (stackCfg ι foreign start) = stackCfg ι foreign finish := by
  have hh : (((advance P)^[bound]) start).l = none := by
    rw [hrun]
    exact hhalt
  obtain ⟨t, ht, he⟩ := outputs ι foreign id id id (fun _ => rfl)
    none P (liftedProgram ι P) (by intro l; rfl) start bound hh
  refine ⟨t, ht, ?_⟩
  have cfg_id (c : TM2.Cfg (fun _ : K => Bool) L V) :
      cfg ι foreign id id none c = stackCfg ι foreign c := by
    rcases c with ⟨l, v, S⟩
    cases l <;> rfl
  rw [cfg_id, cfg_id, hrun] at he
  exact he

end EthInapproximability.CurrentPaper.SourceBooleanPrefix.PrefixSharedExecution
