import EthInapproximability.CurrentPaper.BitMachineStackEmbedding

/-!
# Exact runs under a pure stack-location embedding

Source: frozen v8 `B-effectivity-details.tex` and `06-eth.tex`. This special
case changes neither labels nor finite control and preserves halting. It can
therefore transport a complete bounded run, including idle steps after halt,
without a first-halting-time witness.
-/

namespace EthInapproximability.CurrentPaper.BitMachineStackRun

open Turing BitMachineEncoding BitMachineStackEmbedding

variable {K J L V : Type*} [DecidableEq K] [DecidableEq J]

theorem step (ι : K ↪ J) (foreign : J → List Bool)
    (P : L → TM2.Stmt (fun _ : K => Bool) L V)
    (c : TM2.Cfg (fun _ : K => Bool) L V) :
    advance (fun l => stackStmt ι (P l)) (stackCfg ι foreign c) =
      stackCfg ι foreign (advance P c) := by
  rcases c with ⟨l, v, S⟩
  cases l with
  | none => rfl
  | some l =>
      simpa only [advance, stackCfg, TM2.step, Option.getD_some] using
        stack_stepAux ι foreign (P l) v S

theorem run (ι : K ↪ J) (foreign : J → List Bool)
    (P : L → TM2.Stmt (fun _ : K => Bool) L V)
    (c : TM2.Cfg (fun _ : K => Bool) L V) (t : ℕ) :
    ((advance (fun l => stackStmt ι (P l)))^[t]) (stackCfg ι foreign c) =
      stackCfg ι foreign (((advance P)^[t]) c) := by
  induction t with
  | zero => rfl
  | succ t ih =>
      rw [Function.iterate_succ_apply', ih, step, Function.iterate_succ_apply']

end EthInapproximability.CurrentPaper.BitMachineStackRun
