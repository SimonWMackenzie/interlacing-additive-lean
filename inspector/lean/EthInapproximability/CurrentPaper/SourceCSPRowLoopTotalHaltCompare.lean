import EthInapproximability.CurrentPaper.SourceCSPRowLoopTotalRowResult

/-!
# Deterministic terminal-state comparison

Two proved executions of the same physical finite program may use different
upper-bound times. Once halted, the configuration is unchanged, so their
terminal configurations agree. This lets the all-input and exact-success
row theorems share one literal output bank without an assumed oracle result.
-/

namespace EthInapproximability.CurrentPaper.SourceCSPRowLoopTotalHaltCompare

open Turing BitMachineEncoding

theorem halted_unique {K L V : Type*} [DecidableEq K]
    (P : L → TM2.Stmt (fun _ : K => Bool) L V)
    (c : TM2.Cfg (fun _ : K => Bool) L V) (t u : Nat)
    (ht : (((advance P)^[t]) c).l = none)
    (hu : (((advance P)^[u]) c).l = none) :
    ((advance P)^[t]) c = ((advance P)^[u]) c := by
  rcases le_total t u with h | h
  · have he : u = t + (u - t) := by omega
    rw [he, show t + (u - t) = (u - t) + t by omega,
      Function.iterate_add_apply]
    exact (BitMachineSubroutine.run_halted P _ ht _).symm
  · have he : t = u + (t - u) := by omega
    rw [he, show u + (t - u) = (t - u) + u by omega,
      Function.iterate_add_apply]
    exact BitMachineSubroutine.run_halted P _ hu _

end EthInapproximability.CurrentPaper.SourceCSPRowLoopTotalHaltCompare
