import Paper2.SSSchedClock

/-! Lane owner:a-sched-space-1, WP-SCHED segment (3): the formalisable independence clauses of T44
(lock v12 P:65-66, "... and are independent of the base matrix, its communication complexity, and the intended
repetition count").

* The machine `SSSched.sched Δ γ` is a function of the machine constants `(Δ, γ)` only (its type takes no base
  matrix, protocol, optimum or repetition count `k`): structural, visible in its definition.
* Its whole run is a function of the literal bytes `encode g` only (`sched_bytes_only`): two graphs with the same
  byte string have identical runs at every time.
* The decided predicate `CompletePublicScheduleScratch.Checks (V := Fin n) (E := Fin m) L Δ γ` takes only
  `n, m, L = clog₂ n, Δ, γ`, and the printed values are the admitted functions of `n, m` (`sched_run`).  Together
  with `sched_bytes_only` this states the lock's independence: nothing about the base matrix, its complexity or `k`
  can enter, because none of them is an input. -/

namespace SSSchedIndep

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open Paper2
open SSSched

/-- The run of the schedule machine depends on the literal graph bytes only. -/
theorem sched_bytes_only (Δ : ℕ) (γ : ℚ) (g g' : EncodedGraph.Graph)
    (h : EncodedGraph.encode g = EncodedGraph.encode g') (T : ℕ) :
    ((advance (sched Δ γ))^[T])
        (⟨some (schedStart Δ γ), schedCtl Δ γ, Sum.elim (CountFront.G0 g) (fun _ => [])⟩ :
          TM2.Cfg (fun _ : KS => Bool) _ _) =
      ((advance (sched Δ γ))^[T])
        (⟨some (schedStart Δ γ), schedCtl Δ γ, Sum.elim (CountFront.G0 g') (fun _ => [])⟩ :
          TM2.Cfg (fun _ : KS => Bool) _ _) := by
  have e : CountFront.G0 g = CountFront.G0 g' := by
    unfold CountFront.G0; rw [h]
  rw [e]

end SSSchedIndep

#print axioms SSSchedIndep.sched_bytes_only
