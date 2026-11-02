import CurrentAdditive.GaussWholeStepNoPivot
import CurrentAdditive.GaussWholeStepPivot

namespace CurrentAdditive.GaussWholeStepCorrect
noncomputable section
set_option maxRecDepth 16384
set_option maxHeartbeats 6000000
set_option maxSynthPendingDepth 128
open EthInapproximability.CurrentPaper

/-- Correctness of one actual finite whole-step machine on every valid Gauss
state before the last column. It obtains every decision and matrix operand by
running the physical programs; no local-run or prepared-data premise remains.
This theorem asserts termination, not the final uniform polynomial clock. -/
theorem outputs_step {m k : Nat} (s : GaussControlTrace.State m k)
    (hc : s.c < k) (hcount : s.r=s.pivots.length) :
    ∃ T : Nat,GaussWholeStepProgram.machine.OutputsWithin (GaussControlTrace.statePacket s)
      (GaussControlTrace.statePacket (GaussControlTrace.step s)) T := by
  by_cases hr : s.r < m
  · cases hp : SequentialTotality.pivotTyped s.B s.r ⟨s.c,hc⟩ with
    | none => exact GaussWholeStepNoPivot.outputs_noPivot s hr hc hp
    | some pivot => exact GaussWholeStepPivot.outputs_pivot s hr hc pivot hp hcount
  · refine ⟨GaussWholeStepTerminal.terminalClock s,?_⟩
    simpa only [GaussControlTrace.step,hr,↓reduceDIte] using
      GaussWholeStepTerminal.terminal_outputs s hr

theorem outputs_actual_step {m k : Nat} (A : Fin m → Fin k → ℚ) (t : Nat) (ht : t < k) :
    ∃ T : Nat,GaussWholeStepProgram.machine.OutputsWithin
      (GaussControlTrace.statePacket (GaussControlTrace.after A t))
      (GaussControlTrace.statePacket (GaussControlTrace.after A (t+1))) T := by
  have hc := (GaussControlTrace.after_size A t).2.1
  obtain ⟨T,hT⟩ := outputs_step (GaussControlTrace.after A t) (by omega)
    (GaussControlTrace.after_pivotCount A t)
  refine ⟨T,?_⟩
  simpa only [GaussControlTrace.after,Function.iterate_succ_apply'] using hT

#print axioms outputs_step
#print axioms outputs_actual_step
end
end CurrentAdditive.GaussWholeStepCorrect
