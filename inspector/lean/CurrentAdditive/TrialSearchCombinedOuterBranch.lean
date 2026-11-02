import CurrentAdditive.TrialSearchCombinedCallback

/-! Reuse any checked controller branch as a run of the shared physical TM2. -/

namespace CurrentAdditive.FieldMachineHelper.TrialSearchCombinedOuterBranch

open CurrentAdditive.FieldMachineHelper.TrialSearchCombinedMachine
open CurrentAdditive.FieldMachineHelper.TrialSearchCombinedOuterLift
open CurrentAdditive.FieldMachineHelper.TrialSearchCombinedRun
open CurrentAdditive.FieldMachineHelper.TrialSearchCombinedSimulation (carriedLabel)

namespace Outer
export CurrentAdditive.FieldMachineHelper.TrialSearchControllerMachine
  (Label Config program run)
end Outer

theorem combined_controller_to_boundary
    (base : Registers) (S : Fin 12 → List Bool)
    (start target : Outer.Label) (n : Nat)
    (hlocal :
      (Outer.run n ⟨some start, base.outer, S⟩).l = some target)
    (hboundary : boundary target) :
    let c := Outer.run n ⟨some start, base.outer, S⟩
    let g := run n ⟨some (.outer start), base, S⟩
    g.l = some (.outer target) ∧
    g.var.outer = c.var ∧
    (∀ i : Fin 12, g.stk i = c.stk i) := by
  have hrel := outer_run_to_boundary base S start n
    ⟨target, hlocal, hboundary⟩
  rcases hrel with ⟨hl, hv, hs, _⟩
  refine ⟨?_, ?_, hs⟩
  · simpa [hlocal, carriedLabel] using hl
  · simpa [hlocal] using congrArg Registers.outer hv

#print axioms combined_controller_to_boundary

end CurrentAdditive.FieldMachineHelper.TrialSearchCombinedOuterBranch
