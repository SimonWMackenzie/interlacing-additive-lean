import CurrentAdditive.TrialSearchCombinedOuterBranch

/-! Exact output configuration for a physical controller branch. -/

namespace CurrentAdditive.FieldMachineHelper.TrialSearchCombinedOuterExact

open CurrentAdditive.FieldMachineHelper.TrialSearchCombinedMachine
open CurrentAdditive.FieldMachineHelper.TrialSearchCombinedOuterLift
open CurrentAdditive.FieldMachineHelper.TrialSearchCombinedRun
open CurrentAdditive.FieldMachineHelper.TrialSearchCombinedSimulation (carriedLabel)

namespace Outer
export CurrentAdditive.FieldMachineHelper.TrialSearchControllerMachine
  (Label Config program run)
end Outer

theorem combined_controller_exact
    (base : Registers) (S : Fin 12 → List Bool)
    (start target : Outer.Label) (n : Nat)
    (hlocal :
      (Outer.run n ⟨some start, base.outer, S⟩).l = some target)
    (hboundary : boundary target) :
    run n ⟨some (.outer start), base, S⟩ =
      ⟨some (.outer target),
        {base with outer :=
          (Outer.run n ⟨some start, base.outer, S⟩).var},
        (Outer.run n ⟨some start, base.outer, S⟩).stk⟩ := by
  have hrel := outer_run_to_boundary base S start n
    ⟨target, hlocal, hboundary⟩
  rcases hrel with ⟨hl, hv, hs, _⟩
  cases hg : run n ⟨some (.outer start), base, S⟩ with
  | mk gl gv gs =>
    have hl' : gl = some (.outer target) := by
      simpa [hg, hlocal, carriedLabel] using hl
    have hv' : gv = {base with outer :=
        (Outer.run n ⟨some start, base.outer, S⟩).var} := by
      simpa [hg, hlocal] using hv
    have hs' : gs = (Outer.run n ⟨some start, base.outer, S⟩).stk := by
      funext i
      simpa [hg] using hs i
    cases hl'
    cases hv'
    cases hs'
    rfl

#print axioms combined_controller_exact

end CurrentAdditive.FieldMachineHelper.TrialSearchCombinedOuterExact
