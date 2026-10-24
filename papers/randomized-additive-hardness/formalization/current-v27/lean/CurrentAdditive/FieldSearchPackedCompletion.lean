import CurrentAdditive.UnifiedTailFreeAdapter

/-! The real first-passing search supplies the missing search premise of the
same-program packed field-list printer, with a tail-independent initial bank. -/

namespace CurrentAdditive.FieldSearchCompletion

set_option maxHeartbeats 1000000

open CurrentAdditive.FieldMachineHelper.TrialSearchCombinedMachine
open CurrentAdditive.FiniteFieldConstructor.TrialSearch

namespace Unified
export CurrentAdditive.FiniteFieldMachine.UnifiedFieldListMachine
  (run packedBits)
end Unified

theorem physical_firstPassing_packed (d n : Nat) (hd : 0 < d) :
    ∃ c < 2 ^ d,
      firstPassing d = some (monicBits d c) ∧
      ∃ t ≤ 55 * 2 ^ d * 2 ^ (d / 2) * (d + 1) ^ 2 + 2 +
          CurrentAdditive.FiniteFieldMachine.FieldListOutputMachine.timeBound d c n,
        (Unified.run t (concreteTailFreeStart d n (initialConfig d))).l = none ∧
        (Unified.run t (concreteTailFreeStart d n (initialConfig d))).stk
          (CurrentAdditive.FiniteFieldMachine.FieldSearchPrinterHandoff.printerSlots
            CurrentAdditive.FiniteFieldMachine.FieldListOutputMachine.output) =
          Unified.packedBits d c n := by
  obtain ⟨c, hc, hfirst, steps, hsteps, hout⟩ :=
    physical_firstPassing_with_clock d hd
  let g := CurrentAdditive.FieldMachineHelper.TrialSearchCombinedMachine.run
    steps (initialConfig d)
  change g.l = _ ∧ _ at hout
  rcases hout with ⟨hl, hbank⟩
  have hsearch :
      ((EthInapproximability.CurrentPaper.BitMachineEncoding.advance
        CurrentAdditive.FieldMachineHelper.TrialSearchCombinedMachine.program)^[steps])
          (initialConfig d) =
        ⟨some (.outer .success), g.var, g.stk⟩ := by
    change g = _
    rcases g with ⟨l, r, S⟩
    change l = _ at hl
    cases hl
    rfl
  obtain ⟨t, ht, hprinted⟩ :=
    run_packed_after_tailFree_search
      d c n steps hc hd (initialConfig d) g.var g.stk hsearch hbank
  refine ⟨c, hc, hfirst, t, ?_, ?_⟩
  · omega
  · simpa only [tailFreeStart_eq_concrete] using hprinted

#print axioms physical_firstPassing_packed

end CurrentAdditive.FieldSearchCompletion
