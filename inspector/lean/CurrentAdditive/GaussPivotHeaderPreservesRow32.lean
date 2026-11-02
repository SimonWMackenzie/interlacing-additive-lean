import CurrentAdditive.GaussStepPivotHeaderExactRun32

/-! The V2 count-header stage reads the unary row cursor on bank 5 but
restores it. The final Bank4 assembler still needs that cursor. -/

namespace CurrentAdditive.GaussPivotHeaderPreservesRow32

noncomputable section

open EthInapproximability.CurrentPaper
open CurrentAdditive.GaussStepFields32

private noncomputable abbrev W :=
  SourceListMachineWriter.framingMachine false

theorem result5 (unary : List Bool) (S : Stack → List Bool)
    (c : W.Config) :
    (GaussStepPivotHeaderExactRun32.result unary S c).stk 5 = unary := by
  change SourceClausePreservingBroadcast.result
    GaussPivotHeader32.outputSlot 31 [30]
    (SourceListMachineWriter.result false unary)
    (GaussPivotHeaderExact32.workerResult unary S c) 5 = unary
  rw [SourceClausePreservingBroadcast.other_preserved
    GaussPivotHeader32.outputSlot 31 [30]
    (SourceListMachineWriter.result false unary)
    (GaussPivotHeaderExact32.workerResult unary S c) 5
    (by decide) (by decide) (by decide)]
  change (BitMachineStackEmbedding.bank GaussPivotFraming32.locate
    (GaussPivotHeader32.afterIn unary S) c.stk) 5 = unary
  rw [BitMachineStackEmbedding.bank_outside
    GaussPivotFraming32.locate _ _ 5 (by
      rintro ⟨q,hq⟩
      have hv := congrArg Fin.val hq
      have hq' : q.val < 8 := by
        simpa only [show W.stackCount = 8 by rfl] using q.isLt
      simp [GaussPivotFraming32.locate] at hv)]
  exact SourceClausePreservingBroadcast.source_restored
    (5 : Stack) 31 [GaussPivotHeader32.inputSlot]
    (by decide) unary S

#print axioms result5

end
end CurrentAdditive.GaussPivotHeaderPreservesRow32
