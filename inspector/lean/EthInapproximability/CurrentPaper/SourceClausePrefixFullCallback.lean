import EthInapproximability.CurrentPaper.SourceClausePrefixThreeCycles

namespace EthInapproximability.CurrentPaper.SourceBooleanPrefix.PrefixFullCallback

open Turing BitMachineEncoding BitMachineStackEmbedding
open SourceBooleanEncoding SourceClauseEncoding EncodedCNF
open scoped Classical

noncomputable def terminalCost (n v w : ℕ)
    (saved output count : List Bool) : ℕ :=
  (SourceClauseFixedBatch.costPrefix
      (PrefixUnitClean.constantSize w 2) 3 + 1) +
    PrefixUnitRun.cost n v w 2 + 1 +
    PrefixSharedClear.cost
      (bank PrefixSharedCore.unitEmbedding
        (PrefixGateReady.blank n v saved output count)
        (PrefixUnitRun.finished n v w 2 true saved output count)) + 1

noncomputable def cost {n q : ℕ} (v : Fin n)
    (saved output count : List Bool) : ℕ :=
  PrefixThreeCycles.cost (q := q) v saved output count +
    terminalCost n v.val (width 2 q + 1)
      (PrefixThreeCycles.thirdSaved (q := q) v saved)
      output (List.replicate 7 true ++ count) + 1

noncomputable def program (q : ℕ) :=
  BitMachineRawSequence.program
    (PrefixThreeCycles.program q)
    (PrefixUnitCycle.program (width 2 q + 1) 2 true)
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel
        (SourceClauseFixedBatch.labelAt
          (PrefixUnitClean.constantSize (width 2 q + 1) 2) 0)))
    ((PrefixFirstTwoCycles.unitControl,
        PrefixFirstTwoCycles.gateControl),
      PrefixFirstTwoCycles.gateControl)
    PrefixFirstTwoCycles.unitControl

/-- One fixed-control physical at-least callback. The initial core is supplied;
the variable-length vertex loop is a separate machine. -/
theorem run {n q : ℕ} (v : Fin n)
    (saved output count : List Bool) :
    ∃ t ≤ cost (q := q) v saved output count,
      ((advance (program q))^[t])
        (⟨some (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel
              (BitMachineRawSequence.leftLabel
                (BitMachineRawSequence.leftLabel
                  (BitMachineRawSequence.leftLabel
                    (SourceClauseFixedBatch.labelAt
                      (PrefixUnitClean.constantSize (width 2 q + 1) 0) 0)))))),
          (((PrefixFirstTwoCycles.unitControl,
            PrefixFirstTwoCycles.gateControl),
            PrefixFirstTwoCycles.gateControl),
            PrefixFirstTwoCycles.unitControl),
          PrefixGateReady.blank n v.val saved output count⟩) =
        ⟨none, (((PrefixFirstTwoCycles.unitControl,
          PrefixFirstTwoCycles.gateControl),
          PrefixFirstTwoCycles.gateControl),
          PrefixFirstTwoCycles.unitControl),
          PrefixGateReady.blank n v.val
            ((clauseFields (chain (base n q (atLeastOrdinal v))
              (atLeastPayload v))).reverse ++ saved)
            output (List.replicate 8 true ++ count)⟩ := by
  let w := width 2 q + 1
  let s₃ := PrefixThreeCycles.thirdSaved (q := q) v saved
  let B := PrefixGateReady.blank n v.val saved output count
  let C := PrefixGateReady.blank n v.val s₃ output
    (List.replicate 7 true ++ count)
  let D := PrefixGateReady.blank n v.val
    ((clauseFields (chain (base n q (atLeastOrdinal v))
      (atLeastPayload v))).reverse ++ saved)
    output (List.replicate 8 true ++ count)
  obtain ⟨a, ha, hA⟩ := PrefixThreeCycles.run (q := q) v
    saved output count
  obtain ⟨b, hb, hB⟩ := PrefixUnitCycle.run n v.val w 2 true
    s₃ output (List.replicate 7 true ++ count)
  have hA' :
      ((advance (PrefixThreeCycles.program q))^[a])
        (⟨some (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel
              (BitMachineRawSequence.leftLabel
                (SourceClauseFixedBatch.labelAt
                  (PrefixUnitClean.constantSize w 0) 0))))),
          ((PrefixFirstTwoCycles.unitControl,
            PrefixFirstTwoCycles.gateControl),
            PrefixFirstTwoCycles.gateControl), B⟩) =
        ⟨none, ((PrefixFirstTwoCycles.unitControl,
          PrefixFirstTwoCycles.gateControl),
          PrefixFirstTwoCycles.gateControl), C⟩ := hA
  have hB' :
      ((advance (PrefixUnitCycle.program w 2 true))^[b])
        (⟨some (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel
            (SourceClauseFixedBatch.labelAt
              (PrefixUnitClean.constantSize w 2) 0))),
          PrefixFirstTwoCycles.unitControl, C⟩) =
        ⟨none, PrefixFirstTwoCycles.unitControl, D⟩ := by
    rw [show D = PrefixGateReady.blank n v.val
      (PrefixSharedUnitHandoff.nextSaved n v.val w 2 true s₃)
      output (true :: (List.replicate 7 true ++ count)) from ?_]
    · simpa only [PrefixFirstTwoCycles.unitControl, C] using hB
    · dsimp only [D, s₃, w]
      rw [← PrefixSourceIdentity.savedAfter_eq_chain (q := q) v saved]
      rfl
  obtain ⟨t, ht, h⟩ := BitMachineRawSequence.runs
    (PrefixThreeCycles.program q)
    (PrefixUnitCycle.program w 2 true)
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel
            (SourceClauseFixedBatch.labelAt
              (PrefixUnitClean.constantSize w 0) 0)))))
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel
        (SourceClauseFixedBatch.labelAt
          (PrefixUnitClean.constantSize w 2) 0)))
    ((PrefixFirstTwoCycles.unitControl,
        PrefixFirstTwoCycles.gateControl),
      PrefixFirstTwoCycles.gateControl)
    ((PrefixFirstTwoCycles.unitControl,
        PrefixFirstTwoCycles.gateControl),
      PrefixFirstTwoCycles.gateControl)
    PrefixFirstTwoCycles.unitControl PrefixFirstTwoCycles.unitControl
    B C D a b hA' hB'
  refine ⟨t, ?_, ?_⟩
  · change a ≤ PrefixThreeCycles.cost (q := q) v saved output count at ha
    change b ≤ terminalCost n v.val w s₃ output
      (List.replicate 7 true ++ count) at hb
    change t ≤ PrefixThreeCycles.cost (q := q) v saved output count +
      terminalCost n v.val w s₃ output
        (List.replicate 7 true ++ count) + 1
    omega
  · simpa only [program, w, B, D] using h

end EthInapproximability.CurrentPaper.SourceBooleanPrefix.PrefixFullCallback

#print axioms EthInapproximability.CurrentPaper.SourceBooleanPrefix.PrefixFullCallback.run
