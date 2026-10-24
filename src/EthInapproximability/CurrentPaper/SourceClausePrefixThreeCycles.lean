import EthInapproximability.CurrentPaper.SourceClausePrefixFirstTwoCycles

namespace EthInapproximability.CurrentPaper.SourceBooleanPrefix.PrefixThreeCycles

open Turing BitMachineEncoding BitMachineStackEmbedding
open SourceBooleanEncoding
open scoped Classical

def thirdSaved {n q : ℕ} (v : Fin n) (saved : List Bool) : List Bool :=
  PrefixSharedGateHandoff.nextSaved (q := q) v (1 : Fin 2)
    (PrefixFirstTwoCycles.secondSaved (q := q) v saved)

noncomputable def cost {n q : ℕ} (v : Fin n)
    (saved output count : List Bool) : ℕ :=
  PrefixFirstTwoCycles.unitCost n v.val (width 2 q + 1)
      saved output count +
    PrefixFirstTwoCycles.gateCost (q := q) v (0 : Fin 2)
      (PrefixFirstTwoCycles.firstSaved n v.val (width 2 q + 1) saved)
      output (true :: count) + 1 +
    PrefixFirstTwoCycles.gateCost (q := q) v (1 : Fin 2)
      (PrefixFirstTwoCycles.secondSaved (q := q) v saved)
      output (List.replicate 4 true ++ count) + 1

noncomputable def program (q : ℕ) :=
  BitMachineRawSequence.program
    (PrefixFirstTwoCycles.program q)
    (PrefixGateCycle.program 1 (width 2 q + 1))
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel
          (SourceClauseFixedBatch.labelAt
            (PrefixGateOperands.constantSize 1 (width 2 q + 1)) 0))))
    (PrefixFirstTwoCycles.unitControl, PrefixFirstTwoCycles.gateControl)
    PrefixFirstTwoCycles.gateControl

theorem run {n q : ℕ} (v : Fin n)
    (saved output count : List Bool) :
    ∃ t ≤ cost (q := q) v saved output count,
      ((advance (program q))^[t])
        (⟨some (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel
              (BitMachineRawSequence.leftLabel
                (BitMachineRawSequence.leftLabel
                  (SourceClauseFixedBatch.labelAt
                    (PrefixUnitClean.constantSize (width 2 q + 1) 0) 0))))),
          ((PrefixFirstTwoCycles.unitControl,
            PrefixFirstTwoCycles.gateControl),
            PrefixFirstTwoCycles.gateControl),
          PrefixGateReady.blank n v.val saved output count⟩) =
        ⟨none, ((PrefixFirstTwoCycles.unitControl,
          PrefixFirstTwoCycles.gateControl),
          PrefixFirstTwoCycles.gateControl),
          PrefixGateReady.blank n v.val (thirdSaved (q := q) v saved)
            output (List.replicate 7 true ++ count)⟩ := by
  let w := width 2 q + 1
  let s₂ := PrefixFirstTwoCycles.secondSaved (q := q) v saved
  let B := PrefixGateReady.blank n v.val saved output count
  let C := PrefixGateReady.blank n v.val s₂ output
    (List.replicate 4 true ++ count)
  let D := PrefixGateReady.blank n v.val
    (thirdSaved (q := q) v saved) output
    (List.replicate 7 true ++ count)
  obtain ⟨a, ha, hA⟩ := PrefixFirstTwoCycles.run (q := q) v
    saved output count
  obtain ⟨b, hb, hB⟩ := PrefixGateCycle.run (q := q) v (1 : Fin 2)
    s₂ output (List.replicate 4 true ++ count)
  have hA' :
      ((advance (PrefixFirstTwoCycles.program q))^[a])
        (⟨some (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel
              (SourceClauseFixedBatch.labelAt
                (PrefixUnitClean.constantSize w 0) 0)))),
          (PrefixFirstTwoCycles.unitControl,
            PrefixFirstTwoCycles.gateControl), B⟩) =
        ⟨none, (PrefixFirstTwoCycles.unitControl,
          PrefixFirstTwoCycles.gateControl), C⟩ := hA
  have hB' :
      ((advance (PrefixGateCycle.program 1 w))^[b])
        (⟨some (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel
              (SourceClauseFixedBatch.labelAt
                (PrefixGateOperands.constantSize 1 w) 0)))),
          PrefixFirstTwoCycles.gateControl, C⟩) =
        ⟨none, PrefixFirstTwoCycles.gateControl, D⟩ := by
    simpa only [PrefixFirstTwoCycles.gateControl, C, D, s₂,
      thirdSaved, List.replicate, List.cons_append,
      List.nil_append] using hB
  obtain ⟨t, ht, h⟩ := BitMachineRawSequence.runs
    (PrefixFirstTwoCycles.program q)
    (PrefixGateCycle.program 1 w)
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel
          (SourceClauseFixedBatch.labelAt
            (PrefixUnitClean.constantSize w 0) 0))))
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel
          (SourceClauseFixedBatch.labelAt
            (PrefixGateOperands.constantSize 1 w) 0))))
    (PrefixFirstTwoCycles.unitControl, PrefixFirstTwoCycles.gateControl)
    (PrefixFirstTwoCycles.unitControl, PrefixFirstTwoCycles.gateControl)
    PrefixFirstTwoCycles.gateControl PrefixFirstTwoCycles.gateControl
    B C D a b hA' hB'
  refine ⟨t, ?_, ?_⟩
  · change a ≤ PrefixFirstTwoCycles.unitCost n v.val w
        saved output count +
      PrefixFirstTwoCycles.gateCost (q := q) v (0 : Fin 2)
        (PrefixFirstTwoCycles.firstSaved n v.val w saved)
        output (true :: count) + 1 at ha
    change b ≤ PrefixFirstTwoCycles.gateCost (q := q) v (1 : Fin 2)
      s₂ output (List.replicate 4 true ++ count) at hb
    change t ≤ PrefixFirstTwoCycles.unitCost n v.val w saved output count +
      PrefixFirstTwoCycles.gateCost (q := q) v (0 : Fin 2)
        (PrefixFirstTwoCycles.firstSaved n v.val w saved)
        output (true :: count) + 1 +
      PrefixFirstTwoCycles.gateCost (q := q) v (1 : Fin 2)
        s₂ output (List.replicate 4 true ++ count) + 1
    omega
  · simpa only [program, w, B, D] using h

end EthInapproximability.CurrentPaper.SourceBooleanPrefix.PrefixThreeCycles

#print axioms EthInapproximability.CurrentPaper.SourceBooleanPrefix.PrefixThreeCycles.run
