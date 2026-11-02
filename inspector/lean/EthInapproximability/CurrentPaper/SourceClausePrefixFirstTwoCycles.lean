import EthInapproximability.CurrentPaper.SourceClausePrefixSourceIdentity

namespace EthInapproximability.CurrentPaper.SourceBooleanPrefix.PrefixFirstTwoCycles

open Turing BitMachineEncoding BitMachineStackEmbedding
open SourceBooleanEncoding
open scoped Classical

noncomputable def unitControl :=
  (((), PrefixUnitRun.startControl), ((), (none : Option Bool)))

noncomputable def gateControl :=
  ((((), ((), (none : Option Bool))), PrefixGateCycle.gateControl),
    ((), (none : Option Bool)))

def firstSaved (n v w : ℕ) (saved : List Bool) : List Bool :=
  PrefixSharedUnitHandoff.nextSaved n v w 0 false saved

def secondSaved {n q : ℕ} (v : Fin n) (saved : List Bool) : List Bool :=
  PrefixSharedGateHandoff.nextSaved (q := q) v (0 : Fin 2)
    (firstSaved n v.val (width 2 q + 1) saved)

noncomputable def unitCost (n v w : ℕ)
    (saved output count : List Bool) : ℕ :=
  (SourceClauseFixedBatch.costPrefix
      (PrefixUnitClean.constantSize w 0) 3 + 1) +
    PrefixUnitRun.cost n v w 0 + 1 +
    PrefixSharedClear.cost
      (bank PrefixSharedCore.unitEmbedding
        (PrefixGateReady.blank n v saved output count)
        (PrefixUnitRun.finished n v w 0 false saved output count)) + 1

noncomputable def gateCost {n q : ℕ} (v : Fin n) (s : Fin 2)
    (saved output count : List Bool) : ℕ :=
  PrefixGateOperands.preparationCost s.val (width 2 q + 1)
      (List.replicate v.val true) +
    SourceClauseRowGate.cost v.val 2 s.val n s.val v.val
      (width 2 q + 1) true + 1 +
    PrefixSharedClear.cost
      (bank PrefixSharedCore.gateEmbedding
        (PrefixGateReady.prepared (q := q) v s saved output count)
        (SourceClauseRowGate.finalBank (0 : Fin 1) (vertexFrame v)
          v.val 2 s.val n s.val v.val (width 2 q + 1) true
          saved output count)) + 1

noncomputable def program (q : ℕ) :=
  BitMachineRawSequence.program
    (PrefixUnitCycle.program (width 2 q + 1) 0 false)
    (PrefixGateCycle.program 0 (width 2 q + 1))
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel
          (SourceClauseFixedBatch.labelAt
            (PrefixGateOperands.constantSize 0 (width 2 q + 1)) 0))))
    unitControl gateControl

theorem run {n q : ℕ} (v : Fin n)
    (saved output count : List Bool) :
    ∃ t ≤ unitCost n v.val (width 2 q + 1) saved output count +
        gateCost (q := q) v (0 : Fin 2)
          (firstSaved n v.val (width 2 q + 1) saved) output
          (true :: count) + 1,
      ((advance (program q))^[t])
        (⟨some (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel
              (BitMachineRawSequence.leftLabel
                (SourceClauseFixedBatch.labelAt
                  (PrefixUnitClean.constantSize (width 2 q + 1) 0) 0)))),
          (unitControl, gateControl),
          PrefixGateReady.blank n v.val saved output count⟩) =
        ⟨none, (unitControl, gateControl),
          PrefixGateReady.blank n v.val (secondSaved (q := q) v saved)
            output (List.replicate 4 true ++ count)⟩ := by
  let w := width 2 q + 1
  let s₁ := firstSaved n v.val w saved
  let B := PrefixGateReady.blank n v.val saved output count
  let C := PrefixGateReady.blank n v.val s₁ output (true :: count)
  let D := PrefixGateReady.blank n v.val
    (secondSaved (q := q) v saved) output
    (List.replicate 4 true ++ count)
  obtain ⟨a, ha, hA⟩ := PrefixUnitCycle.run n v.val w 0 false
    saved output count
  obtain ⟨b, hb, hB⟩ := PrefixGateCycle.run (q := q) v (0 : Fin 2)
    s₁ output (true :: count)
  have hA' :
      ((advance (PrefixUnitCycle.program w 0 false))^[a])
        (⟨some (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel
            (SourceClauseFixedBatch.labelAt
              (PrefixUnitClean.constantSize w 0) 0))),
          unitControl, B⟩) =
        ⟨none, unitControl, C⟩ := by
    simpa only [unitControl, C, s₁, firstSaved, B] using hA
  have hB' :
      ((advance (PrefixGateCycle.program 0 w))^[b])
        (⟨some (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel
              (SourceClauseFixedBatch.labelAt
                (PrefixGateOperands.constantSize 0 w) 0)))),
          gateControl, C⟩) =
        ⟨none, gateControl, D⟩ := by
    simpa only [gateControl, C, D, s₁, secondSaved,
      firstSaved, w, List.replicate, List.cons_append,
      List.nil_append] using hB
  obtain ⟨t, ht, h⟩ := BitMachineRawSequence.runs
    (PrefixUnitCycle.program w 0 false)
    (PrefixGateCycle.program 0 w)
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel
        (SourceClauseFixedBatch.labelAt
          (PrefixUnitClean.constantSize w 0) 0)))
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel
          (SourceClauseFixedBatch.labelAt
            (PrefixGateOperands.constantSize 0 w) 0))))
    unitControl unitControl gateControl gateControl B C D a b hA' hB'
  refine ⟨t, ?_, ?_⟩
  · change t ≤ unitCost n v.val w saved output count +
      gateCost (q := q) v (0 : Fin 2) s₁ output (true :: count) + 1
    change a ≤ unitCost n v.val w saved output count at ha
    change b ≤ gateCost (q := q) v (0 : Fin 2)
      s₁ output (true :: count) at hb
    omega
  · simpa only [program, w, B, D] using h

end EthInapproximability.CurrentPaper.SourceBooleanPrefix.PrefixFirstTwoCycles

#print axioms EthInapproximability.CurrentPaper.SourceBooleanPrefix.PrefixFirstTwoCycles.run
