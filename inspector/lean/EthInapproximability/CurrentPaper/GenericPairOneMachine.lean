import EthInapproximability.CurrentPaper.GenericPairSource
import EthInapproximability.CurrentPaper.SourceGenericPairOrdinal
import EthInapproximability.CurrentPaper.SourceClausePairMachineComposition

namespace EthInapproximability.CurrentPaper.SourceGenericPrefixMachine.PairOneMachine

open Turing BitMachineEncoding
open SourceBooleanPrefix SourceBooleanEncoding SourceClauseEncoding EncodedCNF
open SourceBooleanPrefix.PairMachineComposition
open scoped Classical

noncomputable def loader (a : Nat) (s t : Fin a) : Routine :=
  fromProgram (SourceGenericPairOrdinal.program a s t) .vertexCopy none

noncomputable def unit (a w ell : Nat) (sign : Bool) : Routine :=
  fromProgram (PairUnit.program a w ell sign)
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel
        (SourceClauseFixedBatch.labelAt
          (UnitStage.constantSize a w ell) 0)))
    (((), PrefixUnitRun.startControl), ((), none))

noncomputable def gate {a : Nat} (bit : Fin a) (ell : Fin 2)
    (sign : Bool) (w : Nat) : Routine :=
  fromProgram (PairGateCycle.program bit ell sign w)
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel
        (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel
            (BitMachineRawSequence.leftLabel
              (BitMachineRawSequence.leftLabel
                (SourceClauseFixedBatch.labelAt
                  (GateOperands.constantSize a bit.val w) 0)))))))
    (((((((), ((), none)), ((), none)), none), ()),
      PairGateExecute.gateControl), ((), none))

noncomputable def reset : Routine :=
  fromProgram PairOrdinalReset.program .drain none

noncomputable def routine (a q : Nat) (s t : Fin a) : Routine :=
  let w := width a q + 1
  sequence
    (sequence
      (sequence
        (sequence
          (sequence (loader a s t) (unit a w 0 false))
          (gate s 0 (decide (s=t)) w))
        (gate t 1 false w))
      (unit a w 2 true))
    reset

noncomputable def unitCost (n a ordinal w ell : Nat) (sign : Bool)
    (saved output count : List Bool) : Nat :=
  UnitCycle.cost n a ordinal w ell sign saved output count

noncomputable def gateCost {n a : Nat} (v : Fin n) (bit : Fin a)
    (ell : Fin 2) (ordinal w : Nat) (sign : Bool)
    (saved output count : List Bool) : Nat :=
  GateOperands.cost a bit.val w (List.replicate v.val true) +
    (v.val + bit.val + 4) + (2*ordinal+2) +
    (PairGatePatch.offsetSize ell 0 + 2) + 3 +
    SourceClauseRowGate.cost v.val a bit.val n ell.val ordinal w sign + 1 +
    PrefixSharedClear.cost (PairGateCleanup.localBank v bit ell.val ordinal w sign
      saved output count) + 1

noncomputable def cost {n a q : Nat} (v : Fin n) (s t : Fin a)
    (saved output count : List Bool) : Nat :=
  let ord := SourceGenericPrefix.pairOrdinal v s t
  let w := width a q + 1
  let s₁ := UnitHandoff.nextSaved n a ord w 0 false saved
  let s₂ := (clauseFields (PairGateCleanup.emitted v s 0 ord w
    (decide (s=t)))).reverse ++ s₁
  let s₃ := (clauseFields (PairGateCleanup.emitted v t 1 ord w false)).reverse ++ s₂
  let c₁ := true :: count
  let c₂ := true :: true :: true :: c₁
  let c₃ := true :: true :: true :: c₂
  SourceGenericPairOrdinal.clock n v.val +
    unitCost n a ord w 0 false saved output count + 1 +
    gateCost v s 0 ord w (decide (s=t)) s₁ output c₁ + 1 +
    gateCost v t 1 ord w false s₂ output c₂ + 1 +
    unitCost n a ord w 2 true s₃ output c₃ + 1 +
    (ord+2)+1

theorem run {n a q : Nat} (v : Fin n) (s t : Fin a)
    (saved output count : List Bool) :
    Runs (routine a q s t)
      (PairUnitLift.pairBank n v.val 0 saved output count)
      (PairUnitLift.pairBank n v.val 0
        ((clauseFields (chain
          (SourceGenericPrefix.base n a q (SourceGenericPrefix.pairOrdinal v s t))
          (SourceGenericPrefix.pairPayload v s t))).reverse ++ saved)
        output (List.replicate 8 true ++ count))
      (cost (q := q) v s t saved output count) := by
  let ord := SourceGenericPrefix.pairOrdinal v s t
  let w := width a q + 1
  let s₁ := UnitHandoff.nextSaved n a ord w 0 false saved
  let s₂ := (clauseFields (PairGateCleanup.emitted v s 0 ord w
    (decide (s=t)))).reverse ++ s₁
  let s₃ := (clauseFields (PairGateCleanup.emitted v t 1 ord w false)).reverse ++ s₂
  let s₄ := UnitHandoff.nextSaved n a ord w 2 true s₃
  let c₁ := true :: count
  let c₂ := true :: true :: true :: c₁
  let c₃ := true :: true :: true :: c₂
  let c₄ := true :: c₃
  let B₀ := PairUnitLift.pairBank n v.val 0 saved output count
  let B₁ := PairUnitLift.pairBank n v.val ord saved output count
  let B₂ := PairUnitLift.pairBank n v.val ord s₁ output c₁
  let B₃ := PairUnitLift.pairBank n v.val ord s₂ output c₂
  let B₄ := PairUnitLift.pairBank n v.val ord s₃ output c₃
  let B₅ := PairUnitLift.pairBank n v.val ord s₄ output c₄
  let B₆ := PairUnitLift.pairBank n v.val 0 s₄ output c₄
  have h₀ : Runs (loader a s t) B₀ B₁
      (SourceGenericPairOrdinal.clock n v.val) := by
    exact ⟨_,le_refl _,SourceGenericPairOrdinal.pairBank_run_source v a s t
      saved output count⟩
  have h₁ : Runs (unit a w 0 false) B₁ B₂
      (unitCost n a ord w 0 false saved output count) := by
    simpa only [Runs,unit,fromProgram,unitCost] using
      (PairUnit.run n a v.val ord w 0 false saved output count)
  have h₂ : Runs (gate s 0 (decide (s=t)) w) B₂ B₃
      (gateCost v s 0 ord w (decide (s=t)) s₁ output c₁) := by
    simpa only [Runs,gate,fromProgram,gateCost] using
      (PairGateCycle.run v s 0 ord w (decide (s=t)) s₁ output c₁)
  have h₃ : Runs (gate t 1 false w) B₃ B₄
      (gateCost v t 1 ord w false s₂ output c₂) := by
    simpa only [Runs,gate,fromProgram,gateCost] using
      (PairGateCycle.run v t 1 ord w false s₂ output c₂)
  have h₄ : Runs (unit a w 2 true) B₄ B₅
      (unitCost n a ord w 2 true s₃ output c₃) := by
    simpa only [Runs,unit,fromProgram,unitCost] using
      (PairUnit.run n a v.val ord w 2 true s₃ output c₃)
  have h₅ : Runs reset B₅ B₆ (ord+2) := by
    exact ⟨_,le_refl _,PairOrdinalReset.pairBank_run n v.val ord s₄ output c₄⟩
  have h₀₁ := runs_sequence (loader a s t) (unit a w 0 false)
    B₀ B₁ B₂ _ _ h₀ h₁
  have h₀₂ := runs_sequence _ _ B₀ B₂ B₃ _ _ h₀₁ h₂
  have h₀₃ := runs_sequence _ _ B₀ B₃ B₄ _ _ h₀₂ h₃
  have h₀₄ := runs_sequence _ _ B₀ B₄ B₅ _ _ h₀₃ h₄
  have h₀₅ := runs_sequence _ _ B₀ B₅ B₆ _ _ h₀₄ h₅
  have hs : s₄ =
      (clauseFields (chain (SourceGenericPrefix.base n a q ord)
        (SourceGenericPrefix.pairPayload v s t))).reverse ++ saved :=
    PairSource.savedAfter_eq_chain (q := q) v s t saved
  have hc : c₄ = List.replicate 8 true ++ count := by
    simp [c₄,c₃,c₂,c₁,List.replicate]
  simpa only [routine,cost,ord,w,s₁,s₂,s₃,s₄,c₁,c₂,c₃,c₄,
    B₀,B₆,hs,hc] using h₀₅

#print axioms run

end EthInapproximability.CurrentPaper.SourceGenericPrefixMachine.PairOneMachine
