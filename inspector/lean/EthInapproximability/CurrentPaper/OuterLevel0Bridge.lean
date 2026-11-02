import EthInapproximability.CurrentPaper.OuterLevel0Prep
import EthInapproximability.CurrentPaper.WeightedLevel0WriterRun

/-! Lane owner:b-weighted-level-5, unit 2, segment 1 (1c-c-outer), piece D.

The charged handoff into the ADMITTED physical step: the admitted
`MatrixTableInterlaceProtectedBridge.program` embedded by `pEmb` into the SAME
global stack `HStack` (its writer region is owner-4's `wEmb` region, its outer
region is the outer region written by `prepProgram`). From ANY bank that
agrees with `exitBank` (the exit of `prepProgram`) on every bridge cell except
writer 22, and holds `d.rawBits` in writer 22 (THE one named premise, lane
owner:b-stage4-entry-program-3), the embedded program runs within the admitted
`actualPhysicalBudget` to a halted configuration whose second-output cell is
the admitted `actualPhysicalOutput`; all cells outside the bridge region are
unchanged (`bank pEmb S _`). This is `actual_physical_step_run` transported,
not re-proved. -/

namespace EthInapproximability.CurrentPaper.OuterLevel0Bridge

open Turing BitMachineEncoding BitMachineStackEmbedding
open EthInapproximability.ParameterizedNP.GuardedSourceGraph
open WeightedLevel0Rows WeightedLevel0Persist WeightedLevel0Clean WeightedLevel0Ready
open OuterLevel0Prep

noncomputable section

set_option maxHeartbeats 8000000
set_option maxRecDepth 8192
set_option synthInstance.maxSize 200000
set_option synthInstance.maxHeartbeats 2000000

abbrev BStack := MatrixTableInterlaceProtectedBridge.Stack

def pMap : BStack → HStack
  | .inl w => .inl (wEmb w)
  | .inr o => oc o

theorem pMap_inj : Function.Injective pMap := by
  intro a b h
  rcases a with w | o <;> rcases b with w' | o'
  · exact congrArg Sum.inl (wEmb.injective (Sum.inl.inj h))
  · cases h
  · cases h
  · exact congrArg Sum.inr (Sum.inl.inj (Sum.inr.inj h))

/-- The admitted protected-bridge stack inside the global stack. -/
def pEmb : BStack ↪ HStack := ⟨pMap, pMap_inj⟩

/-- The admitted physical-step program on the global stack. -/
def bridgeH := fun l => stackStmt pEmb (MatrixTableInterlaceProtectedBridge.program l)

/-- The admitted run, with the run's decidable-equality instance replaced by
the ambient one (the two are equal by `Subsingleton`). -/
theorem bridge_advance_eq (i : DecidableEq BStack) :
    @advance BStack MatrixTableInterlaceProtectedBridge.Label
      MatrixTableInterlaceProtectedBridge.Control i
      MatrixTableInterlaceProtectedBridge.program =
    advance MatrixTableInterlaceProtectedBridge.program := by
  congr 1

variable (M : BitMachine.Machine)
variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

theorem level0_physical_handoff (G : EndpointGraph V E) (n c : ℕ)
    (F : ETHBinsJoinedScratch.Stack → List Bool)
    (Q : WeightedGraphQJoined.Stack → List Bool) (P : ChosenPrimeRaw.Stack → List Bool)
    (hf : level0Facts M G n c F Q P) (S : HStack → List Bool)
    (hS : ∀ x : BStack, x ≠ .inl (.inl (.inl 22)) →
      S (pEmb x) = exitBank G n c (G4 (level0RowsBank M G n c F Q P)) (pEmb x))
    (h22 : S (pEmb (.inl (.inl (.inl 22)))) =
      (ProtectedFullBankBridgeScratch.actualD G c (EffectiveIteration.sourceDepth n)
        (Iteration.seedState (EffectiveIteration.sourceDepth n)).budget 0
        (Iteration.seedState (EffectiveIteration.sourceDepth n)).matrix).rawBits) :
    ∃ t ≤ ProtectedFullBankBridgeScratch.actualPhysicalBudget G c (EffectiveIteration.sourceDepth n)
        (Iteration.seedState (EffectiveIteration.sourceDepth n)).budget 0
        (Iteration.seedState (EffectiveIteration.sourceDepth n)).matrix,
      ∃ z : MatrixTableInterlaceProtectedBridge.Config,
        ((advance bridgeH)^[t])
          (⟨some MatrixTableInterlaceProtectedBridge.start,
            ((MatrixWeightedOrderPreparation.initial, MatrixWeightedOrderWriter.writerInitial),
              (OuterStartBank.outerVar, none)), S⟩ :
            TM2.Cfg (fun _ : HStack => Bool) MatrixTableInterlaceProtectedBridge.Label
              MatrixTableInterlaceProtectedBridge.Control) =
          ⟨z.l, z.var, bank pEmb S z.stk⟩ ∧
        z.l = none ∧
        z.stk (.inr MatrixTableInterlaceOuterJoin.secondOutput) =
          ProtectedFullBankBridgeScratch.actualPhysicalOutput G c (EffectiveIteration.sourceDepth n)
            (Iteration.seedState (EffectiveIteration.sourceDepth n)).budget 0
            (Iteration.seedState (EffectiveIteration.sourceDepth n)).matrix := by
  obtain ⟨t, ht, z, hz, hl, hout⟩ := ProtectedFullBankBridgeScratch.actual_physical_step_run
    G c (EffectiveIteration.sourceDepth n)
    (Iteration.seedState (EffectiveIteration.sourceDepth n)).budget 0
    (Iteration.seedState (EffectiveIteration.sourceDepth n)).matrix
  have hz' : ((advance MatrixTableInterlaceProtectedBridge.program)^[t])
      (ProtectedFullBankBridgeScratch.actualPhysicalStart G c (EffectiveIteration.sourceDepth n)
        (Iteration.seedState (EffectiveIteration.sourceDepth n)).budget 0
        (Iteration.seedState (EffectiveIteration.sourceDepth n)).matrix) = z := by
    rw [← bridge_advance_eq]
    exact hz
  have hG : ∀ k : BStack,
      (ProtectedFullBankBridgeScratch.actualPhysicalStart G c (EffectiveIteration.sourceDepth n)
        (Iteration.seedState (EffectiveIteration.sourceDepth n)).budget 0
        (Iteration.seedState (EffectiveIteration.sourceDepth n)).matrix).stk k = S (pEmb k) := by
    intro k
    rcases k with w | o
    · rw [OuterStartBank.actualPhysicalStart_writer]
      by_cases hw : w = .inl (.inl 22)
      · subst hw
        rw [WeightedLevel0WriterRun.writer_start_22, h22]
      · rw [hS (.inl w) (by intro e; exact hw (Sum.inl.inj e))]
        exact (ready_writer M G n c F Q P hf w hw).symm
    · rw [OuterStartBank.actualPhysicalStart_outer, hS (.inr o) (by intro e; cases e)]
      rfl
  have r := WeightedRawWords.region_run pEmb MatrixTableInterlaceProtectedBridge.program
    _ _ t hz' S hG
  rw [OuterStartBank.actualPhysicalStart_label, OuterStartBank.actualPhysicalStart_var] at r
  exact ⟨t, ht, z, r, hl, hout⟩

#print axioms pMap_inj
#print axioms bridge_advance_eq
#print axioms level0_physical_handoff

end
end EthInapproximability.CurrentPaper.OuterLevel0Bridge
