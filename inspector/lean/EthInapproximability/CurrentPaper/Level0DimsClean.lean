import EthInapproximability.CurrentPaper.Level0DimsRound
import EthInapproximability.CurrentPaper.Level0CleanRun

/-! Lane owner:b-weighted-level-8, unit 2, segment 2c splice, piece 2: the level-0 round with
cost AND dims updates (`Level0DimsRound.round4Program`) followed, on the SAME stack `H4`, by a
charged copy of the admitted output word (cell `oc secondOutput`) into the fresh cell
`outCell = .inr 55` (temporary `.inr 56`) and a charged clear of the WHOLE bridge region (every
cell `pEmb x`), the clear charged through the growth conjunct of `level0_dims_round` (the SAME
bridge run). This replays owner-6 `Level0CleanRun.level0_clean` on `H4`; `blankBridge` and `nB`
are owner-6's.

Exit bank EXACT and free of the admitted step's residue: the prep/cost exit `S2` with the bridge
region blank on `HStack`, blank cost cells, and on the fresh region `D1` (rows and columns of
level 1 in cells 0, 1) with `outCell` holding the admitted output word (the row-major word of the
physical level-1 matrix). Masters C, B, Y, E and fresh cells 0, 1 hold all six level-1 raw
words. -/

namespace EthInapproximability.CurrentPaper.Level0DimsClean

open Turing BitMachineEncoding BitMachineStackEmbedding
open EthInapproximability.ParameterizedNP.GuardedSourceGraph
open WeightedLevel0Rows WeightedLevel0Persist WeightedLevel0Clean WeightedLevel0Ready
open OuterLevel0Prep OuterLevel0Run OuterLevel0Bridge OuterLevel0Full NextMasterWords
open CostUpdateStages CostUpdateMachine CostUpdateEmbed Level0CostRound Level0CostRun
open Level0DimsRound

noncomputable section

set_option maxHeartbeats 8000000
set_option maxRecDepth 8192
set_option synthInstance.maxSize 200000
set_option synthInstance.maxHeartbeats 2000000

def outCell : H4 := .inr 55
def tmpCell : H4 := .inr 56
def srcOut : H4 := .inl (.inl (oc MatrixTableInterlaceOuterJoin.secondOutput))

def outSlots : Fin 3 ↪ H4 := ⟨![srcOut, outCell, tmpCell], by
  intro a b h
  fin_cases a <;> fin_cases b <;>
    first
    | rfl
    | (exfalso; cases h; done)
    | exact absurd (Sum.inr.inj h) (by decide)⟩

def copyOutP := MatrixStage4ScalarPreparationOps.copyProgram outSlots

section Clean

variable [Fintype BStack]

def bridgeCells4 (i : Fin Level0CleanRun.nB) : H4 :=
  .inl (.inl (pEmb ((Fintype.equivFin BStack).symm i)))

theorem bridgeCells4_inj : Function.Injective bridgeCells4 := by
  intro a b h
  exact (Fintype.equivFin BStack).symm.injective (pEmb.injective (Sum.inl.inj (Sum.inl.inj h)))

def clearB4 := WeightedRawWords.clearProgram bridgeCells4

variable (M : BitMachine.Machine)
variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- ONE fixed program: the level-0 round with cost and dims updates ; copy of the output word ;
clear of the bridge region. -/
def clean4Program (c : ℕ) {LW VW : Type} (W : LW → TM2.Stmt (fun _ : HStack => Bool) LW VW)
    (w₀ : LW) (v₀ : VW) :=
  BitMachineRawSequence.program (round4Program M c W w₀ v₀)
    (BitMachineRawSequence.program copyOutP clearB4 0 none ((), none))
    (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)
    (((((((none, ((), ((WeightedRawWords.level0Ctrl, (WeightedRawWords.edgesCtrl, WeightedRawWords.tailCtrl)), WeightedRawWords.kCtrl M))), WeightedVertexWord.vertexCtrl), (WeightedLevelFields15.initialControl, (((), none), WeightedRowFields.rowInit))), ((), none)), ((none : Option Bool), ((none : Option Bool), ((), none)))), ctrl27), (v₀, (costCtrl, (NextDimsMachineTN.dimsCtrl, bridgeCtrl))))
    (none, ((), none))

theorem level0_dims_clean [Fintype MatrixTableInterlaceProtectedBridge.Label]
    (G : EndpointGraph V E) (n c : ℕ) (hc : 1 ≤ c) {LW VW : Type}
    (W : LW → TM2.Stmt (fun _ : HStack => Bool) LW VW) (w₀ : LW) (v₀ : VW) (T22 : ℕ)
    (hW : Writer22Spec M W w₀ v₀ T22 G n c) :
    ∃ F : ETHBinsJoinedScratch.Stack → List Bool,
    ∃ Q : WeightedGraphQJoined.Stack → List Bool,
    ∃ P : ChosenPrimeRaw.Stack → List Bool,
    ∃ t ≤ (prepBound M G n c +
        (T22 + (costBound (Parameters.scale (P0 G n c)) (EffectiveIteration.sourceDepth n) c
            (Parameters.bins (P0 G n c)) (Fintype.card E)
            (Iteration.seedState (EffectiveIteration.sourceDepth n)).budget +
          (NextDimsMachineTN.dimsBound (dx G n c) +
            ProtectedFullBankBridgeScratch.actualPhysicalBudget G c
              (EffectiveIteration.sourceDepth n)
              (Iteration.seedState (EffectiveIteration.sourceDepth n)).budget 0
              (Iteration.seedState (EffectiveIteration.sourceDepth n)).matrix + 1) + 1) + 1) + 1) +
        ((2 * (ProtectedFullBankBridgeScratch.actualPhysicalOutput G c (EffectiveIteration.sourceDepth n)
            (Iteration.seedState (EffectiveIteration.sourceDepth n)).budget 0
            (Iteration.seedState (EffectiveIteration.sourceDepth n)).matrix).length + 2) +
          ((∑ i : Fin Level0CleanRun.nB,
              (((ProtectedFullBankBridgeScratch.actualPhysicalStart G c (EffectiveIteration.sourceDepth n)
                (Iteration.seedState (EffectiveIteration.sourceDepth n)).budget 0
                (Iteration.seedState (EffectiveIteration.sourceDepth n)).matrix).stk
                  ((Fintype.equivFin BStack).symm i)).length +
                BitMachineStackGrowth.perStep bridgeH *
                  ProtectedFullBankBridgeScratch.actualPhysicalBudget G c (EffectiveIteration.sourceDepth n)
                    (Iteration.seedState (EffectiveIteration.sourceDepth n)).budget 0
                    (Iteration.seedState (EffectiveIteration.sourceDepth n)).matrix)) + Level0CleanRun.nB + 2) + 1) + 1,
      ((advance (clean4Program M c W w₀ v₀))^[t])
          ⟨some (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel (.inl (.scan 0)))))))))),
            ((((((((none, ((), ((WeightedRawWords.level0Ctrl, (WeightedRawWords.edgesCtrl, WeightedRawWords.tailCtrl)), WeightedRawWords.kCtrl M))), WeightedVertexWord.vertexCtrl), (WeightedLevelFields15.initialControl, (((), none), WeightedRowFields.rowInit))), ((), none)), ((none : Option Bool), ((none : Option Bool), ((), none)))), ctrl27), (v₀, (costCtrl, (NextDimsMachineTN.dimsCtrl, bridgeCtrl)))), (none, ((), none))),
            ext4 (H0 (SourceOriginalBranchPackets.packet n (EncodedGraph.encode (EncodedETHSource.serializeGraph G)))) blank57⟩ =
        ⟨none, ((((((((none, ((), ((WeightedRawWords.level0Ctrl, (WeightedRawWords.edgesCtrl, WeightedRawWords.tailCtrl)), WeightedRawWords.kCtrl M))), WeightedVertexWord.vertexCtrl), (WeightedLevelFields15.initialControl, (((), none), WeightedRowFields.rowInit))), ((), none)), ((none : Option Bool), ((none : Option Bool), ((), none)))), ctrl27), (v₀, (costCtrl, (NextDimsMachineTN.dimsCtrl, bridgeCtrl)))), (none, ((), none))),
          Function.update (ext4 (Level0CleanRun.blankBridge (S2 M G n c F Q P)) (D1 G n c)) outCell
            (ProtectedFullBankBridgeScratch.actualPhysicalOutput G c (EffectiveIteration.sourceDepth n)
              (Iteration.seedState (EffectiveIteration.sourceDepth n)).budget 0
              (Iteration.seedState (EffectiveIteration.sourceDepth n)).matrix)⟩ ∧
      level0Facts M G n c F Q P ∧
      Level0CleanRun.blankBridge (S2 M G n c F Q P) (mcell .C) =
        ETHParameterScaleMachineInput.words (rp G n c (0 + 1)) 0 ∧
      Level0CleanRun.blankBridge (S2 M G n c F Q P) (mcell .B) =
        ETHParameterScaleMachineInput.words (rp G n c (0 + 1)) 1 ∧
      Level0CleanRun.blankBridge (S2 M G n c F Q P) (mcell .Y) =
        ETHParameterScaleMachineInput.words (rp G n c (0 + 1)) 2 ∧
      D1 G n c 0 = ETHParameterScaleMachineInput.words (rp G n c (0 + 1)) 3 ∧
      D1 G n c 1 = ETHParameterScaleMachineInput.words (rp G n c (0 + 1)) 4 ∧
      Level0CleanRun.blankBridge (S2 M G n c F Q P) (mcell .E) =
        ETHParameterScaleMachineInput.words (rp G n c (0 + 1)) 5 := by
  obtain ⟨F, Q, P, t, ht, z, hrun, hout, hf, mC, mB, mY, mR, mCo, mE, hgrow⟩ :=
    level0_dims_round M G n c hc W w₀ v₀ T22 hW
  set X : H4 → List Bool := ext4 (bank pEmb (S2 M G n c F Q P) z.stk) (D1 G n c) with hX
  have hX0 : X srcOut = ProtectedFullBankBridgeScratch.actualPhysicalOutput G c
      (EffectiveIteration.sourceDepth n)
      (Iteration.seedState (EffectiveIteration.sourceDepth n)).budget 0
      (Iteration.seedState (EffectiveIteration.sourceDepth n)).matrix := by
    show bank pEmb (S2 M G n c F Q P) z.stk (pEmb (.inr MatrixTableInterlaceOuterJoin.secondOutput)) = _
    rw [bank_at]
    exact hout
  have hXt : X (outSlots 2) = [] := D1_spare G n c 56 (by decide) (by decide)
  have hc0 := MatrixStage4ScalarPreparationOps.copy_run outSlots X hXt
  have e0 : outSlots 0 = srcOut := rfl
  have e1 : outSlots 1 = outCell := rfl
  have hXo : X outCell = [] := D1_spare G n c 55 (by decide) (by decide)
  rw [e0, e1, hX0, hXo, List.append_nil] at hc0
  set X1 := Function.update X outCell
    (ProtectedFullBankBridgeScratch.actualPhysicalOutput G c (EffectiveIteration.sourceDepth n)
      (Iteration.seedState (EffectiveIteration.sourceDepth n)).budget 0
      (Iteration.seedState (EffectiveIteration.sourceDepth n)).matrix) with hX1
  have hcl := WeightedRawWords.clear_run bridgeCells4 bridgeCells4_inj X1
  have hfinal : BitMachineClearBank.cleared bridgeCells4 X1 =
      Function.update (ext4 (Level0CleanRun.blankBridge (S2 M G n c F Q P)) (D1 G n c)) outCell
        (ProtectedFullBankBridgeScratch.actualPhysicalOutput G c (EffectiveIteration.sourceDepth n)
          (Iteration.seedState (EffectiveIteration.sourceDepth n)).budget 0
          (Iteration.seedState (EffectiveIteration.sourceDepth n)).matrix) := by
    funext y
    unfold BitMachineClearBank.cleared
    rcases y with (h | h) | i
    · by_cases hb : ∃ y', pEmb y' = h
      · obtain ⟨y', rfl⟩ := hb
        have hin : ∃ i, bridgeCells4 i = (.inl (.inl (pEmb y')) : H4) :=
          ⟨(Fintype.equivFin BStack) y', by simp [bridgeCells4]⟩
        rw [if_pos hin, Function.update_of_ne (by intro e; cases e)]
        show [] = Level0CleanRun.blankBridge (S2 M G n c F Q P) (pEmb y')
        simp only [Level0CleanRun.blankBridge]
        rw [if_pos ⟨y', rfl⟩]
      · have hin : ¬ ∃ i, bridgeCells4 i = (.inl (.inl h) : H4) := by
          rintro ⟨i, hi⟩
          exact hb ⟨_, Sum.inl.inj (Sum.inl.inj hi)⟩
        rw [if_neg hin, hX1, Function.update_of_ne (by intro e; cases e),
          Function.update_of_ne (by intro e; cases e)]
        show bank pEmb (S2 M G n c F Q P) z.stk h = Level0CleanRun.blankBridge (S2 M G n c F Q P) h
        rw [bank_outside _ _ _ _ hb]
        simp only [Level0CleanRun.blankBridge]
        rw [if_neg hb]
    · have hin : ¬ ∃ i, bridgeCells4 i = (.inl (.inr h) : H4) := by
        rintro ⟨i, hi⟩
        cases hi
      rw [if_neg hin, hX1, Function.update_of_ne (by intro e; cases e),
        Function.update_of_ne (by intro e; cases e)]
      rfl
    · have hin : ¬ ∃ j, bridgeCells4 j = (.inr i : H4) := by
        rintro ⟨j, hj⟩
        cases hj
      rw [if_neg hin, hX1]
      by_cases hi : (Sum.inr i : H4) = outCell
      · rw [hi, Function.update_self, Function.update_self]
      · rw [Function.update_of_ne hi, Function.update_of_ne hi]
        rfl
  rw [hfinal] at hcl
  have hsum : (∑ i : Fin Level0CleanRun.nB, (X1 (bridgeCells4 i)).length) ≤
      ∑ i : Fin Level0CleanRun.nB,
        (((ProtectedFullBankBridgeScratch.actualPhysicalStart G c (EffectiveIteration.sourceDepth n)
          (Iteration.seedState (EffectiveIteration.sourceDepth n)).budget 0
          (Iteration.seedState (EffectiveIteration.sourceDepth n)).matrix).stk
            ((Fintype.equivFin BStack).symm i)).length +
          BitMachineStackGrowth.perStep bridgeH *
            ProtectedFullBankBridgeScratch.actualPhysicalBudget G c (EffectiveIteration.sourceDepth n)
              (Iteration.seedState (EffectiveIteration.sourceDepth n)).budget 0
              (Iteration.seedState (EffectiveIteration.sourceDepth n)).matrix) := by
    apply Finset.sum_le_sum
    intro i _
    rw [hX1, Function.update_of_ne (by intro e; cases e)]
    show (bank pEmb (S2 M G n c F Q P) z.stk (pEmb ((Fintype.equivFin BStack).symm i))).length ≤ _
    rw [bank_at]
    exact hgrow _
  obtain ⟨t2, ht2, q2⟩ := BitMachineRawSequence.runs copyOutP clearB4
    BitMachineCopy.Label.scan 0 none none ((), none) ((), none) X X1 _ _ _ hc0 hcl
  obtain ⟨u, hu, q1⟩ := BitMachineRawSequence.runs (round4Program M c W w₀ v₀) _
    _ _ _ _ _ _ _ _ _ _ _ hrun q2
  have hbb : ∀ a : WeightedRawWords.Aux,
      Level0CleanRun.blankBridge (S2 M G n c F Q P) (mcell a) = S2 M G n c F Q P (mcell a) := by
    intro a
    simp only [Level0CleanRun.blankBridge]
    rw [if_neg (mcell_outside a)]
  rw [bank_master] at mC mB mY mE
  refine ⟨F, Q, P, u, ?_, q1, hf, by rw [hbb]; exact mC, by rw [hbb]; exact mB,
    by rw [hbb]; exact mY, mR, mCo, by rw [hbb]; exact mE⟩
  unfold Level0CleanRun.nB at hsum ht2 ⊢
  omega

#print axioms level0_dims_clean

end Clean

/-! ## The instance premises discharged by the globally synthesized instances -/

abbrev instLabel : Fintype MatrixTableInterlaceProtectedBridge.Label := inferInstance
abbrev instBStack : Fintype BStack := inferInstance

/-- `level0_dims_clean` with both instance arguments supplied by the globally synthesized
instances `instBStack`, `instLabel` (statement: literally `level0_dims_clean`'s at them). -/
theorem level0_dims_clean_inst (M : BitMachine.Machine) {V E : Type} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E] :
    type_of% (@level0_dims_clean instBStack M V E _ _ _ _ instLabel) :=
  @level0_dims_clean instBStack M V E _ _ _ _ instLabel

#print axioms instLabel
#print axioms instBStack
#print axioms level0_dims_clean_inst

end
end EthInapproximability.CurrentPaper.Level0DimsClean
