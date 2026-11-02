import EthInapproximability.CurrentPaper.Level0RoundClean

/-! Lane owner:b-weighted-level-6, unit 2, segment 2e, piece 2: the level-0
round followed by a charged harvest of the admitted output word and a charged
clear of the WHOLE bridge region (see `Level0RoundClean` for piece 1 and the
disclosed instance premises). Global stack `H3 = H2 ⊕ Fin 2` (`outCell` holds
the next-level matrix word; `tmpCell` is the copy temporary). -/

namespace EthInapproximability.CurrentPaper.Level0CleanRun

open Turing BitMachineEncoding BitMachineStackEmbedding
open EthInapproximability.ParameterizedNP.GuardedSourceGraph
open WeightedLevel0Rows WeightedLevel0Persist WeightedLevel0Clean WeightedLevel0Ready
open OuterLevel0Prep OuterLevel0Run OuterLevel0Bridge OuterLevel0Full NextMasterWords
open CostUpdateStages CostUpdateMachine CostUpdateEmbed Level0CostRound Level0CostRun
open Level0RoundClean

noncomputable section

set_option maxHeartbeats 8000000
set_option maxRecDepth 8192
set_option synthInstance.maxSize 200000
set_option synthInstance.maxHeartbeats 2000000

abbrev H3 := H2 ⊕ Fin 2

def iH : H2 ↪ H3 := ⟨Sum.inl, Sum.inl_injective⟩

def ext3 (S : H2 → List Bool) : H3 → List Bool := Sum.elim S (fun _ => [])

def lift3 {L V : Type} (P : L → TM2.Stmt (fun _ : H2 => Bool) L V) :
    L → TM2.Stmt (fun _ : H3 => Bool) L V :=
  fun l => stackStmt iH (P l)

theorem bank_ext3 (S T : H2 → List Bool) : bank iH (ext3 S) T = ext3 T := by
  funext x
  rcases x with x | x
  · exact bank_at iH (ext3 S) T x
  · rw [bank_outside _ _ _ _ (by rintro ⟨k, hk⟩; cases hk)]
    rfl

theorem lift3_run {L V : Type} (P : L → TM2.Stmt (fun _ : H2 => Bool) L V)
    (l l' : Option L) (v v' : V) (S T : H2 → List Bool) (t : ℕ)
    (h : ((advance P)^[t]) (⟨l, v, S⟩ : TM2.Cfg (fun _ : H2 => Bool) L V) = ⟨l', v', T⟩) :
    ((advance (lift3 P))^[t]) (⟨l, v, ext3 S⟩ : TM2.Cfg (fun _ : H3 => Bool) L V) =
      ⟨l', v', ext3 T⟩ := by
  have r := WeightedRawWords.region_run iH P ⟨l, v, S⟩ ⟨l', v', T⟩ t h (ext3 S) (fun _ => rfl)
  dsimp only at r
  rw [bank_ext3] at r
  exact r

def outCell : H3 := .inr 0
def tmpCell : H3 := .inr 1
def srcOut : H3 := .inl (.inl (oc MatrixTableInterlaceOuterJoin.secondOutput))

def outSlots : Fin 3 ↪ H3 := ⟨![srcOut, outCell, tmpCell], by
  intro a b h
  fin_cases a <;> fin_cases b <;>
    first
    | rfl
    | (exfalso; cases h; done)
    | exact absurd (Sum.inr.inj h) (by decide)⟩

def copyOutP := MatrixStage4ScalarPreparationOps.copyProgram outSlots

/-- The prep/cost exit bank with the whole bridge region blank. -/
def blankBridge (S : HStack → List Bool) : HStack → List Bool :=
  fun x => if ∃ y, pEmb y = x then [] else S x

section Clean

variable [Fintype BStack]

def nB : ℕ := Fintype.card BStack

def bridgeCells (i : Fin nB) : H3 :=
  .inl (.inl (pEmb ((Fintype.equivFin BStack).symm i)))

theorem bridgeCells_inj : Function.Injective bridgeCells := by
  intro a b h
  exact (Fintype.equivFin BStack).symm.injective (pEmb.injective (Sum.inl.inj (Sum.inl.inj h)))

def clearB := WeightedRawWords.clearProgram bridgeCells

variable (M : BitMachine.Machine)
variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- ONE fixed program: the level-0 round ; copy of the output word ; clear of the bridge region. -/
def cleanProgram (c : ℕ) {LW VW : Type} (W : LW → TM2.Stmt (fun _ : HStack => Bool) LW VW)
    (w₀ : LW) (v₀ : VW) :=
  BitMachineRawSequence.program (lift3 (roundProgram M c W w₀ v₀))
    (BitMachineRawSequence.program copyOutP clearB 0 none ((), none))
    (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)
    (((((((none, ((), ((WeightedRawWords.level0Ctrl, (WeightedRawWords.edgesCtrl, WeightedRawWords.tailCtrl)), WeightedRawWords.kCtrl M))), WeightedVertexWord.vertexCtrl), (WeightedLevelFields15.initialControl, (((), none), WeightedRowFields.rowInit))), ((), none)), ((none : Option Bool), ((none : Option Bool), ((), none)))), ctrl27), (v₀, (costCtrl, bridgeCtrl)))
    (none, ((), none))

theorem level0_clean [Fintype MatrixTableInterlaceProtectedBridge.Label]
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
          ProtectedFullBankBridgeScratch.actualPhysicalBudget G c
            (EffectiveIteration.sourceDepth n)
            (Iteration.seedState (EffectiveIteration.sourceDepth n)).budget 0
            (Iteration.seedState (EffectiveIteration.sourceDepth n)).matrix + 1) + 1) + 1) +
        ((2 * (ProtectedFullBankBridgeScratch.actualPhysicalOutput G c (EffectiveIteration.sourceDepth n)
            (Iteration.seedState (EffectiveIteration.sourceDepth n)).budget 0
            (Iteration.seedState (EffectiveIteration.sourceDepth n)).matrix).length + 2) +
          ((∑ i : Fin nB,
              (((ProtectedFullBankBridgeScratch.actualPhysicalStart G c (EffectiveIteration.sourceDepth n)
                (Iteration.seedState (EffectiveIteration.sourceDepth n)).budget 0
                (Iteration.seedState (EffectiveIteration.sourceDepth n)).matrix).stk
                  ((Fintype.equivFin BStack).symm i)).length +
                BitMachineStackGrowth.perStep bridgeH *
                  ProtectedFullBankBridgeScratch.actualPhysicalBudget G c (EffectiveIteration.sourceDepth n)
                    (Iteration.seedState (EffectiveIteration.sourceDepth n)).budget 0
                    (Iteration.seedState (EffectiveIteration.sourceDepth n)).matrix)) + nB + 2) + 1) + 1,
      ((advance (cleanProgram M c W w₀ v₀))^[t])
          ⟨some (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel (.inl (.scan 0)))))))))),
            ((((((((none, ((), ((WeightedRawWords.level0Ctrl, (WeightedRawWords.edgesCtrl, WeightedRawWords.tailCtrl)), WeightedRawWords.kCtrl M))), WeightedVertexWord.vertexCtrl), (WeightedLevelFields15.initialControl, (((), none), WeightedRowFields.rowInit))), ((), none)), ((none : Option Bool), ((none : Option Bool), ((), none)))), ctrl27), (v₀, (costCtrl, bridgeCtrl))), (none, ((), none))),
            ext3 (ext (H0 (SourceOriginalBranchPackets.packet n (EncodedGraph.encode (EncodedETHSource.serializeGraph G)))))⟩ =
        ⟨none, ((((((((none, ((), ((WeightedRawWords.level0Ctrl, (WeightedRawWords.edgesCtrl, WeightedRawWords.tailCtrl)), WeightedRawWords.kCtrl M))), WeightedVertexWord.vertexCtrl), (WeightedLevelFields15.initialControl, (((), none), WeightedRowFields.rowInit))), ((), none)), ((none : Option Bool), ((none : Option Bool), ((), none)))), ctrl27), (v₀, (costCtrl, bridgeCtrl))), (none, ((), none))),
          Function.update (ext3 (ext (blankBridge (S2 M G n c F Q P)))) outCell
            (ProtectedFullBankBridgeScratch.actualPhysicalOutput G c (EffectiveIteration.sourceDepth n)
              (Iteration.seedState (EffectiveIteration.sourceDepth n)).budget 0
              (Iteration.seedState (EffectiveIteration.sourceDepth n)).matrix)⟩ ∧
      level0Facts M G n c F Q P ∧
      blankBridge (S2 M G n c F Q P) (mcell .C) =
        ETHParameterScaleMachineInput.words (rp G n c (0 + 1)) 0 ∧
      blankBridge (S2 M G n c F Q P) (mcell .B) =
        ETHParameterScaleMachineInput.words (rp G n c (0 + 1)) 1 ∧
      blankBridge (S2 M G n c F Q P) (mcell .Y) =
        ETHParameterScaleMachineInput.words (rp G n c (0 + 1)) 2 ∧
      blankBridge (S2 M G n c F Q P) (mcell .E) =
        ETHParameterScaleMachineInput.words (rp G n c (0 + 1)) 5 := by
  obtain ⟨F, Q, P, t, ht, z, hrun, hout, hf, mC, mB, mY, mE, hgrow⟩ :=
    level0_round_growth M G n c hc W w₀ v₀ T22 hW
  have h1 := lift3_run (roundProgram M c W w₀ v₀) _ _ _ _ _ _ t hrun
  set X : H3 → List Bool := ext3 (ext (bank pEmb (S2 M G n c F Q P) z.stk)) with hX
  have hX0 : X srcOut = ProtectedFullBankBridgeScratch.actualPhysicalOutput G c
      (EffectiveIteration.sourceDepth n)
      (Iteration.seedState (EffectiveIteration.sourceDepth n)).budget 0
      (Iteration.seedState (EffectiveIteration.sourceDepth n)).matrix := by
    show bank pEmb (S2 M G n c F Q P) z.stk (pEmb (.inr MatrixTableInterlaceOuterJoin.secondOutput)) = _
    rw [bank_at]
    exact hout
  have hc0 := MatrixStage4ScalarPreparationOps.copy_run outSlots X rfl
  have e0 : outSlots 0 = srcOut := rfl
  have e1 : outSlots 1 = outCell := rfl
  have hXo : X outCell = [] := rfl
  rw [e0, e1, hX0, hXo, List.append_nil] at hc0
  set X1 := Function.update X outCell
    (ProtectedFullBankBridgeScratch.actualPhysicalOutput G c (EffectiveIteration.sourceDepth n)
      (Iteration.seedState (EffectiveIteration.sourceDepth n)).budget 0
      (Iteration.seedState (EffectiveIteration.sourceDepth n)).matrix) with hX1
  have hcl := WeightedRawWords.clear_run bridgeCells bridgeCells_inj X1
  have hfinal : BitMachineClearBank.cleared bridgeCells X1 =
      Function.update (ext3 (ext (blankBridge (S2 M G n c F Q P)))) outCell
        (ProtectedFullBankBridgeScratch.actualPhysicalOutput G c (EffectiveIteration.sourceDepth n)
          (Iteration.seedState (EffectiveIteration.sourceDepth n)).budget 0
          (Iteration.seedState (EffectiveIteration.sourceDepth n)).matrix) := by
    funext y
    unfold BitMachineClearBank.cleared
    rcases y with (h | h) | i
    · by_cases hb : ∃ y', pEmb y' = h
      · obtain ⟨y', rfl⟩ := hb
        have hin : ∃ i, bridgeCells i = (.inl (.inl (pEmb y')) : H3) :=
          ⟨(Fintype.equivFin BStack) y', by simp [bridgeCells]⟩
        rw [if_pos hin, Function.update_of_ne (by intro e; cases e)]
        show [] = blankBridge (S2 M G n c F Q P) (pEmb y')
        simp only [blankBridge]
        rw [if_pos ⟨y', rfl⟩]
      · have hin : ¬ ∃ i, bridgeCells i = (.inl (.inl h) : H3) := by
          rintro ⟨i, hi⟩
          exact hb ⟨_, Sum.inl.inj (Sum.inl.inj hi)⟩
        rw [if_neg hin, hX1, Function.update_of_ne (by intro e; cases e),
          Function.update_of_ne (by intro e; cases e)]
        show bank pEmb (S2 M G n c F Q P) z.stk h = blankBridge (S2 M G n c F Q P) h
        rw [bank_outside _ _ _ _ hb]
        simp only [blankBridge]
        rw [if_neg hb]
    · have hin : ¬ ∃ i, bridgeCells i = (.inl (.inr h) : H3) := by
        rintro ⟨i, hi⟩
        cases hi
      rw [if_neg hin, hX1, Function.update_of_ne (by intro e; cases e),
        Function.update_of_ne (by intro e; cases e)]
      rfl
    · have hin : ¬ ∃ j, bridgeCells j = (.inr i : H3) := by
        rintro ⟨j, hj⟩
        cases hj
      rw [if_neg hin, hX1]
      by_cases hi : (Sum.inr i : H3) = outCell
      · rw [hi, Function.update_self, Function.update_self]
      · rw [Function.update_of_ne hi, Function.update_of_ne hi]
        rfl
  rw [hfinal] at hcl
  have hsum : (∑ i : Fin nB, (X1 (bridgeCells i)).length) ≤
      ∑ i : Fin nB,
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
  obtain ⟨t2, ht2, q2⟩ := BitMachineRawSequence.runs copyOutP clearB
    BitMachineCopy.Label.scan 0 none none ((), none) ((), none) X X1 _ _ _ hc0 hcl
  obtain ⟨u, hu, q1⟩ := BitMachineRawSequence.runs (lift3 (roundProgram M c W w₀ v₀)) _
    _ _ _ _ _ _ _ _ _ _ _ h1 q2
  have hbC := mC
  have hbB := mB
  have hbY := mY
  have hbE := mE
  rw [bank_master] at hbC hbB hbY hbE
  have hbb : ∀ a : WeightedRawWords.Aux,
      blankBridge (S2 M G n c F Q P) (mcell a) = S2 M G n c F Q P (mcell a) := by
    intro a
    simp only [blankBridge]
    rw [if_neg (mcell_outside a)]
  refine ⟨F, Q, P, u, ?_, q1, hf, by rw [hbb]; exact hbC, by rw [hbb]; exact hbB,
    by rw [hbb]; exact hbY, by rw [hbb]; exact hbE⟩
  unfold nB at hsum ht2 ⊢
  omega

#print axioms level0_clean

end Clean

end
end EthInapproximability.CurrentPaper.Level0CleanRun
