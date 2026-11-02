import EthInapproximability.CurrentPaper.W12C1j

/-! Lane owner:b-weighted-level-12, segment 1, LEVEL `j`: the ready half `LevelJPrep.readyBoundJ`
(= owner-8's `cleanBoundJ` = level-row clock `boundJ` + the charged clear of the installed level bank `C1j`,
plus the rows/cols carrier terms) at every physical level `j < k` of the actual master region
`StepP.mSj (Level0Install.mb1 M G n c) …` (any machine `M`), explicitly polynomial in `a = |w| + 1` and
`T = tableSize`. -/

namespace EthInapproximability.CurrentPaper.W12ReadyJ

open EthInapproximability.ParameterizedNP.GuardedSourceGraph
open EntryClockPoly3 W12BoundJ

noncomputable section

set_option maxHeartbeats 3000000
set_option maxRecDepth 16384

variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

theorem ready_splitJ (G : EndpointGraph V E) (c b yb lv : ℕ) (Mx : Iteration.Matrix)
    (mS : WeightedRawWords.Aux → List Bool) :
    LevelJPrep.readyBoundJ G c b yb lv Mx mS =
      LevelJReady.cleanBoundJ G c b yb lv Mx mS +
        ((2 * ProtectedFullBankBridgeScratch.actualRows G c b yb lv Mx + 2) +
          ((2 * ProtectedFullBankBridgeScratch.actualCols G c b yb lv Mx + 2) +
            (ProtectedFullBankBridgeScratch.actualRows G c b yb lv Mx +
             ProtectedFullBankBridgeScratch.actualCols G c b yb lv Mx + 4) + 1) + 1) + 1 := rfl

/-- owner-8's `cleanBoundJ` splits literally; `ps3` is `perStep p2` as elaborated there. -/
theorem cleanJ_split : ∃ ps3 : ℕ, ∀ {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : EndpointGraph V E) (c b y lv : ℕ) (Mx : Iteration.Matrix) (mS : WeightedRawWords.Aux → List Bool),
    LevelJReady.cleanBoundJ G c b y lv Mx mS =
      LevelJClean.boundJ G c b y lv Mx +
        ((∑ k : Fin WeightedLevel0Clean.nClear,
            (LevelJRows.C1j G c b y lv Mx mS (WeightedLevel0Clean.clearCells k)).length) +
          WeightedLevel0Clean.nClear * (ps3 * LevelJClean.boundJ G c b y lv Mx) +
          WeightedLevel0Clean.nClear + 2) + 1 :=
  ⟨_, fun {V E} _ _ _ _ _ _ _ _ _ _ _ => rfl⟩

theorem mSj_N (M : BitMachine.Machine) (G : EndpointGraph V E) (n c b j : ℕ) :
    StepP.mSj (Level0Install.mb1 M G n c) G c b j .N = [] := by
  rw [StepP.mSj_ne _ _ _ _ _ _ (by intro h; cases h)]
  simp [Level0Install.mb1]

/-- The raw parameter word of a physical level is at most `6 · T · a`. -/
theorem wordSize_level (G : EndpointGraph V E) (c A d Δ n : ℕ) (γ : ℚ)
    (hcommon : G.SourceCommon γ Δ) (hlower : n ≤ Fintype.card E)
    (hupper : Fintype.card E ≤ A * n * EffectiveIteration.sourceDepth n ^ d)
    (hrep : 1 ≤ ETHTailGrowth.repetitions c A d n) (j : ℕ) (hj : j < ETHTailGrowth.repetitions c A d n) :
    ETHParameterScaleMachineInput.wordSize (Iteration.stepParameters G c (EffectiveIteration.sourceDepth n)
        (StepP.yP G c (EffectiveIteration.sourceDepth n) j) j (StepP.MP G c (EffectiveIteration.sourceDepth n) j)) ≤
      6 * (FinalPadding.tableSize (ETHTailGrowth.repetitions c A d) n *
        ((SourceOriginalBranchPackets.packet n
          (EncodedGraph.encode (EncodedETHSource.serializeGraph G))).length + 1)) := by
  let i : LI := ⟨V, E, G, c, EffectiveIteration.sourceDepth n, StepP.yP G c (EffectiveIteration.sourceDepth n) j, j,
    StepP.MP G c (EffectiveIteration.sourceDepth n) j⟩
  obtain ⟨-, -, -, -, -, -, -, -, hrx, hcy, -, -, -, -, -, -, -, -, hsc, hnd, hco, hed, -, -, -⟩ := sizes i
  have hname := naming_at_levels G c A d Δ n γ hcommon hlower hupper hrep j hj
  rw [EffectiveIteration.oneLevelBound, ← EffectiveIteration.nextScale_identity] at hname
  have hexp : FinalPadding.exponent (ETHTailGrowth.repetitions c A d) n =
      n / (2 * ETHTailGrowth.repetitions c A d n) := by
    unfold FinalPadding.exponent; rw [max_eq_right hrep]
  have hpk := ClockH.packet_ge n (EncodedGraph.encode (EncodedETHSource.serializeGraph G))
  have hU : U i ≤ FinalPadding.tableSize (ETHTailGrowth.repetitions c A d) n *
      ((SourceOriginalBranchPackets.packet n
        (EncodedGraph.encode (EncodedETHSource.serializeGraph G))).length + 1) := by
    unfold U FinalPadding.tableSize
    rw [hexp]
    refine Nat.mul_le_mul ((Nat.pow_le_pow_right (by decide) hname).trans
      (Nat.pow_le_pow_right (by decide) (by omega))) ?_
    show ell3 G + 1 ≤ _
    unfold ell3
    omega
  unfold ETHParameterScaleMachineInput.wordSize
  have h6 : (PL i).sourceConstant + (PL i).nextDepth + (PL i).cost + rxI i + cyI i + (PL i).edges ≤ 6 * U i := by
    omega
  exact h6.trans (Nat.mul_le_mul_left 6 hU)

/-- **Segment 1, level `j`: the ready half at every physical level `j < k`, explicitly polynomial.**
`Cp`, `ps`, `ps3` absolute; `KE c A` from owner-11's `ClockK`; `a`, `T`, `Z` written out. -/
theorem readyJ_level : ∃ Cp ps ps3 : ℕ, ∀ (M : BitMachine.Machine) {V E : Type} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E] (G : EndpointGraph V E) (c A d Δ n : ℕ) (γ : ℚ),
    G.SourceCommon γ Δ → n ≤ Fintype.card E →
    Fintype.card E ≤ A * n * EffectiveIteration.sourceDepth n ^ d →
    1 ≤ ETHTailGrowth.repetitions c A d n →
    ∀ j, j < ETHTailGrowth.repetitions c A d n →
    LevelJPrep.readyBoundJ G c (EffectiveIteration.sourceDepth n) (StepP.yP G c (EffectiveIteration.sourceDepth n) j) j
        (StepP.MP G c (EffectiveIteration.sourceDepth n) j)
        (StepP.mSj (Level0Install.mb1 M G n c) G c (EffectiveIteration.sourceDepth n) j) ≤
      (1 + WeightedLevel0Clean.nClear * ps3) *
        ((1 + 9 * ps) * (2 * ((SourceOriginalBranchPackets.packet n
            (EncodedGraph.encode (EncodedETHSource.serializeGraph G))).length + 1) ^ Cp *
          FinalPadding.tableSize (ETHTailGrowth.repetitions c A d) n ^ Cp) + 13 +
        W12RowTime.Krow * (ClockK.KE c A * ((((SourceOriginalBranchPackets.packet n
            (EncodedGraph.encode (EncodedETHSource.serializeGraph G))).length + 1) ^ (d + 1) *
            FinalPadding.tableSize (ETHTailGrowth.repetitions c A d) n) *
          (((SourceOriginalBranchPackets.packet n
            (EncodedGraph.encode (EncodedETHSource.serializeGraph G))).length + 1) ^ (d + 1) *
            FinalPadding.tableSize (ETHTailGrowth.repetitions c A d) n)) + 1) ^ 9) +
      WeightedLevel0Clean.nClear *
        (7 * (FinalPadding.tableSize (ETHTailGrowth.repetitions c A d) n *
          ((SourceOriginalBranchPackets.packet n
            (EncodedGraph.encode (EncodedETHSource.serializeGraph G))).length + 1))) +
      WeightedLevel0Clean.nClear + 3 + (24 * FinalPadding.tableSize (ETHTailGrowth.repetitions c A d) n + 11) := by
  obtain ⟨Cp, ps, hB⟩ := boundJ_level
  obtain ⟨ps3, hps3⟩ := cleanJ_split
  refine ⟨Cp, ps, ps3, fun M {V E} _ _ _ _ G c A d Δ n γ hcommon hlower hupper hrep j hj => ?_⟩
  have hb := hB G c A d Δ n γ hcommon hlower hupper hrep j hj
  have hsum := W12C1j.C1j_sum_le G c (EffectiveIteration.sourceDepth n)
    (StepP.yP G c (EffectiveIteration.sourceDepth n) j) j (StepP.MP G c (EffectiveIteration.sourceDepth n) j)
    (StepP.mSj (Level0Install.mb1 M G n c) G c (EffectiveIteration.sourceDepth n) j)
    (mSj_N M G n c (EffectiveIteration.sourceDepth n) j)
  have hws := wordSize_level G c A d Δ n γ hcommon hlower hupper hrep j hj
  have hpk := ClockH.packet_ge n (EncodedGraph.encode (EncodedETHSource.serializeGraph G))
  have hT1 : 1 ≤ FinalPadding.tableSize (ETHTailGrowth.repetitions c A d) n := ClockH.table_pos _ n
  have hTa : (EncodedGraph.encode (EncodedETHSource.serializeGraph G)).length + 1 ≤
      FinalPadding.tableSize (ETHTailGrowth.repetitions c A d) n *
        ((SourceOriginalBranchPackets.packet n
          (EncodedGraph.encode (EncodedETHSource.serializeGraph G))).length + 1) :=
    (show (EncodedGraph.encode (EncodedETHSource.serializeGraph G)).length + 1 ≤
      (SourceOriginalBranchPackets.packet n
        (EncodedGraph.encode (EncodedETHSource.serializeGraph G))).length + 1 by omega).trans
      (Nat.le_mul_of_pos_left _ hT1)
  have hsum' := hsum.trans (Nat.mul_le_mul_left WeightedLevel0Clean.nClear
    (show ETHParameterScaleMachineInput.wordSize (Iteration.stepParameters G c (EffectiveIteration.sourceDepth n)
        (StepP.yP G c (EffectiveIteration.sourceDepth n) j) j (StepP.MP G c (EffectiveIteration.sourceDepth n) j)) +
        (EncodedGraph.encode (EncodedETHSource.serializeGraph G)).length + 1 ≤
      7 * (FinalPadding.tableSize (ETHTailGrowth.repetitions c A d) n *
          ((SourceOriginalBranchPackets.packet n
            (EncodedGraph.encode (EncodedETHSource.serializeGraph G))).length + 1)) by omega))
  have hact := ClockF.level_actual G c A d Δ n γ hcommon hlower hupper hrep j hj
  rw [ready_splitJ, hps3]
  generalize LevelJClean.boundJ G c (EffectiveIteration.sourceDepth n)
    (StepP.yP G c (EffectiveIteration.sourceDepth n) j) j (StepP.MP G c (EffectiveIteration.sourceDepth n) j) = x
    at hb ⊢
  generalize ((1 + 9 * ps) * (2 * ((SourceOriginalBranchPackets.packet n
            (EncodedGraph.encode (EncodedETHSource.serializeGraph G))).length + 1) ^ Cp *
          FinalPadding.tableSize (ETHTailGrowth.repetitions c A d) n ^ Cp) + 13 +
        W12RowTime.Krow * (ClockK.KE c A * ((((SourceOriginalBranchPackets.packet n
            (EncodedGraph.encode (EncodedETHSource.serializeGraph G))).length + 1) ^ (d + 1) *
            FinalPadding.tableSize (ETHTailGrowth.repetitions c A d) n) *
          (((SourceOriginalBranchPackets.packet n
            (EncodedGraph.encode (EncodedETHSource.serializeGraph G))).length + 1) ^ (d + 1) *
            FinalPadding.tableSize (ETHTailGrowth.repetitions c A d) n)) + 1) ^ 9) = B at hb ⊢
  have hm : WeightedLevel0Clean.nClear * (ps3 * x) ≤ WeightedLevel0Clean.nClear * (ps3 * B) :=
    Nat.mul_le_mul_left _ (Nat.mul_le_mul_left ps3 hb)
  have e : (1 + WeightedLevel0Clean.nClear * ps3) * B = B + WeightedLevel0Clean.nClear * (ps3 * B) := by ring
  rw [e]
  omega

#print axioms ready_splitJ
#print axioms cleanJ_split
#print axioms mSj_N
#print axioms wordSize_level
#print axioms readyJ_level

end
end EthInapproximability.CurrentPaper.W12ReadyJ
