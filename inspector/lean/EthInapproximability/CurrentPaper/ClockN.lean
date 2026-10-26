import EthInapproximability.CurrentPaper.ClockM

/-! Lane owner:b-weighted-level-11, unit 2, segment 5 (reduced composition): `HB2Physical` for ONE
fixed machine (owner-10's `hb2Machine (actualMachine c A d) c W₀ w₀₀ v₀₀ W w₀ v₀`, through
`ClockB.hb2_physical_source`) from the endpoint source constants, the writer-22 specs `hW₀`, `hW`,
the entry-clock polynomial premises on `T22₀`, `T22` in the exact form
`(n + |enc G| + 1)^C + 2^(C p)`, `p = FinalPadding.exponent`, and polynomial premises on the
two remaining round-clock components (`prepBound`/`prepBoundJ`, `dimsBound`) ONLY. -/

namespace EthInapproximability.CurrentPaper.ClockN

open Turing BitMachineEncoding BitMachineStackEmbedding
open EthInapproximability.ParameterizedNP.GuardedSourceGraph
open WeightedLevel0Rows WeightedLevel0Persist WeightedLevel0Clean WeightedLevel0Target
open WeightedLevel0Ready WeightedLevel0WriterRun LevelJRows LevelJPersist LevelJClean LevelJReady
open LevelJMasters OuterLevel0Prep OuterLevel0Run LevelJPrep OuterLevel0Bridge LevelJBridge
open OuterLevel0Full NextMasterWords CostUpdateStages CostUpdateMachine CostUpdateEmbed
open Level0CostRound Level0CostRun Level0DimsRound Level0DimsClean RoundP CleanP ExitP StepP
open Level0Install
open FuelShell Emission HB2Machine ClockA ClockB ClockM

noncomputable section

set_option maxHeartbeats 3000000

variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- One round clock (`1 ≤ j < k` in use; stated for every `j < k`). -/
theorem round_le [Fintype BStack] [Fintype MatrixTableInterlaceProtectedBridge.Label]
    (G : EndpointGraph V E) (c A d Δ n : ℕ) (γ : ℚ)
    (hcommon : G.SourceCommon γ Δ) (hlower : n ≤ Fintype.card E)
    (hupper : Fintype.card E ≤ A * n * EffectiveIteration.sourceDepth n ^ d)
    (hrep : 1 ≤ ETHTailGrowth.repetitions c A d n) (Cx ex fx C22 T22 : ℕ)
    (mb : WeightedRawWords.Aux → List Bool) (j : ℕ)
    (hj : j < ETHTailGrowth.repetitions c A d n)
    (hT22 : T22 ≤ (n + (EncodedGraph.encode (EncodedETHSource.serializeGraph G)).length + 1) ^ C22 +
      2 ^ (C22 * FinalPadding.exponent (ETHTailGrowth.repetitions c A d) n))
    (hprep : prepBoundJ G c (EffectiveIteration.sourceDepth n) (yP G c (EffectiveIteration.sourceDepth n) j) j
        (MP G c (EffectiveIteration.sourceDepth n) j) (mSj mb G c (EffectiveIteration.sourceDepth n) j) ≤
      Cx * ((SourceOriginalBranchPackets.packet n
          (EncodedGraph.encode (EncodedETHSource.serializeGraph G))).length + 1) ^ ex *
        FinalPadding.tableSize (ETHTailGrowth.repetitions c A d) n ^ fx)
    (hdims : NextDimsMachineTN.dimsBound (dxJ G c (EffectiveIteration.sourceDepth n)
        (yP G c (EffectiveIteration.sourceDepth n) j) j (MP G c (EffectiveIteration.sourceDepth n) j)) ≤
      Cx * ((SourceOriginalBranchPackets.packet n
          (EncodedGraph.encode (EncodedETHSource.serializeGraph G))).length + 1) ^ ex *
        FinalPadding.tableSize (ETHTailGrowth.repetitions c A d) n ^ fx) :
    roundBoundP G c (EffectiveIteration.sourceDepth n) j mb
        (MatrixMaterialization.rowMajor
          (PhysicalLevelRun.physRun G c (EffectiveIteration.sourceDepth n)
            (Iteration.seedState (EffectiveIteration.sourceDepth n)) j).matrix.entry) T22 ≤
      Kround c A Cx * (((SourceOriginalBranchPackets.packet n
          (EncodedGraph.encode (EncodedETHSource.serializeGraph G))).length + 1) *
        FinalPadding.tableSize (ETHTailGrowth.repetitions c A d) n) ^ mexp d ex fx C22 := by
  obtain ⟨hY, hexfx, hC22, hTY, hZ36, hcost⟩ :=
    level_pieces G c A d Δ n γ hcommon hlower hupper hrep ex fx C22 j hj
  set b := EffectiveIteration.sourceDepth n with hb
  set a := (SourceOriginalBranchPackets.packet n
    (EncodedGraph.encode (EncodedETHSource.serializeGraph G))).length + 1 with ha
  set T := FinalPadding.tableSize (ETHTailGrowth.repetitions c A d) n with hT
  set Ym := (a * T) ^ mexp d ex fx C22 with hYm
  set Z := a ^ (d + 1) * T with hZ
  have hP : prepBoundJ G c b (yP G c b j) j (MP G c b j) (mSj mb G c b j) ≤ Cx * Ym :=
    calc _ ≤ Cx * a ^ ex * T ^ fx := hprep
      _ = Cx * (a ^ ex * T ^ fx) := by ring
      _ ≤ Cx * Ym := Nat.mul_le_mul_left _ hexfx
  have hd : NextDimsMachineTN.dimsBound (dxJ G c b (yP G c b j) j (MP G c b j)) ≤ Cx * Ym :=
    calc _ ≤ Cx * a ^ ex * T ^ fx := hdims
      _ = Cx * (a ^ ex * T ^ fx) := by ring
      _ ≤ Cx * Ym := Nat.mul_le_mul_left _ hexfx
  have hT22' : T22 ≤ 2 * Ym :=
    calc T22 ≤ 2 * a ^ C22 * T ^ C22 := ClockH.translate_packet G _ n C22 T22 hT22
      _ = 2 * (a ^ C22 * T ^ C22) := by ring
      _ ≤ 2 * Ym := Nat.mul_le_mul_left _ hC22
  have hc : costBound (Parameters.scale (Pj G c b (yP G c b j) j (MP G c b j))) b c
      (Parameters.bins (Pj G c b (yP G c b j) j (MP G c b j))) (Fintype.card E)
      (Pj G c b (yP G c b j) j (MP G c b j)).cost ≤ Kcost c A * Ym := hcost
  have hb' : ProtectedFullBankBridgeScratch.actualPhysicalBudget G c b (yP G c b j) j (MP G c b j) ≤
      (ProtectedBudgetNormalizationScratch.coefficient * ClockK.KE c A ^ 18) * Ym :=
    calc _ ≤ ProtectedBudgetNormalizationScratch.coefficient * ClockK.KE c A ^ 18 * Z ^ 36 :=
          ClockK.level_budget G c A d Δ n γ hcommon hlower hupper hrep j hj
      _ ≤ _ := Nat.mul_le_mul_left _ hZ36
  have hmw : (MatrixMaterialization.rowMajor
      (PhysicalLevelRun.physRun G c b (Iteration.seedState b) j).matrix.entry).length ≤ 4 * Ym := by
    have : (MatrixMaterialization.rowMajor
        (PhysicalLevelRun.physRun G c b (Iteration.seedState b) j).matrix.entry).length < 4 * T :=
      ClockE.level_mw G c A d Δ n γ hcommon hlower hupper hrep j (le_of_lt hj)
    omega
  have ho : (ProtectedFullBankBridgeScratch.actualPhysicalOutput G c b (yP G c b j) j (MP G c b j)).length ≤
      4 * Ym := by
    have : (ProtectedFullBankBridgeScratch.actualPhysicalOutput G c b (yP G c b j) j
        (MP G c b j)).length < 4 * T :=
      ClockE.level_output G c A d Δ n γ hcommon hlower hupper hrep j hj
    omega
  have hS : (∑ i : Fin Level0CleanRun.nB,
        (((ProtectedFullBankBridgeScratch.actualPhysicalStart G c b (yP G c b j) j (MP G c b j)).stk
              ((Fintype.equivFin BStack).symm i)).length +
          BitMachineStackGrowth.perStep bridgeH *
            ProtectedFullBankBridgeScratch.actualPhysicalBudget G c b (yP G c b j) j (MP G c b j))) ≤
      (Level0CleanRun.nB * (ClockK.KE c A + BitMachineStackGrowth.perStep bridgeH *
          (ProtectedBudgetNormalizationScratch.coefficient * ClockK.KE c A ^ 18))) * Ym :=
    calc _ ≤ _ := ClockL.level_stacks G c A d Δ n γ hcommon hlower hupper hrep j hj
      _ ≤ _ := Nat.mul_le_mul_left _ hZ36
  have hn : Level0CleanRun.nB ≤ Level0CleanRun.nB * Ym := Nat.le_mul_of_pos_right _ hY
  have key := round_arith _ _ _ _ _ _ _ _ _ Ym Cx (Kcost c A)
    (ProtectedBudgetNormalizationScratch.coefficient * ClockK.KE c A ^ 18)
    (Level0CleanRun.nB * (ClockK.KE c A + BitMachineStackGrowth.perStep bridgeH *
          (ProtectedBudgetNormalizationScratch.coefficient * ClockK.KE c A ^ 18)))
    hP hT22' hc hd hb' hmw ho hS hn hY
  unfold roundBoundP
  exact key

/-- The level-0 round clock. -/
theorem level0_le [Fintype BStack] [Fintype MatrixTableInterlaceProtectedBridge.Label]
    (M : BitMachine.Machine) (G : EndpointGraph V E) (c A d Δ n : ℕ) (γ : ℚ)
    (hcommon : G.SourceCommon γ Δ) (hlower : n ≤ Fintype.card E)
    (hupper : Fintype.card E ≤ A * n * EffectiveIteration.sourceDepth n ^ d)
    (hrep : 1 ≤ ETHTailGrowth.repetitions c A d n) (Cx ex fx C22 T22₀ : ℕ)
    (hT22 : T22₀ ≤ (n + (EncodedGraph.encode (EncodedETHSource.serializeGraph G)).length + 1) ^ C22 +
      2 ^ (C22 * FinalPadding.exponent (ETHTailGrowth.repetitions c A d) n))
    (hprep : prepBound M G n c ≤
      Cx * ((SourceOriginalBranchPackets.packet n
          (EncodedGraph.encode (EncodedETHSource.serializeGraph G))).length + 1) ^ ex *
        FinalPadding.tableSize (ETHTailGrowth.repetitions c A d) n ^ fx)
    (hdims : NextDimsMachineTN.dimsBound (dx G n c) ≤
      Cx * ((SourceOriginalBranchPackets.packet n
          (EncodedGraph.encode (EncodedETHSource.serializeGraph G))).length + 1) ^ ex *
        FinalPadding.tableSize (ETHTailGrowth.repetitions c A d) n ^ fx) :
    level0BoundP M G n c T22₀ ≤
      Kround c A Cx * (((SourceOriginalBranchPackets.packet n
          (EncodedGraph.encode (EncodedETHSource.serializeGraph G))).length + 1) *
        FinalPadding.tableSize (ETHTailGrowth.repetitions c A d) n) ^ mexp d ex fx C22 := by
  obtain ⟨hY, hexfx, hC22, hTY, hZ36, hcost⟩ :=
    level_pieces G c A d Δ n γ hcommon hlower hupper hrep ex fx C22 0 hrep
  set b := EffectiveIteration.sourceDepth n with hb
  set a := (SourceOriginalBranchPackets.packet n
    (EncodedGraph.encode (EncodedETHSource.serializeGraph G))).length + 1 with ha
  set T := FinalPadding.tableSize (ETHTailGrowth.repetitions c A d) n with hT
  set Ym := (a * T) ^ mexp d ex fx C22 with hYm
  set Z := a ^ (d + 1) * T with hZ
  have hP : prepBound M G n c ≤ Cx * Ym :=
    calc _ ≤ Cx * a ^ ex * T ^ fx := hprep
      _ = Cx * (a ^ ex * T ^ fx) := by ring
      _ ≤ Cx * Ym := Nat.mul_le_mul_left _ hexfx
  have hd : NextDimsMachineTN.dimsBound (dx G n c) ≤ Cx * Ym :=
    calc _ ≤ Cx * a ^ ex * T ^ fx := hdims
      _ = Cx * (a ^ ex * T ^ fx) := by ring
      _ ≤ Cx * Ym := Nat.mul_le_mul_left _ hexfx
  have hT22' : T22₀ ≤ 2 * Ym :=
    calc T22₀ ≤ 2 * a ^ C22 * T ^ C22 := ClockH.translate_packet G _ n C22 T22₀ hT22
      _ = 2 * (a ^ C22 * T ^ C22) := by ring
      _ ≤ 2 * Ym := Nat.mul_le_mul_left _ hC22
  have hc : costBound (Parameters.scale (P0 G n c)) b c (Parameters.bins (P0 G n c)) (Fintype.card E)
      (Iteration.seedState b).budget ≤ Kcost c A * Ym := hcost
  have hb' : ProtectedFullBankBridgeScratch.actualPhysicalBudget G c b (Iteration.seedState b).budget 0
      (Iteration.seedState b).matrix ≤
      (ProtectedBudgetNormalizationScratch.coefficient * ClockK.KE c A ^ 18) * Ym :=
    calc _ ≤ ProtectedBudgetNormalizationScratch.coefficient * ClockK.KE c A ^ 18 * Z ^ 36 :=
          ClockK.level_budget G c A d Δ n γ hcommon hlower hupper hrep 0 hrep
      _ ≤ _ := Nat.mul_le_mul_left _ hZ36
  have ho : (ProtectedFullBankBridgeScratch.actualPhysicalOutput G c b (Iteration.seedState b).budget 0
      (Iteration.seedState b).matrix).length ≤ 4 * Ym := by
    have : (ProtectedFullBankBridgeScratch.actualPhysicalOutput G c b (Iteration.seedState b).budget 0
        (Iteration.seedState b).matrix).length < 4 * T :=
      ClockE.level_output G c A d Δ n γ hcommon hlower hupper hrep 0 hrep
    omega
  have hS : (∑ i : Fin Level0CleanRun.nB,
        (((ProtectedFullBankBridgeScratch.actualPhysicalStart G c b (Iteration.seedState b).budget 0
            (Iteration.seedState b).matrix).stk ((Fintype.equivFin BStack).symm i)).length +
          BitMachineStackGrowth.perStep bridgeH *
            ProtectedFullBankBridgeScratch.actualPhysicalBudget G c b (Iteration.seedState b).budget 0
              (Iteration.seedState b).matrix)) ≤
      (Level0CleanRun.nB * (ClockK.KE c A + BitMachineStackGrowth.perStep bridgeH *
          (ProtectedBudgetNormalizationScratch.coefficient * ClockK.KE c A ^ 18))) * Ym :=
    calc _ ≤ _ := ClockL.level_stacks G c A d Δ n γ hcommon hlower hupper hrep 0 hrep
      _ ≤ _ := Nat.mul_le_mul_left _ hZ36
  have hn : Level0CleanRun.nB ≤ Level0CleanRun.nB * Ym := Nat.le_mul_of_pos_right _ hY
  have key := level0_arith _ _ _ _ _ _ _ _ Ym Cx (Kcost c A)
    (ProtectedBudgetNormalizationScratch.coefficient * ClockK.KE c A ^ 18)
    (Level0CleanRun.nB * (ClockK.KE c A + BitMachineStackGrowth.perStep bridgeH *
          (ProtectedBudgetNormalizationScratch.coefficient * ClockK.KE c A ^ 18)))
    hP hT22' hc hd hb' ho hS hn hY
  unfold level0BoundP
  exact key

/-- **Reduced composition.** `HB2Physical` for ONE fixed machine from the endpoint source
constants, the writer-22 specs, the entry-clock polynomial premises on `T22₀`, `T22`, and
polynomial premises on `prepBound`/`prepBoundJ` and `dimsBound` only. The machine is owner-10's
`hb2Machine (actualMachine c A d) c W₀ w₀₀ v₀₀ W w₀ v₀`; the constants are
`C₂ = 2 (Kround c A Cx + 2c + 2A + 66) + 400`, `E₂ = mexp + d + 2`, `F₂ = mexp + 2`. -/
theorem hb2_physical_components [Fintype BStack] [Fintype MatrixTableInterlaceProtectedBridge.Label]
    (c A d Δ : ℕ) (γ : ℚ) (hΔ : 0 < Δ) (hγ : 0 < γ) (hγone : γ ≤ 1)
    (hsource : 2 ^ 44 * (Δ : ℚ) / γ ≤ c)
    {LW₀ VW₀ LW VW : Type} [Fintype LW₀] [Fintype VW₀] [Fintype LW] [Fintype VW]
    (W₀ : LW₀ → TM2.Stmt (fun _ : HStack => Bool) LW₀ VW₀) (w₀₀ : LW₀) (v₀₀ : VW₀)
    (W : LW → TM2.Stmt (fun _ : H4 => Bool) LW VW) (w₀ : LW) (v₀ : VW) (Cx ex fx C22 : ℕ)
    (hprem : ∀ {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
      (G : EndpointGraph V E) (n : ℕ),
      G.SourceCommon γ Δ → n ≤ Fintype.card E →
      Fintype.card E ≤ A * n * EffectiveIteration.sourceDepth n ^ d →
      1 ≤ ETHTailGrowth.repetitions c A d n →
      ∃ T22₀ T22 : ℕ,
        Writer22Spec (CutoffBitMachine.actualMachine c A d) W₀ w₀₀ v₀₀ T22₀ G n c ∧
        (∀ j, 1 ≤ j → j < WeightedRawWords.kValue (CutoffBitMachine.actualMachine c A d) n →
          Writer22SpecJ W w₀ v₀ T22 G c (EffectiveIteration.sourceDepth n)
            (yP G c (EffectiveIteration.sourceDepth n) j) j
            (MP G c (EffectiveIteration.sourceDepth n) j)
            (mSj (mb1 (CutoffBitMachine.actualMachine c A d) G n c) G c
              (EffectiveIteration.sourceDepth n) j)
            (MatrixMaterialization.rowMajor
              (PhysicalLevelRun.physRun G c (EffectiveIteration.sourceDepth n)
                (Iteration.seedState (EffectiveIteration.sourceDepth n)) j).matrix.entry)) ∧
        T22₀ ≤ (n + (EncodedGraph.encode (EncodedETHSource.serializeGraph G)).length + 1) ^ C22 +
          2 ^ (C22 * FinalPadding.exponent (ETHTailGrowth.repetitions c A d) n) ∧
        T22 ≤ (n + (EncodedGraph.encode (EncodedETHSource.serializeGraph G)).length + 1) ^ C22 +
          2 ^ (C22 * FinalPadding.exponent (ETHTailGrowth.repetitions c A d) n) ∧
        prepBound (CutoffBitMachine.actualMachine c A d) G n c ≤
          Cx * ((SourceOriginalBranchPackets.packet n
              (EncodedGraph.encode (EncodedETHSource.serializeGraph G))).length + 1) ^ ex *
            FinalPadding.tableSize (ETHTailGrowth.repetitions c A d) n ^ fx ∧
        NextDimsMachineTN.dimsBound (dx G n c) ≤
          Cx * ((SourceOriginalBranchPackets.packet n
              (EncodedGraph.encode (EncodedETHSource.serializeGraph G))).length + 1) ^ ex *
            FinalPadding.tableSize (ETHTailGrowth.repetitions c A d) n ^ fx ∧
        (∀ j, 1 ≤ j → j < WeightedRawWords.kValue (CutoffBitMachine.actualMachine c A d) n →
          prepBoundJ G c (EffectiveIteration.sourceDepth n) (yP G c (EffectiveIteration.sourceDepth n) j) j
              (MP G c (EffectiveIteration.sourceDepth n) j)
              (mSj (mb1 (CutoffBitMachine.actualMachine c A d) G n c) G c
                (EffectiveIteration.sourceDepth n) j) ≤
            Cx * ((SourceOriginalBranchPackets.packet n
                (EncodedGraph.encode (EncodedETHSource.serializeGraph G))).length + 1) ^ ex *
              FinalPadding.tableSize (ETHTailGrowth.repetitions c A d) n ^ fx ∧
          NextDimsMachineTN.dimsBound (dxJ G c (EffectiveIteration.sourceDepth n)
              (yP G c (EffectiveIteration.sourceDepth n) j) j (MP G c (EffectiveIteration.sourceDepth n) j)) ≤
            Cx * ((SourceOriginalBranchPackets.packet n
                (EncodedGraph.encode (EncodedETHSource.serializeGraph G))).length + 1) ^ ex *
              FinalPadding.tableSize (ETHTailGrowth.repetitions c A d) n ^ fx)) :
    PhysicalLevelRun.HB2Physical c A d Δ γ := by
  refine ClockB.hb2_physical_source c A d Δ γ hΔ hγ hγone hsource W₀ w₀₀ v₀₀ W w₀ v₀
    (Kround c A Cx) (mexp d ex fx C22) (mexp d ex fx C22) ?_
  intro V E iV dV iE dE G n hcommon hlower hupper hrep
  obtain ⟨T22₀, T22, hW₀, hW, hT0, hT, hp0, hd0, hj⟩ := hprem G n hcommon hlower hupper hrep
  have hpow : Kround c A Cx * (((SourceOriginalBranchPackets.packet n
          (EncodedGraph.encode (EncodedETHSource.serializeGraph G))).length + 1) *
        FinalPadding.tableSize (ETHTailGrowth.repetitions c A d) n) ^ mexp d ex fx C22 =
      Kround c A Cx * ((SourceOriginalBranchPackets.packet n
          (EncodedGraph.encode (EncodedETHSource.serializeGraph G))).length + 1) ^ mexp d ex fx C22 *
        FinalPadding.tableSize (ETHTailGrowth.repetitions c A d) n ^ mexp d ex fx C22 := by
    rw [mul_pow]; ring
  refine ⟨T22₀, T22, Kround c A Cx * (((SourceOriginalBranchPackets.packet n
          (EncodedGraph.encode (EncodedETHSource.serializeGraph G))).length + 1) *
        FinalPadding.tableSize (ETHTailGrowth.repetitions c A d) n) ^ mexp d ex fx C22,
    hW₀, hW, ?_, ?_, le_of_eq hpow⟩
  · intro j hj1 hjk
    obtain ⟨hpj, hdj⟩ := hj j hj1 hjk
    exact round_le G c A d Δ n γ hcommon hlower hupper hrep Cx ex fx C22 T22
      (mb1 (CutoffBitMachine.actualMachine c A d) G n c) j hjk hT hpj hdj
  · rw [← hpow]
    exact level0_le (CutoffBitMachine.actualMachine c A d) G c A d Δ n γ hcommon hlower hupper hrep
      Cx ex fx C22 T22₀ hT0 hp0 hd0

#print axioms round_le
#print axioms level0_le
#print axioms hb2_physical_components

end
end EthInapproximability.CurrentPaper.ClockN
