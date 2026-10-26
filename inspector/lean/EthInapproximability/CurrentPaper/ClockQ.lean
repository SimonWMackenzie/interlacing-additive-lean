import EthInapproximability.CurrentPaper.ClockO
import EthInapproximability.CurrentPaper.ClockP

/-! Lane owner:b-weighted-level-11, unit 2, segment 5 with the OUTER halves of the preparation clocks
discharged (`ClockP`): `HB2Physical` from `hW`, the entry-clock premises on `T22zero`/`T22`, and polynomial
premises on the READY halves `readyBound`/`readyBoundJ` and on `dimsBound` only. -/

namespace EthInapproximability.CurrentPaper.ClockQ

open Turing BitMachineEncoding BitMachineStackEmbedding
open EthInapproximability.ParameterizedNP.GuardedSourceGraph
open WeightedLevel0Rows WeightedLevel0Persist WeightedLevel0Clean WeightedLevel0Target
open WeightedLevel0Ready WeightedLevel0WriterRun LevelJRows LevelJPersist LevelJClean LevelJReady
open LevelJMasters OuterLevel0Prep OuterLevel0Run LevelJPrep OuterLevel0Bridge LevelJBridge
open OuterLevel0Full NextMasterWords CostUpdateStages CostUpdateMachine CostUpdateEmbed
open Level0CostRound Level0CostRun Level0DimsRound Level0DimsClean RoundP CleanP ExitP StepP
open Level0Install
open FuelShell Emission HB2Machine ClockA ClockB ClockM ClockN ClockO ClockP

noncomputable section

set_option maxHeartbeats 3000000
set_option synthInstance.maxSize 200000
set_option synthInstance.maxHeartbeats 2000000
set_option maxRecDepth 16384


theorem prep_shape (R O Cx Kf Kw a T ex fx d M : ℕ) (ha : 1 ≤ a) (hT : 1 ≤ T) (hex : ex ≤ M)
    (hfx : fx ≤ M) (hd : 2 * (d + 1) ≤ M) (hR : R ≤ Cx * a ^ ex * T ^ fx)
    (hO : O ≤ Kf * (Kw * (a * T) ^ (d + 1)) ^ 2) :
    R + O + 1 ≤ (Cx + Kf * Kw ^ 2 + 1) * a ^ M * T ^ M := by
  have h1 : a ^ ex ≤ a ^ M := Nat.pow_le_pow_right ha hex
  have h2 : T ^ fx ≤ T ^ M := Nat.pow_le_pow_right hT hfx
  have h3 : ((a * T) ^ (d + 1)) ^ 2 ≤ a ^ M * T ^ M := by
    rw [← pow_mul, mul_pow]
    exact Nat.mul_le_mul (Nat.pow_le_pow_right ha (by omega)) (Nat.pow_le_pow_right hT (by omega))
  have hR' : R ≤ Cx * (a ^ M * T ^ M) :=
    le_trans hR (by rw [Nat.mul_assoc]; exact Nat.mul_le_mul_left _ (Nat.mul_le_mul h1 h2))
  have hO' : O ≤ (Kf * Kw ^ 2) * (a ^ M * T ^ M) := by
    have e : Kf * (Kw * (a * T) ^ (d + 1)) ^ 2 = (Kf * Kw ^ 2) * ((a * T) ^ (d + 1)) ^ 2 := by ring
    rw [e] at hO
    exact le_trans hO (Nat.mul_le_mul_left _ h3)
  have hP1 : 1 ≤ a ^ M * T ^ M := Nat.mul_pos (Nat.one_le_pow _ _ ha) (Nat.one_le_pow _ _ hT)
  have e : (Cx + Kf * Kw ^ 2 + 1) * a ^ M * T ^ M =
      Cx * (a ^ M * T ^ M) + (Kf * Kw ^ 2) * (a ^ M * T ^ M) + a ^ M * T ^ M := by ring
  rw [e]
  omega

theorem dims_shape (D Cx K a T ex fx M : ℕ) (ha : 1 ≤ a) (hT : 1 ≤ T) (hex : ex ≤ M) (hfx : fx ≤ M)
    (hD : D ≤ Cx * a ^ ex * T ^ fx) : D ≤ (Cx + K + 1) * a ^ M * T ^ M := by
  have h1 : a ^ ex ≤ a ^ M := Nat.pow_le_pow_right ha hex
  have h2 : T ^ fx ≤ T ^ M := Nat.pow_le_pow_right hT hfx
  have hD' : D ≤ Cx * (a ^ M * T ^ M) :=
    le_trans hD (by rw [Nat.mul_assoc]; exact Nat.mul_le_mul_left _ (Nat.mul_le_mul h1 h2))
  have e : (Cx + K + 1) * a ^ M * T ^ M = Cx * (a ^ M * T ^ M) + K * (a ^ M * T ^ M) + a ^ M * T ^ M := by ring
  rw [e]
  omega

/-- **Composition, outer preparation halves discharged.** -/
theorem hb2_physical_ready [Fintype BStack] [Fintype MatrixTableInterlaceProtectedBridge.Label]
    (c A d Δ : ℕ) (γ : ℚ) (hΔ : 0 < Δ) (hγ : 0 < γ) (hγone : γ ≤ 1)
    (hsource : 2 ^ 44 * (Δ : ℚ) / γ ≤ c)
    {LW VW : Type} [Fintype LW] [Fintype VW]
    (W : LW → TM2.Stmt (fun _ : H4 => Bool) LW VW) (w₀ : LW) (v₀ : VW) (Cx ex fx C22 : ℕ)
    (hprem : ∀ {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
      (G : EndpointGraph V E) (n : ℕ),
      G.SourceCommon γ Δ → n ≤ Fintype.card E →
      Fintype.card E ≤ A * n * EffectiveIteration.sourceDepth n ^ d →
      1 ≤ ETHTailGrowth.repetitions c A d n →
      ∃ T22 : ℕ,
        (∀ j, 1 ≤ j → j < WeightedRawWords.kValue (CutoffBitMachine.actualMachine c A d) n →
          Writer22SpecJ W w₀ v₀ T22 G c (EffectiveIteration.sourceDepth n)
            (yP G c (EffectiveIteration.sourceDepth n) j) j
            (MP G c (EffectiveIteration.sourceDepth n) j)
            (mSj (mb1 (CutoffBitMachine.actualMachine c A d) G n c) G c
              (EffectiveIteration.sourceDepth n) j)
            (MatrixMaterialization.rowMajor
              (PhysicalLevelRun.physRun G c (EffectiveIteration.sourceDepth n)
                (Iteration.seedState (EffectiveIteration.sourceDepth n)) j).matrix.entry)) ∧
        T22zero G n c ≤ (n + (EncodedGraph.encode (EncodedETHSource.serializeGraph G)).length + 1) ^ C22 +
          2 ^ (C22 * FinalPadding.exponent (ETHTailGrowth.repetitions c A d) n) ∧
        T22 ≤ (n + (EncodedGraph.encode (EncodedETHSource.serializeGraph G)).length + 1) ^ C22 +
          2 ^ (C22 * FinalPadding.exponent (ETHTailGrowth.repetitions c A d) n) ∧
        readyBound (CutoffBitMachine.actualMachine c A d) G n c ≤
          Cx * ((SourceOriginalBranchPackets.packet n
              (EncodedGraph.encode (EncodedETHSource.serializeGraph G))).length + 1) ^ ex *
            FinalPadding.tableSize (ETHTailGrowth.repetitions c A d) n ^ fx ∧
        NextDimsMachineTN.dimsBound (dx G n c) ≤
          Cx * ((SourceOriginalBranchPackets.packet n
              (EncodedGraph.encode (EncodedETHSource.serializeGraph G))).length + 1) ^ ex *
            FinalPadding.tableSize (ETHTailGrowth.repetitions c A d) n ^ fx ∧
        (∀ j, 1 ≤ j → j < WeightedRawWords.kValue (CutoffBitMachine.actualMachine c A d) n →
          readyBoundJ G c (EffectiveIteration.sourceDepth n) (yP G c (EffectiveIteration.sourceDepth n) j) j
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
  refine hb2_physical_entry c A d Δ γ hΔ hγ hγone hsource W w₀ v₀
    (Cx + ((1 + nS * BitMachineStackGrowth.perStep ETHScaleActualComplete.program) * Kp + 33554432 +
          2 * ClockC.binsConst + 4 * nS + 30) * Kw c A ^ 2 + 1)
    (ex + fx + 2 * (d + 1)) (ex + fx + 2 * (d + 1)) C22 ?_
  intro V E iV dV iE dE G n hcommon hlower hupper hrep
  obtain ⟨T22, hW, hT0, hT, hr0, hd0, hj⟩ := hprem G n hcommon hlower hupper hrep
  have ha : 1 ≤ (SourceOriginalBranchPackets.packet n
      (EncodedGraph.encode (EncodedETHSource.serializeGraph G))).length + 1 := by omega
  have hTa : 1 ≤ FinalPadding.tableSize (ETHTailGrowth.repetitions c A d) n := ClockH.table_pos _ n
  refine ⟨T22, hW, hT0, hT, ?_, ?_, ?_⟩
  · have hO : outerBound G n c ≤ ((1 + nS * BitMachineStackGrowth.perStep ETHScaleActualComplete.program) * Kp +
        33554432 + 2 * ClockC.binsConst + 4 * nS + 30) *
        (Kw c A * (((SourceOriginalBranchPackets.packet n
          (EncodedGraph.encode (EncodedETHSource.serializeGraph G))).length + 1) *
          FinalPadding.tableSize (ETHTailGrowth.repetitions c A d) n) ^ (d + 1)) ^ 2 :=
      ClockP.level_outerJ G c A d Δ n γ hcommon hlower hupper hrep 0 (Nat.zero_le _)
    exact prep_shape _ _ _ _ _ _ _ ex fx d _ ha hTa (by omega) (by omega) (by omega) hr0 hO
  · exact dims_shape _ Cx _ _ _ ex fx _ ha hTa (by omega) (by omega) hd0
  · intro j hj1 hjk
    obtain ⟨hrj, hdj⟩ := hj j hj1 hjk
    refine ⟨?_, dims_shape _ Cx _ _ _ ex fx _ ha hTa (by omega) (by omega) hdj⟩
    have hO := ClockP.level_outerJ G c A d Δ n γ hcommon hlower hupper hrep j (le_of_lt hjk)
    exact prep_shape _ _ _ _ _ _ _ ex fx d _ ha hTa (by omega) (by omega) (by omega) hrj hO

#print axioms prep_shape
#print axioms dims_shape
#print axioms hb2_physical_ready

end
end EthInapproximability.CurrentPaper.ClockQ
