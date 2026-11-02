import EthInapproximability.CurrentPaper.ClockM
import EthInapproximability.CurrentPaper.ETHParameterScalePolynomial

/-! Lane owner:b-weighted-level-11, unit 2, segment 4b-ii-6 (d, first half): the OUTER half of the
level preparation clocks, `OuterLevel0Prep.outerBound` (level 0) and `LevelJPrep.outerBoundJ`
(level `j`): the admitted scale machine `ETHScaleActualComplete.totalBound` (majorized by the
admitted `ETHScalePolynomialClock.totalBound_le_polynomial`, a quadratic in the widest raw word),
the four charged copies and the charged clear of the scale region. At every physical level `j < k`
both are `≤ Ko · Kw² · Ym` (`Ym = ((|w|+1) T)^mexp`), so `prepBound`/`prepBoundJ` reduce to the ready
halves `readyBound`/`readyBoundJ`. -/

namespace EthInapproximability.CurrentPaper.ClockP

open Turing BitMachineEncoding BitMachineStackEmbedding
open EthInapproximability.ParameterizedNP.GuardedSourceGraph
open WeightedLevel0Rows WeightedLevel0Persist WeightedLevel0Clean WeightedLevel0Target
open WeightedLevel0Ready WeightedLevel0WriterRun LevelJRows LevelJPersist LevelJClean LevelJReady
open LevelJMasters OuterLevel0Prep OuterLevel0Run LevelJPrep OuterLevel0Bridge LevelJBridge
open OuterLevel0Full NextMasterWords CostUpdateStages CostUpdateMachine CostUpdateEmbed
open Level0CostRound Level0CostRun Level0DimsRound Level0DimsClean RoundP CleanP ExitP StepP
open Level0Install
open ClockM

noncomputable section

set_option maxHeartbeats 3000000

/-- Opaque names for the closed controller constants of the scale clock (never evaluated). -/
irreducible_def PSc : ℕ := BitMachineStackGrowth.perStep ScaleFinalScratch.program
irreducible_def CCc : ℕ := ScaleFinalScratch.cleanupCount
irreducible_def FSc : ℕ := ScaleFinalScratch.floorSize
irreducible_def UBc : ℕ := UnaryBinaryEncoding.coefficient

/-- The quadratic constant of the admitted scale clock. -/
def Kp : ℕ := 3 * (UBc + 8) + 53 + (1 + CCc * PSc) * (UBc + 2 * FSc + 19) + CCc + 3

theorem polyClock_arith (w K F CC PS : ℕ) :
    (3 * (2 * w + 2 + (K + 6) * (w + 1) ^ 2) + 20 * w + 33) +
      ((1 + CC * PS) * ((2 * w + 2 + (K + 6) * (w + 1) ^ 2) + w + 2 * F + 10) + CC + 2) + 1 ≤
    (3 * (K + 8) + 53 + (1 + CC * PS) * (K + 2 * F + 19) + CC + 3) * (w + 1) ^ 2 := by
  generalize hX : (w + 1) ^ 2 = X
  have hX1 : w + 1 ≤ X := by
    rw [← hX, pow_two]; exact Nat.le_mul_of_pos_right _ (by omega)
  generalize hM : 1 + CC * PS = M
  have hFX : F ≤ F * X := Nat.le_mul_of_pos_right _ (by omega)
  have hCX : CC ≤ CC * X := Nat.le_mul_of_pos_right _ (by omega)
  have hin : (2 * w + 2 + (K + 6) * X) + w + 2 * F + 10 ≤ (K + 2 * F + 19) * X := by
    have e : (K + 2 * F + 19) * X = (K + 6) * X + 2 * (F * X) + 13 * X := by ring
    rw [e]; omega
  have hMM := Nat.mul_le_mul_left M hin
  have e : (3 * (K + 8) + 53 + M * (K + 2 * F + 19) + CC + 3) * X =
      3 * ((K + 6) * X) + 59 * X + M * ((K + 2 * F + 19) * X) + CC * X + 3 * X := by ring
  rw [e]
  omega

theorem polyClock_le (w : ℕ) : ETHScalePolynomialClock.polynomialClock w ≤ Kp * (w + 1) ^ 2 := by
  rw [ETHScalePolynomialClock.polynomialClock.eq_1, ETHScalePolynomialClock.preEnvelope.eq_1,
    ETHScalePolynomialClock.logEnvelope.eq_1, ← PSc_def, ← CCc_def, ← FSc_def, ← UBc_def]
  exact polyClock_arith w UBc FSc CCc PSc

theorem outer_arith (TB SC BI WS SB U X b c nS ps kp bc : ℕ) (hT : TB ≤ kp * X)
    (hsc : SC ≤ 16777216 + SB) (hbi : BI ≤ bc + 2 * SB) (hws : WS ≤ 3 * U) (hb : b ≤ SB) (hc : c ≤ SB)
    (hSBU : SB ≤ U) (hUX : U ≤ X) (hX1 : 1 ≤ X) :
    TB + ((2 * SC + 2) + ((2 * b + 2) + ((2 * c + 2) + ((2 * BI + 2) +
      (nS * (WS + ps * TB) + nS + 2) + 1) + 1) + 1) + 1) + 1 ≤
    ((1 + nS * ps) * kp + 33554432 + 2 * bc + 4 * nS + 30) * X := by
  have hA : nS * (WS + ps * TB) ≤ 3 * (nS * X) + nS * (ps * (kp * X)) := by
    rw [Nat.mul_add]
    have h1 : nS * WS ≤ nS * (3 * U) := Nat.mul_le_mul_left _ hws
    have h2 : nS * (ps * TB) ≤ nS * (ps * (kp * X)) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hT)
    have h3 : nS * (3 * U) ≤ 3 * (nS * X) := by
      have := Nat.mul_le_mul_left nS hUX
      calc nS * (3 * U) = 3 * (nS * U) := by ring
        _ ≤ 3 * (nS * X) := Nat.mul_le_mul_left _ this
    omega
  have hbc : bc ≤ bc * X := Nat.le_mul_of_pos_right _ hX1
  have hnS : nS ≤ nS * X := Nat.le_mul_of_pos_right _ hX1
  have e : ((1 + nS * ps) * kp + 33554432 + 2 * bc + 4 * nS + 30) * X =
      kp * X + nS * (ps * (kp * X)) + 33554432 * X + 2 * (bc * X) + 4 * (nS * X) + 30 * X := by ring
  rw [e]
  omega

/-- Generic outer clock (literally the shape of `outerBound` and `outerBoundJ`). -/
theorem outer_generic (P : Parameters.Input) (b c SB R : ℕ) (hSB : Parameters.scaleBound P ≤ SB)
    (hb : b ≤ SB) (hc : c ≤ SB) (hR : P.rows + P.columns + P.edges ≤ R) :
    ETHScaleActualComplete.totalBound P +
      ((2 * Parameters.scale P + 2) +
        ((2 * b + 2) +
          ((2 * c + 2) +
            ((2 * Parameters.bins P + 2) +
              (nS * (ETHParameterScaleMachineInput.wordSize P +
                  BitMachineStackGrowth.perStep ETHScaleActualComplete.program *
                    ETHScaleActualComplete.totalBound P) + nS + 2) + 1) + 1) + 1) + 1) + 1 ≤
      ((1 + nS * BitMachineStackGrowth.perStep ETHScaleActualComplete.program) * Kp + 33554432 +
          2 * ClockC.binsConst + 4 * nS + 30) * (SB + R + 5) ^ 2 := by
  have hsc : P.sourceConstant ≤ SB := le_trans (le_max_left _ _) hSB
  have hnd : P.nextDepth ≤ SB := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hSB
  have hco : P.cost ≤ SB :=
    le_trans (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))) hSB
  have hraw : ETHScalePolynomialClock.rawMax P ≤ SB + R := by
    unfold ETHScalePolynomialClock.rawMax
    simp only [max_le_iff]
    omega
  have hw : ETHScalePolynomialClock.width P + 1 ≤ SB + R + 5 := by
    unfold ETHScalePolynomialClock.width; omega
  have hws : ETHParameterScaleMachineInput.wordSize P ≤ 3 * (SB + R + 5) := by
    unfold ETHParameterScaleMachineInput.wordSize; omega
  have hT : ETHScaleActualComplete.totalBound P ≤ Kp * (SB + R + 5) ^ 2 :=
    le_trans (ETHScalePolynomialClock.totalBound_le_polynomial P)
      (le_trans (polyClock_le _) (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hw 2)))
  have hs : Parameters.scale P ≤ 16777216 + SB := by
    have h := ClockC.scale_le P
    have h24 : (2 : ℕ) ^ 24 = 16777216 := by norm_num
    rw [h24] at h
    omega
  have hbi : Parameters.bins P ≤ ClockC.binsConst + 2 * SB := by
    have h := ClockC.bins_le P
    omega
  have hUX : SB + R + 5 ≤ (SB + R + 5) ^ 2 := by
    rw [pow_two]; exact Nat.le_mul_of_pos_right _ (by omega)
  have hX1 : 1 ≤ (SB + R + 5) ^ 2 := Nat.one_le_pow _ _ (by omega)
  exact outer_arith _ _ _ _ SB (SB + R + 5) _ b c nS (BitMachineStackGrowth.perStep ETHScaleActualComplete.program)
    Kp ClockC.binsConst hT hs hbi hws hb hc (by omega) hUX hX1

#print axioms polyClock_le
#print axioms outer_generic

variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- The width constant. -/
def Kw (c A : ℕ) : ℕ := c + A + 30

/-- At a physical level `j < k` the outer argument `SB + R + 5` is `≤ Kw c A · (a T)^(d+1)`. -/
theorem level_U (G : EndpointGraph V E) (c A d Δ n : ℕ) (γ : ℚ)
    (hcommon : G.SourceCommon γ Δ) (hlower : n ≤ Fintype.card E)
    (hupper : Fintype.card E ≤ A * n * EffectiveIteration.sourceDepth n ^ d)
    (hrep : 1 ≤ ETHTailGrowth.repetitions c A d n) (j : ℕ)
    (hj : j ≤ ETHTailGrowth.repetitions c A d n) :
    (c + 2 * n + 8 * FinalPadding.tableSize (ETHTailGrowth.repetitions c A d) n +
        A * ((SourceOriginalBranchPackets.packet n
          (EncodedGraph.encode (EncodedETHSource.serializeGraph G))).length + 1) ^ (d + 1) + 3) +
      ((PhysicalLevelRun.physParameters G c (EffectiveIteration.sourceDepth n)
          (Iteration.seedState (EffectiveIteration.sourceDepth n)) j).rows +
        (PhysicalLevelRun.physParameters G c (EffectiveIteration.sourceDepth n)
          (Iteration.seedState (EffectiveIteration.sourceDepth n)) j).columns +
        (PhysicalLevelRun.physParameters G c (EffectiveIteration.sourceDepth n)
          (Iteration.seedState (EffectiveIteration.sourceDepth n)) j).edges) + 5 ≤
      Kw c A * (((SourceOriginalBranchPackets.packet n
          (EncodedGraph.encode (EncodedETHSource.serializeGraph G))).length + 1) *
        FinalPadding.tableSize (ETHTailGrowth.repetitions c A d) n) ^ (d + 1) := by
  have hf := (ClockA.level_facts G c A d Δ n γ hcommon hlower hupper hrep j hj).1
  have hr := ClockA.rows_le_prod (PhysicalLevelRun.physRun G c (EffectiveIteration.sourceDepth n)
    (Iteration.seedState (EffectiveIteration.sourceDepth n)) j).matrix
  have hcl := ClockA.cols_le_prod (PhysicalLevelRun.physRun G c (EffectiveIteration.sourceDepth n)
    (Iteration.seedState (EffectiveIteration.sourceDepth n)) j).matrix
  have hP := PhysicalLevelRun.physParameters_eq G c (EffectiveIteration.sourceDepth n)
    (Iteration.seedState (EffectiveIteration.sourceDepth n)) j
  have hrows : (PhysicalLevelRun.physParameters G c (EffectiveIteration.sourceDepth n)
      (Iteration.seedState (EffectiveIteration.sourceDepth n)) j).rows =
      (PhysicalLevelRun.physRun G c (EffectiveIteration.sourceDepth n)
        (Iteration.seedState (EffectiveIteration.sourceDepth n)) j).matrix.rows := rfl
  have hcols : (PhysicalLevelRun.physParameters G c (EffectiveIteration.sourceDepth n)
      (Iteration.seedState (EffectiveIteration.sourceDepth n)) j).columns =
      (PhysicalLevelRun.physRun G c (EffectiveIteration.sourceDepth n)
        (Iteration.seedState (EffectiveIteration.sourceDepth n)) j).matrix.columns := rfl
  have hedges : (PhysicalLevelRun.physParameters G c (EffectiveIteration.sourceDepth n)
      (Iteration.seedState (EffectiveIteration.sourceDepth n)) j).edges = Fintype.card E := rfl
  have hE := EncodedGraph.encode_length_lower (EncodedETHSource.serializeGraph G)
  have hEl : (EncodedETHSource.serializeGraph G).edges.length = Fintype.card E :=
    EncodedETHSource.serializeGraph_edges G
  have hpl := SourceOriginalBranchPackets.packet_length n
    (EncodedGraph.encode (EncodedETHSource.serializeGraph G))
  rw [hrows, hcols, hedges]
  set a := (SourceOriginalBranchPackets.packet n
    (EncodedGraph.encode (EncodedETHSource.serializeGraph G))).length + 1 with ha
  set T := FinalPadding.tableSize (ETHTailGrowth.repetitions c A d) n with hT
  have hT1 : 1 ≤ T := ClockH.table_pos _ n
  have ha1 : 1 ≤ a := by omega
  have hY1 : 1 ≤ a * T := Nat.mul_pos ha1 hT1
  set Y1 := (a * T) ^ (d + 1) with hY1d
  have haT : a ≤ Y1 := by
    calc a ≤ a * T := Nat.le_mul_of_pos_right _ hT1
      _ = (a * T) ^ 1 := (pow_one _).symm
      _ ≤ Y1 := Nat.pow_le_pow_right hY1 (by omega)
  have hTT : T ≤ Y1 := by
    calc T ≤ a * T := Nat.le_mul_of_pos_left _ ha1
      _ = (a * T) ^ 1 := (pow_one _).symm
      _ ≤ Y1 := Nat.pow_le_pow_right hY1 (by omega)
  have hQ : a ^ (d + 1) ≤ Y1 := Nat.pow_le_pow_left (Nat.le_mul_of_pos_right _ hT1) _
  have hAQ : A * a ^ (d + 1) ≤ A * Y1 := Nat.mul_le_mul_left _ hQ
  have hcY : c ≤ c * Y1 := Nat.le_mul_of_pos_right _ (by omega)
  have e : Kw c A * Y1 = c * Y1 + A * Y1 + 30 * Y1 := by unfold Kw; ring
  rw [e]
  omega


/-- The outer clock at level `j < k` (literally `LevelJPrep.outerBoundJ` at the physical state). -/
theorem level_outerJ (G : EndpointGraph V E) (c A d Δ n : ℕ) (γ : ℚ)
    (hcommon : G.SourceCommon γ Δ) (hlower : n ≤ Fintype.card E)
    (hupper : Fintype.card E ≤ A * n * EffectiveIteration.sourceDepth n ^ d)
    (hrep : 1 ≤ ETHTailGrowth.repetitions c A d n) (j : ℕ)
    (hj : j ≤ ETHTailGrowth.repetitions c A d n) :
    outerBoundJ G c (EffectiveIteration.sourceDepth n) (yP G c (EffectiveIteration.sourceDepth n) j) j
        (MP G c (EffectiveIteration.sourceDepth n) j) ≤
      ((1 + nS * BitMachineStackGrowth.perStep ETHScaleActualComplete.program) * Kp + 33554432 +
          2 * ClockC.binsConst + 4 * nS + 30) * (Kw c A * (((SourceOriginalBranchPackets.packet n
          (EncodedGraph.encode (EncodedETHSource.serializeGraph G))).length + 1) *
        FinalPadding.tableSize (ETHTailGrowth.repetitions c A d) n) ^ (d + 1)) ^ 2 := by
  have hSB := ClockC.level_scaleBound G c A d Δ n γ hcommon hlower hupper hrep j hj
  have hU := level_U G c A d Δ n γ hcommon hlower hupper hrep j hj
  have hb : EffectiveIteration.sourceDepth n ≤ c + 2 * n +
      8 * FinalPadding.tableSize (ETHTailGrowth.repetitions c A d) n +
      A * ((SourceOriginalBranchPackets.packet n
        (EncodedGraph.encode (EncodedETHSource.serializeGraph G))).length + 1) ^ (d + 1) + 3 :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hSB
  have hc : c ≤ c + 2 * n +
      8 * FinalPadding.tableSize (ETHTailGrowth.repetitions c A d) n +
      A * ((SourceOriginalBranchPackets.packet n
        (EncodedGraph.encode (EncodedETHSource.serializeGraph G))).length + 1) ^ (d + 1) + 3 := by omega
  have hg := outer_generic (PhysicalLevelRun.physParameters G c (EffectiveIteration.sourceDepth n)
      (Iteration.seedState (EffectiveIteration.sourceDepth n)) j)
    (EffectiveIteration.sourceDepth n) c _ _ hSB hb hc le_rfl
  exact le_trans hg (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hU 2))

#print axioms level_U
#print axioms level_outerJ

end
end EthInapproximability.CurrentPaper.ClockP
