import EthInapproximability.CurrentPaper.G5cKInput
import EthInapproximability.CurrentPaper.W12Ready0
import EthInapproximability.CurrentPaper.EntryClockPoly3Final0

/-!
# Level 0 of the physical run, bounded in the lock's additive form (private lane owner:b-g5-4,
# segment 2)

The level-0 round of the admitted shell (`Level0Install.level0_step`, clock
`level0BoundP M G n c T22 + installBoundP G c b 0 + 1`, with the discharged level-0 writer clock
`T22 := ClockO.T22zero G n c`) is bounded by

  `(n + |enc G| + 1)^N + 2^(N p)`

for ONE `N` chosen after the fixed program data `(M, c)` and before the graph types, `G`, `n`, `p`.
Premises: `1 ≤ c`, `clog(n+2) ≤ p`, the level-0 named premise
`G5cShellNamed.LevelNamed G c b 0 p` (the same premise the round levels `1 ≤ j < k` use, here at
`j = 0`: source names of the level-0 record, output carrier names, next-state names), and the level-0
naming envelope `oneLevelBound (EntryClockPoly.P0 G n c) ≤ p` (the premise of the admitted
`EntryClockPoly3.T22_0_le`, used only for the discharged writer clock `T22zero`).

The `M`-clock stage inside level 0 (`WeightedRawWords.kProgram M`, which writes the dead scratch
`kValue M n` into the master cell `K`) is charged through the admitted
`WeightedRawWordsClock.rawWordsKBound_serialize_le` (`rawC M c * (n + |enc G| + 1)^128`, valid for
EVERY machine `M`), and the controller constant `perStep (level0RowsProgram M c)` through the
admitted `W12Ready0.clean_split`. Hence `N` depends on `(M, c)` (the fixed program), not on `k`,
`G`, the level, the branch or the promise case.

NOT claimed: the parser; the pad join; `y_k` emission; any total machine.
-/

noncomputable section

namespace EthInapproximability.CurrentPaper.G5dLevel0

open Turing BitMachineEncoding BitMachineStackEmbedding
open EthInapproximability.ParameterizedNP.GuardedSourceGraph
open WeightedLevel0Rows WeightedLevel0Persist WeightedLevel0Clean WeightedLevel0Target
open WeightedLevel0Ready WeightedLevel0WriterRun LevelJRows LevelJPersist LevelJClean LevelJReady
open LevelJMasters OuterLevel0Run LevelJPrep OuterLevel0Bridge LevelJBridge
open OuterLevel0Full NextMasterWords CostUpdateStages CostUpdateMachine CostUpdateEmbed
open Level0CostRound Level0CostRun Level0DimsRound Level0DimsClean RoundP CleanP ExitP StepP
open EntryClockPoly3 (ell3)

set_option maxHeartbeats 3000000
set_option maxRecDepth 16384
set_option synthInstance.maxSize 200000
set_option synthInstance.maxHeartbeats 2000000

variable [Fintype BStack] [Fintype MatrixTableInterlaceProtectedBridge.Label]

/-- The level-0 composite clock splits literally into the raw-words clock and the level-row clock
`boundJ` of the level-0 record. -/
theorem bound0_eq (M : BitMachine.Machine) {V E : Type} [Fintype V] [DecidableEq V] [Fintype E]
    [DecidableEq E] (G : EndpointGraph V E) (n c : ℕ) :
    WeightedLevel0Clean.bound0 M G n c =
      WeightedVertexWord.rawWordsKVBound M n c (EncodedETHSource.serializeGraph G) +
        LevelJClean.boundJ G c (EffectiveIteration.sourceDepth n)
          (Iteration.seedState (EffectiveIteration.sourceDepth n)).budget 0
          (Iteration.seedState (EffectiveIteration.sourceDepth n)).matrix + 1 := by
  unfold WeightedLevel0Clean.bound0 LevelJClean.boundJ
  omega

/-- The explicit level-0 bound (everything polynomial in `n`, `ell = |enc G|`, `2^p`). -/
def level0Rest (rawK ps2 C ps K C22 n ell p : ℕ) : ℕ :=
  ((rawK * (n + ell + 1) ^ 128 + 110 * (ell + 1) ^ 3 + 1) +
      ((1 + 9 * ps) * ((800 * (ell + 1) + 2) ^ C + 2 ^ (C * p)) + 13 +
        W12RowTime.Krow * (ell + 205 * 2 ^ (4 * p) + 1) ^ 9) + 1) +
  WeightedLevel0Clean.nClear * (ps2 *
    ((rawK * (n + ell + 1) ^ 128 + 110 * (ell + 1) ^ 3 + 1) +
      ((1 + 9 * ps) * ((800 * (ell + 1) + 2) ^ C + 2 ^ (C * p)) + 13 +
        W12RowTime.Krow * (ell + 205 * 2 ^ (4 * p) + 1) ^ 9) + 1)) +
  WeightedLevel0Clean.nClear + 3 + (6 * 2 ^ p + 11) + K * (3 * 2 ^ p + 2 * ell + 7) ^ 2 + 1 +
  ((n + ell + 1) ^ C22 + 2 ^ (C22 * p)) +
  (2000000 * ClockD.Kc + 1000000) * (5 * 2 ^ p + ell + 1) ^ 6 +
  DimsClock1.Kd * (2 * 2 ^ p + 1) ^ 2 +
  ProtectedBudgetNormalizationScratch.coefficient * 2 ^ 18 * (ell ^ 18 + 205 ^ 18 * 2 ^ (72 * p)) +
  2 * 2 ^ (2 * p) +
  Level0CleanRun.nB * ((ell + 205 * 2 ^ (4 * p)) +
    BitMachineStackGrowth.perStep OuterLevel0Bridge.bridgeH *
      (ProtectedBudgetNormalizationScratch.coefficient * 2 ^ 18 *
        (ell ^ 18 + 205 ^ 18 * 2 ^ (72 * p)))) +
  Level0CleanRun.nB + (12 * 2 ^ p + 4 * ell + 30) + 20

/-- One power bound for `level0Rest` (pure arithmetic). -/
theorem level0Rest_le_pow (rawK ps2 C ps K C22 : ℕ) :
    ∃ N : ℕ, ∀ Y p n ell : ℕ, 2 ≤ Y → 2 ^ p ≤ Y → n ≤ Y → ell ≤ Y →
      level0Rest rawK ps2 C ps K C22 n ell p ≤ Y ^ N := by
  apply Exists.intro
  intro Y p n ell hY hP hn hell
  have hP1 : 2 ^ p ≤ Y ^ 1 := by rw [pow_one]; exact hP
  have hn1 : n ≤ Y ^ 1 := by rw [pow_one]; exact hn
  have hell1 : ell ≤ Y ^ 1 := by rw [pow_one]; exact hell
  unfold level0Rest
  repeat (first
    | with_reducible exact hP1 | with_reducible exact hn1 | with_reducible exact hell1
    | with_reducible apply G5cPowBound.atomC hP | with_reducible apply G5cPowBound.const_le hY
    | with_reducible apply G5cPowBound.add_le hY | with_reducible apply G5cPowBound.mul_le
    | with_reducible apply G5cPowBound.pow_le)

private theorem from_clog {x p : ℕ} (h : Nat.clog 2 x ≤ p) : x ≤ 2 ^ p :=
  (Nat.le_pow_clog (by decide : 1 < (2 : ℕ)) _).trans
    (Nat.pow_le_pow_right (by decide) h)

/-- `max a b ^ N ≤ a ^ N + b ^ N`. -/
theorem max_pow_le (a b N : ℕ) : (max a b) ^ N ≤ a ^ N + b ^ N := by
  rcases le_total a b with h | h
  · rw [max_eq_right h]; omega
  · rw [max_eq_left h]; omega

/-- **Segment 2: level 0 in the additive form.** -/
theorem level0_additive (M : BitMachine.Machine) (c : ℕ) :
    ∃ N : ℕ, ∀ {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
      (G : EndpointGraph V E) (n p : ℕ), 1 ≤ c → Nat.clog 2 (n + 2) ≤ p →
      G5cShellNamed.LevelNamed G c (EffectiveIteration.sourceDepth n) 0 p →
      EffectiveIteration.oneLevelBound (EntryClockPoly.P0 G n c) ≤ p →
      Level0Install.level0BoundP M G n c (ClockO.T22zero G n c) +
          StepP.installBoundP G c (EffectiveIteration.sourceDepth n) 0 + 1 ≤
        (n + (EncodedGraph.encode (EncodedETHSource.serializeGraph G)).length + 1) ^ N +
          2 ^ (N * p) := by
  obtain ⟨C, ps, hB⟩ := G5bBoundJNamed.boundJ_named
  obtain ⟨K, hK⟩ := G5bPrepNamed.outer_named
  obtain ⟨C22, hT⟩ := EntryClockPoly3.T22_0_le
  obtain ⟨ps2, hps2⟩ := W12Ready0.clean_split M c
  obtain ⟨N, hN⟩ := level0Rest_le_pow (WeightedRawWordsClock.rawC M c) ps2 C ps K C22
  refine ⟨N, fun {V E} _ _ _ _ G n p hc hfloor hnamed hone => ?_⟩
  obtain ⟨h, hrows, hcols, hcc, hb, hy, hr, hcol⟩ := hnamed
  let i : EntryClockPoly3.LI := ⟨V, E, G, c, EffectiveIteration.sourceDepth n,
    StepP.yP G c (EffectiveIteration.sourceDepth n) 0, 0,
    StepP.MP G c (EffectiveIteration.sourceDepth n) 0⟩
  -- the named bounds at the level-0 record
  have hbj : LevelJClean.boundJ G c (EffectiveIteration.sourceDepth n)
      (Iteration.seedState (EffectiveIteration.sourceDepth n)).budget 0
      (Iteration.seedState (EffectiveIteration.sourceDepth n)).matrix ≤
      (1 + 9 * ps) * ((800 * (ell3 G + 1) + 2) ^ C + 2 ^ (C * p)) + 13 +
        W12RowTime.Krow * (ell3 G + 205 * 2 ^ (4 * p) + 1) ^ 9 := hB i p h hrows hcols
  have ho : OuterLevel0Prep.outerBound G n c ≤ K * (3 * 2 ^ p + 2 * ell3 G + 7) ^ 2 := hK i p h
  have hcar : ((2 * ProtectedFullBankBridgeScratch.actualRows G c (EffectiveIteration.sourceDepth n)
            (StepP.yP G c (EffectiveIteration.sourceDepth n) 0) 0 (StepP.MP G c (EffectiveIteration.sourceDepth n) 0) + 2) +
          ((2 * ProtectedFullBankBridgeScratch.actualCols G c (EffectiveIteration.sourceDepth n)
            (StepP.yP G c (EffectiveIteration.sourceDepth n) 0) 0 (StepP.MP G c (EffectiveIteration.sourceDepth n) 0) + 2) +
            (ProtectedFullBankBridgeScratch.actualRows G c (EffectiveIteration.sourceDepth n)
              (StepP.yP G c (EffectiveIteration.sourceDepth n) 0) 0 (StepP.MP G c (EffectiveIteration.sourceDepth n) 0) +
             ProtectedFullBankBridgeScratch.actualCols G c (EffectiveIteration.sourceDepth n)
              (StepP.yP G c (EffectiveIteration.sourceDepth n) 0) 0 (StepP.MP G c (EffectiveIteration.sourceDepth n) 0) + 4) +
            1) + 1) + 1 ≤ 6 * 2 ^ p + 11 :=
    G5bPrepNamed.ready_carriers_named i p hrows hcols
  have hcost : costBound (Parameters.scale (OuterLevel0Prep.P0 G n c)) (EffectiveIteration.sourceDepth n) c
      (Parameters.bins (OuterLevel0Prep.P0 G n c)) (Fintype.card E)
      (Iteration.seedState (EffectiveIteration.sourceDepth n)).budget ≤
      (2000000 * ClockD.Kc + 1000000) * (5 * 2 ^ p + ell3 G + 1) ^ 6 :=
    ActualRoundParts.cost_bound_named i p h
  have hdims : NextDimsMachineTN.dimsBound (dx G n c) ≤ DimsClock1.Kd * (2 * 2 ^ p + 1) ^ 2 :=
    ActualRoundParts.dims_bound_named i p hc hrows hcols
  have hbud : ProtectedFullBankBridgeScratch.actualPhysicalBudget G c (EffectiveIteration.sourceDepth n)
      (Iteration.seedState (EffectiveIteration.sourceDepth n)).budget 0
      (Iteration.seedState (EffectiveIteration.sourceDepth n)).matrix ≤
      ProtectedBudgetNormalizationScratch.coefficient * 2 ^ 18 *
        (ell3 G ^ 18 + 205 ^ 18 * 2 ^ (72 * p)) :=
    G5bRoundNamed.budget_named i p h hrows hcols
  have hout : (ProtectedFullBankBridgeScratch.actualPhysicalOutput G c (EffectiveIteration.sourceDepth n)
      (Iteration.seedState (EffectiveIteration.sourceDepth n)).budget 0
      (Iteration.seedState (EffectiveIteration.sourceDepth n)).matrix).length ≤ 2 ^ (2 * p) :=
    G5bRoundNamed.output_named i p hrows hcols
  have hst : (∑ i : Fin Level0CleanRun.nB,
      (((ProtectedFullBankBridgeScratch.actualPhysicalStart G c (EffectiveIteration.sourceDepth n)
        (Iteration.seedState (EffectiveIteration.sourceDepth n)).budget 0
        (Iteration.seedState (EffectiveIteration.sourceDepth n)).matrix).stk
          ((Fintype.equivFin BStack).symm i)).length +
        BitMachineStackGrowth.perStep bridgeH *
          ProtectedFullBankBridgeScratch.actualPhysicalBudget G c (EffectiveIteration.sourceDepth n)
            (Iteration.seedState (EffectiveIteration.sourceDepth n)).budget 0
            (Iteration.seedState (EffectiveIteration.sourceDepth n)).matrix)) ≤
      Level0CleanRun.nB * ((ell3 G + 205 * 2 ^ (4 * p)) +
        BitMachineStackGrowth.perStep OuterLevel0Bridge.bridgeH *
          (ProtectedBudgetNormalizationScratch.coefficient * 2 ^ 18 *
            (ell3 G ^ 18 + 205 ^ 18 * 2 ^ (72 * p)))) :=
    G5bRoundNamed.stacks_named i p h hrows hcols
  have hins : StepP.installBoundP G c (EffectiveIteration.sourceDepth n) 0 ≤ 12 * 2 ^ p + 4 * ell3 G + 30 :=
    ActualRoundParts.install_bound_named G c (EffectiveIteration.sourceDepth n) 0 p hcc hb hy hr hcol
  have ht22 : ClockO.T22zero G n c ≤ (n + ell3 G + 1) ^ C22 + 2 ^ (C22 * p) := hT G n c p hone
  -- the raw-words (`M`-clock) stage
  have hraw : WeightedVertexWord.rawWordsKVBound M n c (EncodedETHSource.serializeGraph G) ≤
      WeightedRawWordsClock.rawC M c * (n + ell3 G + 1) ^ 128 + 110 * (ell3 G + 1) ^ 3 + 1 := by
    have h1 := WeightedRawWordsClock.rawWordsKBound_serialize_le M n c G
    have h2 := W12Ready0.vertexBound_le (EncodedETHSource.serializeGraph G)
      (EncodedETHSource.serializeGraph_valid G)
    have hell : (EncodedGraph.encode (EncodedETHSource.serializeGraph G)).length = ell3 G := rfl
    rw [hell] at h1 h2
    unfold WeightedVertexWord.rawWordsKVBound
    rw [hell]
    omega
  set Rb0 := (WeightedRawWordsClock.rawC M c * (n + ell3 G + 1) ^ 128 + 110 * (ell3 G + 1) ^ 3 + 1) +
      ((1 + 9 * ps) * ((800 * (ell3 G + 1) + 2) ^ C + 2 ^ (C * p)) + 13 +
        W12RowTime.Krow * (ell3 G + 205 * 2 ^ (4 * p) + 1) ^ 9) + 1 with hRb0
  have hb0 : WeightedLevel0Clean.bound0 M G n c ≤ Rb0 := by
    rw [bound0_eq]; omega
  have hmul : WeightedLevel0Clean.nClear * (ps2 * WeightedLevel0Clean.bound0 M G n c) ≤
      WeightedLevel0Clean.nClear * (ps2 * Rb0) :=
    Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hb0)
  have hprep : OuterLevel0Prep.prepBound M G n c ≤
      Rb0 + WeightedLevel0Clean.nClear * (ps2 * Rb0) + WeightedLevel0Clean.nClear + 3 +
        (6 * 2 ^ p + 11) + K * (3 * 2 ^ p + 2 * ell3 G + 7) ^ 2 + 1 := by
    unfold OuterLevel0Prep.prepBound
    rw [W12Ready0.ready_split, hps2]
    omega
  have hmain : Level0Install.level0BoundP M G n c (ClockO.T22zero G n c) +
      StepP.installBoundP G c (EffectiveIteration.sourceDepth n) 0 + 1 ≤
      level0Rest (WeightedRawWordsClock.rawC M c) ps2 C ps K C22 n (ell3 G) p := by
    unfold Level0Install.level0BoundP level0Rest
    rw [← hRb0]
    omega
  -- absorb into one power
  have hp1 : 1 ≤ p := by
    have := Nat.clog_pos (by decide : 1 < 2) (by omega : 1 < n + 2)
    omega
  have h2p : 2 ≤ 2 ^ p := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ p := Nat.pow_le_pow_right (by decide) hp1
  set Y := max (n + ell3 G + 1) (2 ^ p) with hY
  have hY2 : 2 ≤ Y := le_trans h2p (le_max_right _ _)
  have hYp : 2 ^ p ≤ Y := le_max_right _ _
  have hYn : n ≤ Y := le_trans (by omega) (le_max_left _ _)
  have hYl : ell3 G ≤ Y := le_trans (by omega) (le_max_left _ _)
  have hpow := hN Y p n (ell3 G) hY2 hYp hYn hYl
  have hmax := max_pow_le (n + ell3 G + 1) (2 ^ p) N
  rw [← hY] at hmax
  have e2 : (2 ^ p) ^ N = 2 ^ (N * p) := by rw [← pow_mul, mul_comm]
  have hell : (EncodedGraph.encode (EncodedETHSource.serializeGraph G)).length = ell3 G := rfl
  rw [hell]
  omega

#print axioms bound0_eq
#print axioms level0Rest_le_pow
#print axioms level0_additive

end EthInapproximability.CurrentPaper.G5dLevel0
