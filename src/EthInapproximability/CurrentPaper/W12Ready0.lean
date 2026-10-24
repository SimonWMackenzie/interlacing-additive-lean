import EthInapproximability.CurrentPaper.W12BoundJ
import EthInapproximability.CurrentPaper.RawWordsClockPoly
import EthInapproximability.CurrentPaper.OuterLevel0Prep

/-! Lane owner:b-weighted-level-12, segment 1, LEVEL 0: the ready half `OuterLevel0Prep.readyBound`
(= owner-4's `cleanBound` = level-0 composite clock `bound0` + charged clear, plus the rows/cols carrier terms)
is majorized explicitly, polynomially in `a = |w| + 1` and `T = tableSize`, for the actual machine
`CutoffBitMachine.actualMachine c A d`.

`bound0` = the raw-words clock `rawWordsKVBound` (admitted `WeightedRawWordsClock.rawWordsKBound_serialize_le`
plus `vertexBound_le` here) + the level-row clock at level 0 (`W12BoundJ.pbJ_level` at `j = 0`,
`W12RowTime.rowTime_level`, owner-11's `ClockK.level_envelope` at `j = 0`). At level 0 the start bank is blank on
the cleared cells, so the clear costs `nClear · (perStep · bound0)` only (owner-4's `cleanBound`). The carriers
`actualRows`, `actualCols` at level 0 are `< 4 T` (admitted `ClockF.level_actual` at `j = 0`). -/

namespace EthInapproximability.CurrentPaper.W12Ready0

open EthInapproximability.ParameterizedNP.GuardedSourceGraph
open EntryClockPoly3 W12BoundJ

noncomputable section

set_option maxHeartbeats 3000000
set_option maxRecDepth 16384

theorem vertexBound_le (g : EncodedGraph.Graph) (hg : g.Valid) :
    WeightedVertexWord.vertexBound g ≤ 110 * ((EncodedGraph.encode g).length + 1) ^ 3 := by
  have hs := WeightedRawWordsClock.endpointStream_le g hg
  have hn := EncodedGraph.encode_length_lower g
  unfold WeightedVertexWord.vertexBound
  generalize (SourceNormalizationMachineDecode.endpointStream g).length = S at hs ⊢
  generalize (EncodedGraph.encode g).length = L at hn ⊢
  generalize g.edges.length = e at hs hn ⊢
  generalize g.vertices = v at hs hn ⊢
  have h1 : e * (2 * v + 2) ≤ L * (2 * L + 2) := Nat.mul_le_mul (by omega) (by omega)
  have h2 : L * (2 * L + 2) ≤ 2 * (L + 1) ^ 3 := by
    have : L * (2 * L + 2) = 2 * (L * (L + 1)) := by ring
    rw [this]
    have h3 : L * (L + 1) ≤ (L + 1) * (L + 1) := Nat.mul_le_mul_right _ (by omega)
    have h4 : (L + 1) * (L + 1) ≤ (L + 1) ^ 3 := by
      rw [show (L + 1) ^ 3 = (L + 1) * (L + 1) * (L + 1) by ring]
      exact Nat.le_mul_of_pos_right _ (by omega)
    omega
  have h5 : L + 1 ≤ (L + 1) ^ 3 := by
    calc L + 1 = (L + 1) ^ 1 := (pow_one _).symm
      _ ≤ (L + 1) ^ 3 := Nat.pow_le_pow_right (by omega) (by norm_num)
  omega

variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- `bound0` splits literally (level-0 seed arguments are `StepP.yP … 0`, `StepP.MP … 0` definitionally). -/
theorem bound0_split : ∃ ps : ℕ, ∀ (M : BitMachine.Machine) {V E : Type} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E] (G : EndpointGraph V E) (n c : ℕ),
    WeightedLevel0Clean.bound0 M G n c =
      WeightedVertexWord.rawWordsKVBound M n c (EncodedETHSource.serializeGraph G) +
        pbJ ⟨V, E, G, c, EffectiveIteration.sourceDepth n, StepP.yP G c (EffectiveIteration.sourceDepth n) 0, 0,
          StepP.MP G c (EffectiveIteration.sourceDepth n) 0⟩ +
        (9 * (ps * pbJ ⟨V, E, G, c, EffectiveIteration.sourceDepth n,
          StepP.yP G c (EffectiveIteration.sourceDepth n) 0, 0, StepP.MP G c (EffectiveIteration.sourceDepth n) 0⟩) +
          9 + 2) +
        WeightedRowFields.rowTime (Fintype.card V)
          (4 * Iteration.s G c (EffectiveIteration.sourceDepth n) (StepP.yP G c (EffectiveIteration.sourceDepth n) 0) 0
            (StepP.MP G c (EffectiveIteration.sourceDepth n) 0))
          (ProtectedFullBankBridgeScratch.actualD G c (EffectiveIteration.sourceDepth n)
            (StepP.yP G c (EffectiveIteration.sourceDepth n) 0) 0 (StepP.MP G c (EffectiveIteration.sourceDepth n) 0)).nb
          (ProtectedFullBankBridgeScratch.actualD G c (EffectiveIteration.sourceDepth n)
            (StepP.yP G c (EffectiveIteration.sourceDepth n) 0) 0
            (StepP.MP G c (EffectiveIteration.sourceDepth n) 0)).stagePrefixRows
          (ProtectedFullBankBridgeScratch.actualD G c (EffectiveIteration.sourceDepth n)
            (StepP.yP G c (EffectiveIteration.sourceDepth n) 0) 0 (StepP.MP G c (EffectiveIteration.sourceDepth n) 0)).rx
          (ProtectedFullBankBridgeScratch.actualD G c (EffectiveIteration.sourceDepth n)
            (StepP.yP G c (EffectiveIteration.sourceDepth n) 0) 0 (StepP.MP G c (EffectiveIteration.sourceDepth n) 0)).binBase
          (ProtectedFullBankBridgeScratch.actualD G c (EffectiveIteration.sourceDepth n)
            (StepP.yP G c (EffectiveIteration.sourceDepth n) 0) 0 (StepP.MP G c (EffectiveIteration.sourceDepth n) 0)).rawWidth
          (ProtectedFullBankBridgeScratch.actualD G c (EffectiveIteration.sourceDepth n)
            (StepP.yP G c (EffectiveIteration.sourceDepth n) 0) 0 (StepP.MP G c (EffectiveIteration.sourceDepth n) 0)).uniform +
        3 :=
  ⟨_, fun _ {V E} _ _ _ _ _ _ _ => rfl⟩

/-- owner-4's `cleanBound` splits literally; `ps2` is `perStep (level0RowsProgram M c)` as elaborated there. -/
theorem clean_split (M : BitMachine.Machine) (c : ℕ) : ∃ ps2 : ℕ, ∀ {V E : Type} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E] (G : EndpointGraph V E) (n : ℕ),
    WeightedLevel0Ready.cleanBound M G n c =
      WeightedLevel0Clean.bound0 M G n c +
        (WeightedLevel0Clean.nClear * (ps2 * WeightedLevel0Clean.bound0 M G n c) + WeightedLevel0Clean.nClear + 2) + 1 :=
  ⟨_, fun {V E} _ _ _ _ _ _ => rfl⟩

theorem ready_split (M : BitMachine.Machine) (G : EndpointGraph V E) (n c : ℕ) :
    OuterLevel0Prep.readyBound M G n c =
      WeightedLevel0Ready.cleanBound M G n c +
        ((2 * ProtectedFullBankBridgeScratch.actualRows G c (EffectiveIteration.sourceDepth n)
            (StepP.yP G c (EffectiveIteration.sourceDepth n) 0) 0 (StepP.MP G c (EffectiveIteration.sourceDepth n) 0) + 2) +
          ((2 * ProtectedFullBankBridgeScratch.actualCols G c (EffectiveIteration.sourceDepth n)
            (StepP.yP G c (EffectiveIteration.sourceDepth n) 0) 0 (StepP.MP G c (EffectiveIteration.sourceDepth n) 0) + 2) +
            (ProtectedFullBankBridgeScratch.actualRows G c (EffectiveIteration.sourceDepth n)
              (StepP.yP G c (EffectiveIteration.sourceDepth n) 0) 0 (StepP.MP G c (EffectiveIteration.sourceDepth n) 0) +
             ProtectedFullBankBridgeScratch.actualCols G c (EffectiveIteration.sourceDepth n)
              (StepP.yP G c (EffectiveIteration.sourceDepth n) 0) 0 (StepP.MP G c (EffectiveIteration.sourceDepth n) 0) + 4) +
            1) + 1) + 1 := rfl

/-- **Segment 1, level 0: the ready half of the actual machine, explicitly polynomial.**
`a := |w| + 1`, `T := tableSize`, `Z := a^(d+1) · T` (written out). `Cp`, `ps` absolute; `ps2` depends on
`c A d` only (a controller constant of the fixed program `level0RowsProgram (actualMachine c A d) c`). -/
theorem ready0_level : ∃ Cp ps : ℕ, ∀ c A d : ℕ, ∃ ps2 : ℕ,
    ∀ {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : EndpointGraph V E) (Δ n : ℕ) (γ : ℚ),
    G.SourceCommon γ Δ → n ≤ Fintype.card E →
    Fintype.card E ≤ A * n * EffectiveIteration.sourceDepth n ^ d →
    1 ≤ ETHTailGrowth.repetitions c A d n →
    OuterLevel0Prep.readyBound (CutoffBitMachine.actualMachine c A d) G n c ≤
      (1 + WeightedLevel0Clean.nClear * ps2) *
        (WeightedRawWordsClock.rawC (CutoffBitMachine.actualMachine c A d) c *
            ((SourceOriginalBranchPackets.packet n
              (EncodedGraph.encode (EncodedETHSource.serializeGraph G))).length + 1) ^ 128 +
          110 * ((SourceOriginalBranchPackets.packet n
              (EncodedGraph.encode (EncodedETHSource.serializeGraph G))).length + 1) ^ 3 + 1 +
          ((1 + 9 * ps) * (2 * ((SourceOriginalBranchPackets.packet n
              (EncodedGraph.encode (EncodedETHSource.serializeGraph G))).length + 1) ^ Cp *
            FinalPadding.tableSize (ETHTailGrowth.repetitions c A d) n ^ Cp) + 14 +
          W12RowTime.Krow * (ClockK.KE c A * ((((SourceOriginalBranchPackets.packet n
              (EncodedGraph.encode (EncodedETHSource.serializeGraph G))).length + 1) ^ (d + 1) *
              FinalPadding.tableSize (ETHTailGrowth.repetitions c A d) n) *
            (((SourceOriginalBranchPackets.packet n
              (EncodedGraph.encode (EncodedETHSource.serializeGraph G))).length + 1) ^ (d + 1) *
              FinalPadding.tableSize (ETHTailGrowth.repetitions c A d) n)) + 1) ^ 9)) +
        WeightedLevel0Clean.nClear + 3 + (24 * FinalPadding.tableSize (ETHTailGrowth.repetitions c A d) n + 11) := by
  obtain ⟨Cp, hCp⟩ := pbJ_level
  obtain ⟨ps, hps⟩ := bound0_split
  refine ⟨Cp, ps, fun c A d => ?_⟩
  obtain ⟨ps2, hps2⟩ := clean_split (CutoffBitMachine.actualMachine c A d) c
  refine ⟨ps2, fun {V E} _ _ _ _ G Δ n γ hcommon hlower hupper hrep => ?_⟩
  have hk0 : 0 < ETHTailGrowth.repetitions c A d n := hrep
  have hpb := hCp G c A d Δ n γ hcommon hlower hupper hrep 0 hk0
  have hrt := W12RowTime.rowTime_level G c (EffectiveIteration.sourceDepth n)
    (StepP.yP G c (EffectiveIteration.sourceDepth n) 0) 0 (StepP.MP G c (EffectiveIteration.sourceDepth n) 0)
  have hen := ClockK.level_envelope G c A d Δ n γ hcommon hlower hupper hrep 0 hk0
  have hrt' := hrt.trans (Nat.mul_le_mul_left W12RowTime.Krow
    (Nat.pow_le_pow_left (Nat.add_le_add_right hen 1) 9))
  have hraw := WeightedRawWordsClock.rawWordsKBound_serialize_le (CutoffBitMachine.actualMachine c A d) n c G
  have hvx := vertexBound_le (EncodedETHSource.serializeGraph G) (EncodedETHSource.serializeGraph_valid G)
  have hpk := ClockH.packet_ge n (EncodedGraph.encode (EncodedETHSource.serializeGraph G))
  have hraw' := hraw.trans (Nat.mul_le_mul_left (WeightedRawWordsClock.rawC (CutoffBitMachine.actualMachine c A d) c)
    (Nat.pow_le_pow_left hpk 128))
  have hvx' := hvx.trans (Nat.mul_le_mul_left 110 (Nat.pow_le_pow_left (by omega :
    (EncodedGraph.encode (EncodedETHSource.serializeGraph G)).length + 1 ≤
      (SourceOriginalBranchPackets.packet n (EncodedGraph.encode (EncodedETHSource.serializeGraph G))).length + 1) 3))
  have hRW : WeightedVertexWord.rawWordsKVBound (CutoffBitMachine.actualMachine c A d) n c
      (EncodedETHSource.serializeGraph G) =
      WeightedRawWords.rawWordsKBound (CutoffBitMachine.actualMachine c A d) n c
        (EncodedGraph.encode (EncodedETHSource.serializeGraph G)).length (EncodedETHSource.serializeGraph G) +
      WeightedVertexWord.vertexBound (EncodedETHSource.serializeGraph G) + 1 := rfl
  have hact := ClockF.level_actual G c A d Δ n γ hcommon hlower hupper hrep 0 hk0
  -- the level-0 composite clock
  have hb0 : WeightedLevel0Clean.bound0 (CutoffBitMachine.actualMachine c A d) G n c ≤
      WeightedRawWordsClock.rawC (CutoffBitMachine.actualMachine c A d) c *
            ((SourceOriginalBranchPackets.packet n
              (EncodedGraph.encode (EncodedETHSource.serializeGraph G))).length + 1) ^ 128 +
          110 * ((SourceOriginalBranchPackets.packet n
              (EncodedGraph.encode (EncodedETHSource.serializeGraph G))).length + 1) ^ 3 + 1 +
          ((1 + 9 * ps) * (2 * ((SourceOriginalBranchPackets.packet n
              (EncodedGraph.encode (EncodedETHSource.serializeGraph G))).length + 1) ^ Cp *
            FinalPadding.tableSize (ETHTailGrowth.repetitions c A d) n ^ Cp) + 14 +
          W12RowTime.Krow * (ClockK.KE c A * ((((SourceOriginalBranchPackets.packet n
              (EncodedGraph.encode (EncodedETHSource.serializeGraph G))).length + 1) ^ (d + 1) *
              FinalPadding.tableSize (ETHTailGrowth.repetitions c A d) n) *
            (((SourceOriginalBranchPackets.packet n
              (EncodedGraph.encode (EncodedETHSource.serializeGraph G))).length + 1) ^ (d + 1) *
              FinalPadding.tableSize (ETHTailGrowth.repetitions c A d) n)) + 1) ^ 9) := by
    rw [hps, hRW]
    generalize (pbJ (⟨V, E, G, c, EffectiveIteration.sourceDepth n,
      StepP.yP G c (EffectiveIteration.sourceDepth n) 0, 0,
      StepP.MP G c (EffectiveIteration.sourceDepth n) 0⟩ : LI)) = x at hpb ⊢
    generalize (2 * ((SourceOriginalBranchPackets.packet n
          (EncodedGraph.encode (EncodedETHSource.serializeGraph G))).length + 1) ^ Cp *
        FinalPadding.tableSize (ETHTailGrowth.repetitions c A d) n ^ Cp) = B at hpb ⊢
    have h9 : 9 * (ps * x) ≤ 9 * (ps * B) := Nat.mul_le_mul_left 9 (Nat.mul_le_mul_left ps hpb)
    have e : (1 + 9 * ps) * B = B + 9 * (ps * B) := by ring
    rw [e]
    omega
  rw [ready_split, hps2]
  generalize WeightedLevel0Clean.bound0 (CutoffBitMachine.actualMachine c A d) G n c = x at hb0 ⊢
  generalize (WeightedRawWordsClock.rawC (CutoffBitMachine.actualMachine c A d) c *
            ((SourceOriginalBranchPackets.packet n
              (EncodedGraph.encode (EncodedETHSource.serializeGraph G))).length + 1) ^ 128 +
          110 * ((SourceOriginalBranchPackets.packet n
              (EncodedGraph.encode (EncodedETHSource.serializeGraph G))).length + 1) ^ 3 + 1 +
          ((1 + 9 * ps) * (2 * ((SourceOriginalBranchPackets.packet n
              (EncodedGraph.encode (EncodedETHSource.serializeGraph G))).length + 1) ^ Cp *
            FinalPadding.tableSize (ETHTailGrowth.repetitions c A d) n ^ Cp) + 14 +
          W12RowTime.Krow * (ClockK.KE c A * ((((SourceOriginalBranchPackets.packet n
              (EncodedGraph.encode (EncodedETHSource.serializeGraph G))).length + 1) ^ (d + 1) *
              FinalPadding.tableSize (ETHTailGrowth.repetitions c A d) n) *
            (((SourceOriginalBranchPackets.packet n
              (EncodedGraph.encode (EncodedETHSource.serializeGraph G))).length + 1) ^ (d + 1) *
              FinalPadding.tableSize (ETHTailGrowth.repetitions c A d) n)) + 1) ^ 9)) = B at hb0 ⊢
  have hm : WeightedLevel0Clean.nClear * (ps2 * x) ≤ WeightedLevel0Clean.nClear * (ps2 * B) :=
    Nat.mul_le_mul_left _ (Nat.mul_le_mul_left ps2 hb0)
  have e : (1 + WeightedLevel0Clean.nClear * ps2) * B = B + WeightedLevel0Clean.nClear * (ps2 * B) := by ring
  rw [e]
  omega

#print axioms vertexBound_le
#print axioms bound0_split
#print axioms clean_split
#print axioms ready_split
#print axioms ready0_level

end
end EthInapproximability.CurrentPaper.W12Ready0
