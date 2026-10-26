import EthInapproximability.CurrentPaper.G5cAdditiveClock

/-!
# Additive round shape from vertex/edge NAMING premises (private lane owner:b-g5-3)

Segment 1, second reading. Instead of `|enc G| + 1 ≤ (n+2)^D`, assume that the vertex and edge
indices of `G` are named within `p` bits (`|V| ≤ 2^p`, `|E| ≤ 2^p`; the lock's naming premise
B-effectivity-details.tex:90-92 "p ... bounds every intermediate input's and internal index's
binary naming length", read as covering vertex and edge indices). The admitted
`EncodedGraph.encode_length_upper` then gives `|enc G| + 1 ≤ 2^(6p)`, and the round part of the
shell clock is `(k + 1) 2^(F p) + 2` with ONE absolute `F` (no exponent `D` left).
-/

noncomputable section

namespace EthInapproximability.CurrentPaper.G5cAdditiveNamed

open Turing BitMachineEncoding BitMachineStackEmbedding
open EthInapproximability.ParameterizedNP.GuardedSourceGraph
open WeightedLevel0Rows WeightedLevel0Persist WeightedLevel0Clean WeightedLevel0Target
open WeightedLevel0Ready WeightedLevel0WriterRun LevelJRows LevelJPersist LevelJClean LevelJReady
open LevelJMasters OuterLevel0Prep OuterLevel0Run LevelJPrep OuterLevel0Bridge LevelJBridge
open OuterLevel0Full NextMasterWords CostUpdateStages CostUpdateMachine CostUpdateEmbed
open Level0CostRound Level0CostRun Level0DimsRound Level0DimsClean RoundP CleanP ExitP StepP
open Level0Install KShell
open LevelJRound (Dmw Dmw_other)
open RoundInstall (installProgram installCtrl)
open EntryPrepCopy EntryPrepVec EntryPrepFamily EntryPrepVecJ EntryWriter22J
open EntryClockPoly3 (ell3)

set_option maxHeartbeats 3000000
set_option maxRecDepth 8192
set_option synthInstance.maxSize 200000
set_option synthInstance.maxHeartbeats 2000000

private theorem from_clog'' {x p : ℕ} (h : Nat.clog 2 x ≤ p) : x ≤ 2 ^ p :=
  (Nat.le_pow_clog (by decide : 1 < (2 : ℕ)) _).trans
    (Nat.pow_le_pow_right (by decide) h)

/-- `|enc G| + 1 ≤ 2^(6p)` from `|V|, |E| ≤ 2^p`, `p ≥ 1` (admitted `encode_length_upper`). -/
theorem ell3_le_of_names {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : EndpointGraph V E) (p : ℕ) (hp : 1 ≤ p) (hV : Fintype.card V ≤ 2 ^ p)
    (hE : Fintype.card E ≤ 2 ^ p) : ell3 G + 1 ≤ 2 ^ (6 * p) := by
  have h := EncodedGraph.encode_length_upper (EncodedETHSource.serializeGraph G)
    (EncodedETHSource.serializeGraph_valid G)
  rw [EncodedETHSource.serializeGraph_vertices, EncodedETHSource.serializeGraph_edges] at h
  have hP : 2 ≤ 2 ^ p := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ p := Nat.pow_le_pow_right (by decide) hp
  have h6 : 2 ^ (6 * p) = (2 ^ p) ^ 6 := by rw [← pow_mul, mul_comm]
  rw [h6]
  unfold ell3
  set P := 2 ^ p
  have h1 : Fintype.card E * (4 * Fintype.card V + 4) ≤ P * (4 * P + 4) :=
    Nat.mul_le_mul hE (by omega)
  have hP2 : 4 ≤ P ^ 2 := by nlinarith
  have hP4 : 16 ≤ P ^ 4 := by
    have : P ^ 4 = P ^ 2 * P ^ 2 := by ring
    nlinarith
  have hsq : P ^ 2 = P * P := by ring
  have h6' : P ^ 6 = P ^ 2 * P ^ 4 := by ring
  have h2 : P * (4 * P + 4) + P + 3 ≤ P ^ 6 := by nlinarith
  omega

#print axioms ell3_le_of_names

variable [Fintype BStack] [Fintype MatrixTableInterlaceProtectedBridge.Label]

theorem round_part_additive_pow (Cw C ps ps3 K D : ℕ) :
    ∃ F : ℕ, ∀ n ell k p : ℕ, Nat.clog 2 (n + 2) ≤ p → ell + 1 ≤ 2 ^ (D * p) →
      (k - 1) * ((((n + ell + 2) ^ Cw + 2 ^ (Cw * p)) +
          G5bRoundClockNamed.roundRest C ps ps3 K ell p) + 1) + 1 + 1 ≤
        (k + 1) * 2 ^ (F * p) + 2 := by
  obtain ⟨N, hN⟩ := G5cPowBound.clock_le_pow Cw C ps ps3 K
  refine ⟨(D + 1) * N, fun n ell k p hfloor hsize => ?_⟩
  have hn2 : n + 2 ≤ 2 ^ p := from_clog'' hfloor
  have hp1 : 1 ≤ p := le_trans (Nat.clog_pos (by decide) (by omega)) hfloor
  set Y := 2 ^ (p * (D + 1)) with hYdef
  have h2p : 2 ≤ 2 ^ p := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ p := Nat.pow_le_pow_right (by decide) hp1
  have hPY : 2 ^ p ≤ Y := Nat.pow_le_pow_right (by decide) (Nat.le_mul_of_pos_right p (by omega))
  have hY : 2 ≤ Y := le_trans h2p hPY
  have hnY : n ≤ Y := by omega
  have hellY : ell ≤ Y := by
    have h2 : 2 ^ (D * p) ≤ Y :=
      Nat.pow_le_pow_right (by decide) (by rw [mul_comm]; exact Nat.mul_le_mul_left p (by omega))
    omega
  have hT := hN Y p n ell hY hPY hnY hellY
  have hYN : Y ^ N = 2 ^ ((D + 1) * N * p) := by
    rw [hYdef, ← pow_mul]; congr 1; ring
  rw [hYN] at hT
  have hk : (k - 1) * ((((n + ell + 2) ^ Cw + 2 ^ (Cw * p)) +
        G5bRoundClockNamed.roundRest C ps ps3 K ell p) + 1) ≤ (k + 1) * 2 ^ ((D + 1) * N * p) :=
    Nat.mul_le_mul (by omega) hT
  omega

#print axioms round_part_additive_pow

theorem shell_run_additive_named :
    ∃ F : ℕ, ∀ (M : BitMachine.Machine) {V E : Type} [Fintype V] [DecidableEq V]
      [Fintype E] [DecidableEq E] (G : EndpointGraph V E) (n c k p : ℕ), 1 ≤ c → 1 ≤ k →
      Nat.clog 2 (n + 2) ≤ p →
      Fintype.card V ≤ 2 ^ p → Fintype.card E ≤ 2 ^ p →
      (∀ j, 1 ≤ j → j < k →
        G5cShellNamed.LevelNamed G c (EffectiveIteration.sourceDepth n) j p) →
    ∃ t ≤ (level0BoundP M G n c (ClockO.T22zero G n c) + installBoundP G c (EffectiveIteration.sourceDepth n) 0 + 1) +
        ((k + 1) * 2 ^ (F * p) + 2),
      ((advance (shellProgram M c ClockO.W0prog ClockO.w00 ClockO.v00 (writerJ progF
          (BitMachineRawSequence.leftLabel (MultiMove.startLabel (jobsA.map CopyFill.toJob)))
          (MultiMove.initial, ((), (MultiMove.initial, (EntryFamilyLevel.initialControl,
            (MultiMove.initial, ((none : Option Bool), ((), (none : Option Bool)))))))))
          (BitMachineRawSequence.leftLabel (MultiMove.startLabel (jobs55.map CopyFill.toJob)))
          (MultiMove.initial, (prepInit ((MultiMove.initial, false),
            (MultiMove.initial, ((), (MultiMove.initial, (EntryFamilyLevel.initialControl,
              (MultiMove.initial, ((none : Option Bool), ((), (none : Option Bool))))))))),
          (RawTableTail.startControl EntryRunsRaw.startControl, ((), (none : Option Bool)))))))^[t])
          ⟨some (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel (.inl (.scan 0)))))))))))),
            (((((((((((none, ((), ((WeightedRawWords.level0Ctrl, (WeightedRawWords.edgesCtrl, WeightedRawWords.tailCtrl)), WeightedRawWords.kCtrl M))), WeightedVertexWord.vertexCtrl), (WeightedLevelFields15.initialControl, (((), none), WeightedRowFields.rowInit))), ((), none)), ((none : Option Bool), ((none : Option Bool), ((), none)))), ctrl27), (ClockO.v00, (costCtrl, (NextDimsMachineTN.dimsCtrl, bridgeCtrl)))), (none, ((), none))), installCtrl)),
              (none, (((((((WeightedLevelFields15.initialControl, (((), none), WeightedRowFields.rowInit)), ((), none)), ((none : Option Bool), ((none : Option Bool), ((), none)))), ctrl27), ((MultiMove.initial, (prepInit ((MultiMove.initial, false),
            (MultiMove.initial, ((), (MultiMove.initial, (EntryFamilyLevel.initialControl,
              (MultiMove.initial, ((none : Option Bool), ((), (none : Option Bool))))))))),
          (RawTableTail.startControl EntryRunsRaw.startControl, ((), (none : Option Bool))))), (costCtrl, (NextDimsMachineTN.dimsCtrl, bridgeCtrl)))), (((), none), (none, ((), none)))), installCtrl))),
            ext5 (ext4 (H0 (SourceOriginalBranchPackets.packet n
              (EncodedGraph.encode (EncodedETHSource.serializeGraph G)))) blank57)
              (List.replicate (k - 1) true)⟩ =
        ⟨none,
          (((((((((((none, ((), ((WeightedRawWords.level0Ctrl, (WeightedRawWords.edgesCtrl, WeightedRawWords.tailCtrl)), WeightedRawWords.kCtrl M))), WeightedVertexWord.vertexCtrl), (WeightedLevelFields15.initialControl, (((), none), WeightedRowFields.rowInit))), ((), none)), ((none : Option Bool), ((none : Option Bool), ((), none)))), ctrl27), (ClockO.v00, (costCtrl, (NextDimsMachineTN.dimsCtrl, bridgeCtrl)))), (none, ((), none))), installCtrl)),
            (none, (((((((WeightedLevelFields15.initialControl, (((), none), WeightedRowFields.rowInit)), ((), none)), ((none : Option Bool), ((none : Option Bool), ((), none)))), ctrl27), ((MultiMove.initial, (prepInit ((MultiMove.initial, false),
            (MultiMove.initial, ((), (MultiMove.initial, (EntryFamilyLevel.initialControl,
              (MultiMove.initial, ((none : Option Bool), ((), (none : Option Bool))))))))),
          (RawTableTail.startControl EntryRunsRaw.startControl, ((), (none : Option Bool))))), (costCtrl, (NextDimsMachineTN.dimsCtrl, bridgeCtrl)))), (((), none), (none, ((), none)))), installCtrl))),
          ext5 (Bk M G n c k) []⟩    := by
  obtain ⟨Cw, C, ps, ps3, K, h⟩ := G5cShellRun.shell_run_discharged
  obtain ⟨F, hF⟩ := round_part_additive_pow Cw C ps ps3 K 6
  refine ⟨F, fun M {V E} _ _ _ _ G n c k p hc hk hfloor hV hE hnamed => ?_⟩
  obtain ⟨t, ht, hrun⟩ := h M G n c k p hc hk hfloor hnamed
  refine ⟨t, ?_, hrun⟩
  have hp1 : 1 ≤ p := le_trans (Nat.clog_pos (by decide) (by omega)) hfloor
  have := hF n (ell3 G) k p hfloor (ell3_le_of_names G p hp1 hV hE)
  omega

#print axioms shell_run_additive_named

end EthInapproximability.CurrentPaper.G5cAdditiveNamed
