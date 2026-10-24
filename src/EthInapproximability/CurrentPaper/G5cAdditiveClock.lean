import EthInapproximability.CurrentPaper.G5cShellRun
import EthInapproximability.CurrentPaper.G5cPowBound

/-!
# The shell run with the lock's ADDITIVE round shape `(k+1) 2^{F p}` (private lane owner:b-g5-3)

Segment 1. From `G5cShellRun.shell_run_discharged` (uniform constants, level-0 writer discharged)
and the extra premise

  `hsize : |enc G| + 1 ≤ (n + 2)^D`   (`|enc G| = ell3 G`, `D` a FIXED exponent),

the round part `(k - 1) * (T + 1) + 1 + 1` of the proved clock,
`T = (n + |enc G| + 2)^Cw + 2^(Cw p) + roundRest(|enc G|, p)`, is at most `(k + 1) 2^(F p) + 2`
with ONE `F` depending only on `D` (quantified before `M`, the graph types, `G`, `n`, `c`, `k`,
`p`). Proof: with `Y = 2^(p (D+1))`, `n + 2 ≤ 2^p` (from `clog(n+2) ≤ p`) and
`|enc G| < (2^p)^D` put every atom `2^p, n, |enc G|` below `Y`, and `G5cPowBound.clock_le_pow`
gives `T + 1 ≤ Y^N`.

`hsize` is NOT among the named premises (`LevelNamed`/`SourceNames`); it is the reading of the
lock's proof sentence (B-effectivity-details.tex:157-158) "Graph processing costs polynomial time in
n per entry, absorbed by p >= log n", which presupposes `|enc G| ≤ n^{O(1)}`. Without it the
proved round part is `(k - 1) * (poly(n, |enc G|) + 2^{O(p)})` (see `G5cShellRun`); the terms that
prevent the additive form are the `|enc G|`-dependent summands of `T` listed in `G5cShellNamed`.

Still present: the level-0 term `level0BoundP M G n c (T22zero G n c) + installBoundP 0 + 1`
(unbounded here; it contains the `M`-clock stage), the fuel PRELOADED with unary `k - 1`, and the
named premises `LevelNamed` at every round level.
-/

noncomputable section

namespace EthInapproximability.CurrentPaper.G5cAdditiveClock

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

private theorem from_clog' {x p : ℕ} (h : Nat.clog 2 x ≤ p) : x ≤ 2 ^ p :=
  (Nat.le_pow_clog (by decide : 1 < (2 : ℕ)) _).trans
    (Nat.pow_le_pow_right (by decide) h)

variable [Fintype BStack] [Fintype MatrixTableInterlaceProtectedBridge.Label]

/-- The round-part arithmetic: `(k-1)(T+1) + 1 + 1 ≤ (k+1) 2^(F p) + 2`. -/
theorem round_part_additive (Cw C ps ps3 K D : ℕ) :
    ∃ F : ℕ, ∀ n ell k p : ℕ, Nat.clog 2 (n + 2) ≤ p → ell + 1 ≤ (n + 2) ^ D →
      (k - 1) * ((((n + ell + 2) ^ Cw + 2 ^ (Cw * p)) +
          G5bRoundClockNamed.roundRest C ps ps3 K ell p) + 1) + 1 + 1 ≤
        (k + 1) * 2 ^ (F * p) + 2 := by
  obtain ⟨N, hN⟩ := G5cPowBound.clock_le_pow Cw C ps ps3 K
  refine ⟨(D + 1) * N, fun n ell k p hfloor hsize => ?_⟩
  have hn2 : n + 2 ≤ 2 ^ p := from_clog' hfloor
  have hp1 : 1 ≤ p := le_trans (Nat.clog_pos (by decide) (by omega)) hfloor
  set Y := 2 ^ (p * (D + 1)) with hYdef
  have h2p : 2 ≤ 2 ^ p := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ p := Nat.pow_le_pow_right (by decide) hp1
  have hPY : 2 ^ p ≤ Y := Nat.pow_le_pow_right (by decide) (Nat.le_mul_of_pos_right p (by omega))
  have hY : 2 ≤ Y := le_trans h2p hPY
  have hnY : n ≤ Y := by omega
  have hellY : ell ≤ Y := by
    have h1 : (n + 2) ^ D ≤ (2 ^ p) ^ D := Nat.pow_le_pow_left hn2 D
    have h2 : (2 ^ p) ^ D ≤ Y := by
      rw [← pow_mul]; exact Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_left p (by omega))
    omega
  have hT := hN Y p n ell hY hPY hnY hellY
  have hYN : Y ^ N = 2 ^ ((D + 1) * N * p) := by
    rw [hYdef, ← pow_mul]; congr 1; ring
  rw [hYN] at hT
  have hk : (k - 1) * ((((n + ell + 2) ^ Cw + 2 ^ (Cw * p)) +
        G5bRoundClockNamed.roundRest C ps ps3 K ell p) + 1) ≤ (k + 1) * 2 ^ ((D + 1) * N * p) :=
    Nat.mul_le_mul (by omega) hT
  omega

#print axioms round_part_additive

theorem shell_run_additive (D : ℕ) :
    ∃ F : ℕ, ∀ (M : BitMachine.Machine) {V E : Type} [Fintype V] [DecidableEq V]
      [Fintype E] [DecidableEq E] (G : EndpointGraph V E) (n c k p : ℕ), 1 ≤ c → 1 ≤ k →
      Nat.clog 2 (n + 2) ≤ p →
      ell3 G + 1 ≤ (n + 2) ^ D →
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
          ext5 (Bk M G n c k) []⟩   := by
  obtain ⟨Cw, C, ps, ps3, K, h⟩ := G5cShellRun.shell_run_discharged
  obtain ⟨F, hF⟩ := round_part_additive Cw C ps ps3 K D
  refine ⟨F, fun M {V E} _ _ _ _ G n c k p hc hk hfloor hsize hnamed => ?_⟩
  obtain ⟨t, ht, hrun⟩ := h M G n c k p hc hk hfloor hnamed
  refine ⟨t, ?_, hrun⟩
  have := hF n (ell3 G) k p hfloor hsize
  omega

#print axioms shell_run_additive

end EthInapproximability.CurrentPaper.G5cAdditiveClock
