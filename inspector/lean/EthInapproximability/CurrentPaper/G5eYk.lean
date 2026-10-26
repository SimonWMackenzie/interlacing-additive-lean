import EthInapproximability.CurrentPaper.G5eYkCore

/-!
# The k-input shell with the input `k` KEPT and unary `y_k` emitted (private lane owner:b-g5-5,
# segment 3, part a)

`yk_additive`: ONE fixed program `G5eYkCore.ykProgram (G5cKInput.kProgram M c) … kv0` (copy the
input `k` from the fuel cell into `zc 0`; the k-input shell lifted to `H8`; copy consumer raw word 2
(unary `y_k + k`) into `zc 2`; pop `zc 0` and `zc 2` together), started with the branch packet in
`H0`, unary `k` in the fuel cell and three blank cells, halts with the exact level-`k` bank
`ext5 (KShell.Bk M G n c k) []` in the shell region, `zc 0 = zc 1 = []` and `zc 2 = unary y_k`
(`y_k = (physRun … k).budget`), within the additive clock `(n + |enc G| + 1)^N + (k+1) 2^(F p)`.
Master `K` (dead scratch `kValue M n`) is never read by this emission.

The control text `kv0` (the start control of `kProgram`) is copied verbatim by `assemble_yk.py`.
-/

noncomputable section

namespace EthInapproximability.CurrentPaper.G5eYk

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

/-- Absorb the emission charges `5 * 2^p + 8` into `(k+1) 2^((F+5) p)`. -/
theorem absorbE (k p F : ℕ) (hp : 1 ≤ p) :
    (k + 1) * 2 ^ (F * p) + (5 * 2 ^ p + 8) ≤ (k + 1) * 2 ^ ((F + 5) * p) := by
  have e : 2 ^ ((F + 5) * p) = 2 ^ (F * p) * 2 ^ (5 * p) := by
    rw [← pow_add]; congr 1; ring
  have e5 : 2 ^ (5 * p) = 2 ^ p * 2 ^ (4 * p) := by
    rw [← pow_add]; congr 1; ring
  have hA : 1 ≤ 2 ^ (F * p) := Nat.one_le_two_pow
  have hD : 2 ≤ 2 ^ p := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ p := Nat.pow_le_pow_right (by decide) hp
  have h16 : 16 ≤ 2 ^ (4 * p) := by
    calc 16 = 2 ^ 4 := by norm_num
      _ ≤ 2 ^ (4 * p) := Nat.pow_le_pow_right (by decide) (by omega)
  rw [e, e5]
  generalize 2 ^ (F * p) = A at hA ⊢
  generalize 2 ^ p = D at hD ⊢
  generalize 2 ^ (4 * p) = Q at h16 ⊢
  have h1 : 16 * D ≤ D * Q := by nlinarith
  have hAQ : D * Q ≤ A * (D * Q) := Nat.le_mul_of_pos_left _ hA
  generalize hZ : (k + 1) * A = Z
  have hZ1 : 1 ≤ Z := by rw [← hZ]; nlinarith
  have e2 : (k + 1) * (A * (D * Q)) = Z * (D * Q) := by rw [← hZ]; ring
  rw [e2]
  have h3 : Z * (16 * D) ≤ Z * (D * Q) := Nat.mul_le_mul_left _ h1
  nlinarith

variable [Fintype BStack] [Fintype MatrixTableInterlaceProtectedBridge.Label]

/-- **Segment 3a.** The k-input shell with `k` kept and unary `y_k` emitted, additive clock. -/
theorem yk_additive (M : BitMachine.Machine) (c : ℕ) :
    ∃ N F : ℕ, ∀ {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
      (G : EndpointGraph V E) (n k p : ℕ), 1 ≤ c → 1 ≤ k →
      Nat.clog 2 (n + 2) ≤ p →
      Fintype.card V ≤ 2 ^ p → Fintype.card E ≤ 2 ^ p →
      (∀ j, j < k → G5cShellNamed.LevelNamed G c (EffectiveIteration.sourceDepth n) j p) →
    ∃ t ≤ (n + (EncodedGraph.encode (EncodedETHSource.serializeGraph G)).length + 1) ^ N +
        (k + 1) * 2 ^ (F * p),
      ((advance (G5eYkCore.ykProgram (G5cKInput.kProgram M c) (BitMachineRawSequence.leftLabel ())
          (((), (((((((((((none, ((), ((WeightedRawWords.level0Ctrl, (WeightedRawWords.edgesCtrl, WeightedRawWords.tailCtrl)), WeightedRawWords.kCtrl M))), WeightedVertexWord.vertexCtrl), (WeightedLevelFields15.initialControl, (((), none), WeightedRowFields.rowInit))), ((), none)), ((none : Option Bool), ((none : Option Bool), ((), none)))), ctrl27), (ClockO.v00, (costCtrl, (NextDimsMachineTN.dimsCtrl, bridgeCtrl)))), (none, ((), none))), installCtrl)),
              (none, (((((((WeightedLevelFields15.initialControl, (((), none), WeightedRowFields.rowInit)), ((), none)), ((none : Option Bool), ((none : Option Bool), ((), none)))), ctrl27), ((MultiMove.initial, (prepInit ((MultiMove.initial, false),
            (MultiMove.initial, ((), (MultiMove.initial, (EntryFamilyLevel.initialControl,
              (MultiMove.initial, ((none : Option Bool), ((), (none : Option Bool))))))))),
          (RawTableTail.startControl EntryRunsRaw.startControl, ((), (none : Option Bool))))), (costCtrl, (NextDimsMachineTN.dimsCtrl, bridgeCtrl)))), (((), none), (none, ((), none)))), installCtrl)))))))^[t])
        ⟨some (BitMachineRawSequence.leftLabel .scan), (none, ((((), (((((((((((none, ((), ((WeightedRawWords.level0Ctrl, (WeightedRawWords.edgesCtrl, WeightedRawWords.tailCtrl)), WeightedRawWords.kCtrl M))), WeightedVertexWord.vertexCtrl), (WeightedLevelFields15.initialControl, (((), none), WeightedRowFields.rowInit))), ((), none)), ((none : Option Bool), ((none : Option Bool), ((), none)))), ctrl27), (ClockO.v00, (costCtrl, (NextDimsMachineTN.dimsCtrl, bridgeCtrl)))), (none, ((), none))), installCtrl)),
              (none, (((((((WeightedLevelFields15.initialControl, (((), none), WeightedRowFields.rowInit)), ((), none)), ((none : Option Bool), ((none : Option Bool), ((), none)))), ctrl27), ((MultiMove.initial, (prepInit ((MultiMove.initial, false),
            (MultiMove.initial, ((), (MultiMove.initial, (EntryFamilyLevel.initialControl,
              (MultiMove.initial, ((none : Option Bool), ((), (none : Option Bool))))))))),
          (RawTableTail.startControl EntryRunsRaw.startControl, ((), (none : Option Bool))))), (costCtrl, (NextDimsMachineTN.dimsCtrl, bridgeCtrl)))), (((), none), (none, ((), none)))), installCtrl))))), (none, none))),
          G5eYkCore.ext8 (ext5 (ext4 (H0 (SourceOriginalBranchPackets.packet n
            (EncodedGraph.encode (EncodedETHSource.serializeGraph G)))) blank57)
            (List.replicate k true)) (fun _ => [])⟩ =
        ⟨none, (none, ((((), (((((((((((none, ((), ((WeightedRawWords.level0Ctrl, (WeightedRawWords.edgesCtrl, WeightedRawWords.tailCtrl)), WeightedRawWords.kCtrl M))), WeightedVertexWord.vertexCtrl), (WeightedLevelFields15.initialControl, (((), none), WeightedRowFields.rowInit))), ((), none)), ((none : Option Bool), ((none : Option Bool), ((), none)))), ctrl27), (ClockO.v00, (costCtrl, (NextDimsMachineTN.dimsCtrl, bridgeCtrl)))), (none, ((), none))), installCtrl)),
              (none, (((((((WeightedLevelFields15.initialControl, (((), none), WeightedRowFields.rowInit)), ((), none)), ((none : Option Bool), ((none : Option Bool), ((), none)))), ctrl27), ((MultiMove.initial, (prepInit ((MultiMove.initial, false),
            (MultiMove.initial, ((), (MultiMove.initial, (EntryFamilyLevel.initialControl,
              (MultiMove.initial, ((none : Option Bool), ((), (none : Option Bool))))))))),
          (RawTableTail.startControl EntryRunsRaw.startControl, ((), (none : Option Bool))))), (costCtrl, (NextDimsMachineTN.dimsCtrl, bridgeCtrl)))), (((), none), (none, ((), none)))), installCtrl))))), (none, none))),
          G5eYkCore.ext8 (ext5 (Bk M G n c k) [])
            ![[], [], List.replicate (PhysicalLevelRun.physRun G c (EffectiveIteration.sourceDepth n)
              (Iteration.seedState (EffectiveIteration.sourceDepth n)) k).budget true]⟩ := by
  obtain ⟨N, F, hK⟩ := G5eLevel0.k_input_additive_names M c
  refine ⟨N, F + 5, fun {V E} _ _ _ _ G n k p hc hk hfloor hV hE hnamed => ?_⟩
  obtain ⟨t, ht, hrun⟩ := hK G n k p hc hk hfloor hV hE hnamed
  have hY : Bk M G n c k (RoundInstall.consH (WeightedRawWords.consRaw 2)) =
      List.replicate ((PhysicalLevelRun.physRun G c (EffectiveIteration.sourceDepth n)
        (Iteration.seedState (EffectiveIteration.sourceDepth n)) k).budget + k) true :=
    Emission.Bk_raw M G n c k 2
  obtain ⟨u, hu, hr⟩ := G5eYkCore.yk_core_run (G5cKInput.kProgram M c) _ _ _ _ _ k _ t hrun hY
  -- `y_k + k ≤ 2^p` from the next-state name of level `k - 1`
  obtain ⟨-, -, -, -, -, hy, -, -⟩ := hnamed (k - 1) (by omega)
  have hk1 : k - 1 + 1 = k := by omega
  rw [hk1] at hy
  have hyk : (PhysicalLevelRun.physRun G c (EffectiveIteration.sourceDepth n)
      (Iteration.seedState (EffectiveIteration.sourceDepth n)) k).budget + k ≤ 2 ^ p :=
    (Nat.le_pow_clog (by decide : 1 < 2) _).trans (Nat.pow_le_pow_right (by decide) hy)
  have hp : 1 ≤ p := by
    have := Nat.clog_pos (by decide : 1 < 2) (by omega : 1 < n + 2)
    omega
  have hab := absorbE k p F hp
  exact ⟨u, by omega, hr⟩

#print axioms absorbE
#print axioms yk_additive

end EthInapproximability.CurrentPaper.G5eYk
