import EthInapproximability.CurrentPaper.G5dLevel0

/-!
# The k-input shell with the lock's ADDITIVE clock, level 0 included (private lane owner:b-g5-4)

ONE fixed program `G5cKInput.kProgram M c` (b-g5-owner-3: pop one fuel bit, then the admitted shell
`KShell.shellProgram`), started with the branch packet `SourceOriginalBranchPackets.packet n (enc G)`
in `H0` and unary `k` (`k ≥ 1`) in the fuel cell, halts on the exact level-`k` bank
`ext5 (KShell.Bk M G n c k) []` within

  `(n + |enc G| + 1)^N + (k + 1) * 2^(F p)`,

with `N F` chosen after the fixed program data `(M, c)` and before the graph types, `G`, `n`, `k`, `p`.
Premises: `1 ≤ c`, `1 ≤ k`, `clog(n+2) ≤ p`, `|V|, |E| ≤ 2^p` (owner-3's naming reading of vertex and
edge indices), the level-0 naming envelope `oneLevelBound (EntryClockPoly.P0 G n c) ≤ p`, and the named
premise `LevelNamed` at every physical level `0 ≤ j < k`.

The configuration text below is copied verbatim from the frozen `G5cKInput.k_input_run` by
`assemble_kadditive.py`.

NOT claimed: the parser of an encoded `(n, G, k, p)`; the pad join; `y_k` emission.
-/

noncomputable section

namespace EthInapproximability.CurrentPaper.G5dKAdditive

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

/-- Absorb the level-0 exponential term and the constants into `(k+1) 2^(F p)`. -/
theorem absorb (k p F0 N : ℕ) (hp : 1 ≤ p) :
    2 ^ (N * p) + ((k + 1) * 2 ^ (F0 * p) + 2) + 2 ≤ (k + 1) * 2 ^ ((F0 + N + 3) * p) := by
  have e : 2 ^ ((F0 + N + 3) * p) = 2 ^ (F0 * p) * 2 ^ (N * p) * 2 ^ (3 * p) := by
    rw [add_mul, add_mul, pow_add, pow_add]
  rw [e]
  have hA : 1 ≤ 2 ^ (F0 * p) := Nat.one_le_two_pow
  have hB : 1 ≤ 2 ^ (N * p) := Nat.one_le_two_pow
  have hD : 8 ≤ 2 ^ (3 * p) := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ (3 * p) := Nat.pow_le_pow_right (by decide) (by omega)
  generalize 2 ^ (F0 * p) = A at hA ⊢
  generalize 2 ^ (N * p) = B at hB ⊢
  generalize 2 ^ (3 * p) = D at hD ⊢
  have h1 : A * B * 8 ≤ A * B * D := Nat.mul_le_mul_left _ hD
  have h2 : A ≤ A * B := Nat.le_mul_of_pos_right _ hB
  have h3 : B ≤ A * B := Nat.le_mul_of_pos_left _ hA
  have h4 : (k + 1) * (A * B * 8) ≤ (k + 1) * (A * B * D) := Nat.mul_le_mul_left _ h1
  have h5 : (k + 1) * A ≤ (k + 1) * (A * B) := Nat.mul_le_mul_left _ h2
  have h6 : 1 * 1 ≤ A * B := Nat.mul_le_mul hA hB
  have h7 : B ≤ (k + 1) * (A * B) := le_trans h3 (Nat.le_mul_of_pos_left _ (by omega))
  have h8 : 1 * 1 ≤ (k + 1) * (A * B) := le_trans h6 (Nat.le_mul_of_pos_left _ (by omega))
  have e2 : (k + 1) * (A * B * 8) = 8 * ((k + 1) * (A * B)) := by ring
  omega

variable [Fintype BStack] [Fintype MatrixTableInterlaceProtectedBridge.Label]

/-- **The k-input shell, level 0 included, with the additive clock.** -/
theorem k_input_additive (M : BitMachine.Machine) (c : ℕ) :
    ∃ N F : ℕ, ∀ {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
      (G : EndpointGraph V E) (n k p : ℕ), 1 ≤ c → 1 ≤ k →
      Nat.clog 2 (n + 2) ≤ p →
      Fintype.card V ≤ 2 ^ p → Fintype.card E ≤ 2 ^ p →
      EffectiveIteration.oneLevelBound (EntryClockPoly.P0 G n c) ≤ p →
      (∀ j, j < k → G5cShellNamed.LevelNamed G c (EffectiveIteration.sourceDepth n) j p) →
    ∃ t ≤ (n + (EncodedGraph.encode (EncodedETHSource.serializeGraph G)).length + 1) ^ N +
        (k + 1) * 2 ^ (F * p),
      ((advance (G5cKInput.kProgram M c))^[t])
        ⟨some (BitMachineRawSequence.leftLabel ()), ((), (((((((((((none, ((), ((WeightedRawWords.level0Ctrl, (WeightedRawWords.edgesCtrl, WeightedRawWords.tailCtrl)), WeightedRawWords.kCtrl M))), WeightedVertexWord.vertexCtrl), (WeightedLevelFields15.initialControl, (((), none), WeightedRowFields.rowInit))), ((), none)), ((none : Option Bool), ((none : Option Bool), ((), none)))), ctrl27), (ClockO.v00, (costCtrl, (NextDimsMachineTN.dimsCtrl, bridgeCtrl)))), (none, ((), none))), installCtrl)),
              (none, (((((((WeightedLevelFields15.initialControl, (((), none), WeightedRowFields.rowInit)), ((), none)), ((none : Option Bool), ((none : Option Bool), ((), none)))), ctrl27), ((MultiMove.initial, (prepInit ((MultiMove.initial, false),
            (MultiMove.initial, ((), (MultiMove.initial, (EntryFamilyLevel.initialControl,
              (MultiMove.initial, ((none : Option Bool), ((), (none : Option Bool))))))))),
          (RawTableTail.startControl EntryRunsRaw.startControl, ((), (none : Option Bool))))), (costCtrl, (NextDimsMachineTN.dimsCtrl, bridgeCtrl)))), (((), none), (none, ((), none)))), installCtrl)))),
          ext5 (ext4 (H0 (SourceOriginalBranchPackets.packet n
            (EncodedGraph.encode (EncodedETHSource.serializeGraph G)))) blank57)
            (List.replicate k true)⟩ =
        ⟨none, ((), (((((((((((none, ((), ((WeightedRawWords.level0Ctrl, (WeightedRawWords.edgesCtrl, WeightedRawWords.tailCtrl)), WeightedRawWords.kCtrl M))), WeightedVertexWord.vertexCtrl), (WeightedLevelFields15.initialControl, (((), none), WeightedRowFields.rowInit))), ((), none)), ((none : Option Bool), ((none : Option Bool), ((), none)))), ctrl27), (ClockO.v00, (costCtrl, (NextDimsMachineTN.dimsCtrl, bridgeCtrl)))), (none, ((), none))), installCtrl)),
            (none, (((((((WeightedLevelFields15.initialControl, (((), none), WeightedRowFields.rowInit)), ((), none)), ((none : Option Bool), ((none : Option Bool), ((), none)))), ctrl27), ((MultiMove.initial, (prepInit ((MultiMove.initial, false),
            (MultiMove.initial, ((), (MultiMove.initial, (EntryFamilyLevel.initialControl,
              (MultiMove.initial, ((none : Option Bool), ((), (none : Option Bool))))))))),
          (RawTableTail.startControl EntryRunsRaw.startControl, ((), (none : Option Bool))))), (costCtrl, (NextDimsMachineTN.dimsCtrl, bridgeCtrl)))), (((), none), (none, ((), none)))), installCtrl)))), ext5 (Bk M G n c k) []⟩ := by
  obtain ⟨F0, hK⟩ := G5cKInput.k_input_run
  obtain ⟨N, hL⟩ := G5dLevel0.level0_additive M c
  refine ⟨N, F0 + N + 3, fun {V E} _ _ _ _ G n k p hc hk hfloor hV hE hone hnamed => ?_⟩
  obtain ⟨t, ht, hrun⟩ := hK M G n c k p hc hk hfloor hV hE
    (fun j _ hj => hnamed j hj)
  have hl := hL G n p hc hfloor (hnamed 0 (by omega)) hone
  have hp : 1 ≤ p := by
    have := Nat.clog_pos (by decide : 1 < 2) (by omega : 1 < n + 2)
    omega
  have hab := absorb k p F0 N hp
  exact ⟨t, by omega, hrun⟩

#print axioms absorb
#print axioms k_input_additive

end EthInapproximability.CurrentPaper.G5dKAdditive
