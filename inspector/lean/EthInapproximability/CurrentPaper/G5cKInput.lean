import EthInapproximability.CurrentPaper.G5cAdditiveNamed

/-!
# The shell with `k` as an INPUT field (private lane owner:b-g5-3, segments 2-3)

ONE fixed program `kProgram M c = popFuel ; shellProgram M c ClockO.W0prog ..` (charged handoff via
the admitted `BitMachineRawSequence.program`). `popFuel` is a one-statement machine popping one bit
of the fuel cell. Started with unary `k` (the input field, `k ≥ 1`) in the fuel cell and the branch
packet in `H0`, it halts on the exact level-`k` start bank `ext5 (KShell.Bk M G n c k) []` within
`1 + shell clock + 1`. So the `k - 1` fuel is PRODUCED from the input `k` (audit F3c) and `k` is an
input of the machine (audit F4) rather than computed from `n`.

What remains of F4 (stated exactly): the admitted level-0 round still runs the clock machine `M` on
unary `n` and writes unary `kValue M n` into the master cell `K` (named scratch; it stays in the exit
bank `Bk` through `mSj (mb1 M G n c)`); its cost `WeightedRawWordsKFuel.kBound M n` is part of
`level0BoundP`. It does not influence the number of rounds (that is the input `k`).
Off-promise: for `k = 0` nothing is claimed (the premise `1 ≤ k`).
-/

noncomputable section

namespace EthInapproximability.CurrentPaper.G5cKInput

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

variable [Fintype BStack] [Fintype MatrixTableInterlaceProtectedBridge.Label]

/-- Pop one bit of the fuel cell and halt. -/
def popFuel : Unit → TM2.Stmt (fun _ : H5 => Bool) Unit Unit :=
  fun _ => TM2.Stmt.pop fuel (fun v _ => v) TM2.Stmt.halt

omit [Fintype BStack] [Fintype MatrixTableInterlaceProtectedBridge.Label] in
theorem popFuel_run (X : H4 → List Bool) (k : ℕ) :
    ((advance popFuel)^[1]) (⟨some (), (), ext5 X (List.replicate k true)⟩ :
        TM2.Cfg (fun _ : H5 => Bool) Unit Unit) =
      ⟨none, (), ext5 X (List.replicate (k - 1) true)⟩ := by
  rw [Function.iterate_one]
  simp only [advance, TM2.step, popFuel, TM2.stepAux, Option.getD_some]
  congr 1
  rw [← List.tail_replicate]
  exact upd5 X _ _

#print axioms popFuel_run

/-- ONE fixed program: pop the fuel cell, then the admitted shell. -/
def kProgram (M : BitMachine.Machine) (c : ℕ) :=
  BitMachineRawSequence.program popFuel
    (shellProgram M c ClockO.W0prog ClockO.w00 ClockO.v00 (writerJ progF
              (BitMachineRawSequence.leftLabel (MultiMove.startLabel (jobsA.map CopyFill.toJob)))
              (MultiMove.initial, ((), (MultiMove.initial, (EntryFamilyLevel.initialControl,
                (MultiMove.initial, ((none : Option Bool), ((), (none : Option Bool)))))))))
              (BitMachineRawSequence.leftLabel (MultiMove.startLabel (jobs55.map CopyFill.toJob)))
              (MultiMove.initial, (prepInit ((MultiMove.initial, false),
                (MultiMove.initial, ((), (MultiMove.initial, (EntryFamilyLevel.initialControl,
                  (MultiMove.initial, ((none : Option Bool), ((), (none : Option Bool))))))))),
              (RawTableTail.startControl EntryRunsRaw.startControl, ((), (none : Option Bool))))))
    ((BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel (.inl (.scan 0)))))))))))))
    ()
    ((((((((((((none, ((), ((WeightedRawWords.level0Ctrl, (WeightedRawWords.edgesCtrl, WeightedRawWords.tailCtrl)), WeightedRawWords.kCtrl M))), WeightedVertexWord.vertexCtrl), (WeightedLevelFields15.initialControl, (((), none), WeightedRowFields.rowInit))), ((), none)), ((none : Option Bool), ((none : Option Bool), ((), none)))), ctrl27), (ClockO.v00, (costCtrl, (NextDimsMachineTN.dimsCtrl, bridgeCtrl)))), (none, ((), none))), installCtrl)),
              (none, (((((((WeightedLevelFields15.initialControl, (((), none), WeightedRowFields.rowInit)), ((), none)), ((none : Option Bool), ((none : Option Bool), ((), none)))), ctrl27), ((MultiMove.initial, (prepInit ((MultiMove.initial, false),
            (MultiMove.initial, ((), (MultiMove.initial, (EntryFamilyLevel.initialControl,
              (MultiMove.initial, ((none : Option Bool), ((), (none : Option Bool))))))))),
          (RawTableTail.startControl EntryRunsRaw.startControl, ((), (none : Option Bool))))), (costCtrl, (NextDimsMachineTN.dimsCtrl, bridgeCtrl)))), (((), none), (none, ((), none)))), installCtrl))))

theorem k_input_run :
    ∃ F : ℕ, ∀ (M : BitMachine.Machine) {V E : Type} [Fintype V] [DecidableEq V]
      [Fintype E] [DecidableEq E] (G : EndpointGraph V E) (n c k p : ℕ), 1 ≤ c → 1 ≤ k →
      Nat.clog 2 (n + 2) ≤ p →
      Fintype.card V ≤ 2 ^ p → Fintype.card E ≤ 2 ^ p →
      (∀ j, 1 ≤ j → j < k →
        G5cShellNamed.LevelNamed G c (EffectiveIteration.sourceDepth n) j p) →
    ∃ t ≤ 1 + ((level0BoundP M G n c (ClockO.T22zero G n c) + installBoundP G c (EffectiveIteration.sourceDepth n) 0 + 1) +
        ((k + 1) * 2 ^ (F * p) + 2)) + 1,
      ((advance (kProgram M c))^[t])
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
  obtain ⟨F, h⟩ := G5cAdditiveNamed.shell_run_additive_named
  refine ⟨F, fun M {V E} _ _ _ _ G n c k p hc hk hfloor hV hE hnamed => ?_⟩
  obtain ⟨t, ht, hrun⟩ := h M G n c k p hc hk hfloor hV hE hnamed
  obtain ⟨u, hu, hq⟩ := BitMachineRawSequence.runs popFuel _ () _ () () _ _ _ _ _ 1 t
    (popFuel_run _ k) hrun
  exact ⟨u, by omega, hq⟩

#print axioms k_input_run

end EthInapproximability.CurrentPaper.G5cKInput
