import EthInapproximability.CurrentPaper.ClockN
import EthInapproximability.CurrentPaper.EntryPrepFamilyFinal

/-! Lane owner:b-weighted-level-11, unit 2, segment 5 (composition with the level-0 writer 22
discharged): `HB2Physical` for ONE fixed machine whose level-0 writer-22 program is lane
entry-program-8's `progF` composite (`EntryPrepFamily.level0_writer22`, frozen private object
`F8Final`, staged as `EntryPrepFamilyFinal` under WAVE13B_B36). `hW₀` is no longer a premise;
its clock `T22₀` is the literal public expression of `level0_writer22`, and the remaining premises
are: the per-level `Writer22SpecJ` (in the exact form `KShell`/`step_p` consume), the entry-clock
polynomial premises on `T22₀` and `T22` (form `(n + |enc G| + 1)^C + 2^(C p)`), and the polynomial
premises on `prepBound`/`prepBoundJ`/`dimsBound`. -/

namespace EthInapproximability.CurrentPaper.ClockO

open Turing BitMachineEncoding BitMachineStackEmbedding
open EthInapproximability.ParameterizedNP.GuardedSourceGraph
open WeightedLevel0Rows WeightedLevel0Persist WeightedLevel0Clean WeightedLevel0Target
open WeightedLevel0Ready WeightedLevel0WriterRun LevelJRows LevelJPersist LevelJClean LevelJReady
open LevelJMasters OuterLevel0Prep OuterLevel0Run LevelJPrep OuterLevel0Bridge LevelJBridge
open OuterLevel0Full NextMasterWords CostUpdateStages CostUpdateMachine CostUpdateEmbed
open Level0CostRound Level0CostRun Level0DimsRound Level0DimsClean RoundP CleanP ExitP StepP
open Level0Install
open FuelShell Emission HB2Machine ClockA ClockB ClockM ClockN

noncomputable section

set_option maxHeartbeats 3000000
set_option synthInstance.maxSize 200000
set_option synthInstance.maxHeartbeats 2000000
set_option maxRecDepth 16384

/-! Finite-control instances missing from three leaf label types of `W0prog` (each a finite
enumeration; derived here, nothing else is assumed). -/
deriving instance Fintype for FamilyRowBody.ClearLabel
deriving instance DecidableEq, Fintype for PrimeWordExact.ClearLabel
deriving instance Fintype for SeedLoop.Lab

/-- Lane entry-program-8's fixed level-0 writer-22 program (literally the program of
`EntryPrepFamily.level0_writer22`), its start label and start control. -/
abbrev W0prog := BitMachineRawSequence.program EntrySeedSpec.seedProgram
  (BitMachineRawSequence.program
    (EntryPrepVec.prepProg4 EntryPrepFamily.progF
      (BitMachineRawSequence.leftLabel (MultiMove.startLabel (EntryPrepFamily.jobsA.map CopyFill.toJob)))
      (MultiMove.initial, ((), (MultiMove.initial, (EntryFamilyLevel.initialControl,
        (MultiMove.initial, ((none : Option Bool), ((), (none : Option Bool)))))))))
    EntryTailClear.tailClear
    (BitMachineRawSequence.leftLabel RawTableTail.startLabel)
    (EntryPrepVec.prepInit ((MultiMove.initial, false),
      (MultiMove.initial, ((), (MultiMove.initial, (EntryFamilyLevel.initialControl,
        (MultiMove.initial, ((none : Option Bool), ((), (none : Option Bool))))))))))
    (RawTableTail.startControl EntryRunsRaw.startControl, ((), (none : Option Bool))))
  (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel
    (BitMachineRawSequence.leftLabel (MultiMove.startLabel (EntryPrepCopy.copyJobs.map CopyFill.toJob)))))
  ((none : Option Bool), (none : Option Bool))
  (EntryPrepVec.prepInit ((MultiMove.initial, false),
      (MultiMove.initial, ((), (MultiMove.initial, (EntryFamilyLevel.initialControl,
        (MultiMove.initial, ((none : Option Bool), ((), (none : Option Bool))))))))),
    (RawTableTail.startControl EntryRunsRaw.startControl, ((), (none : Option Bool))))

/-- The label and control types of a statement family. -/
abbrev labelOf {K L V : Type} {Γ : K → Type} (_ : L → TM2.Stmt Γ L V) : Type := L
abbrev ctrlOf {K L V : Type} {Γ : K → Type} (_ : L → TM2.Stmt Γ L V) : Type := V

abbrev w00 : labelOf W0prog := BitMachineRawSequence.leftLabel SeedTable.startLabel

abbrev v00 : ctrlOf W0prog := (((none : Option Bool), (none : Option Bool)),
  (EntryPrepVec.prepInit ((MultiMove.initial, false),
      (MultiMove.initial, ((), (MultiMove.initial, (EntryFamilyLevel.initialControl,
        (MultiMove.initial, ((none : Option Bool), ((), (none : Option Bool))))))))),
    (RawTableTail.startControl EntryRunsRaw.startControl, ((), (none : Option Bool)))))

/-- The literal clock of `EntryPrepFamily.level0_writer22`. -/
abbrev T22zero {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (G : EndpointGraph V E) (n c : ℕ) : ℕ :=
  SeedTable.bound (IndexSeed.width (EffectiveIteration.sourceDepth n)) +
    (EntryPrepVec.prepBound G n c (EntryPrepVec.labBound G n c (EntryPrepFamily.TF G n c)) +
      (EntryTailClear.tailBound G n c + EntryTailClear.clearBound G n c + 1) + 1) + 1

theorem hW0_discharged (M : BitMachine.Machine) {V E : Type} [Fintype V] [DecidableEq V]
    [Fintype E] [DecidableEq E] (G : EndpointGraph V E) (n c : ℕ) :
    Writer22Spec M W0prog w00 v00 (T22zero G n c) G n c :=
  EntryPrepFamily.level0_writer22 M G n c

/-- **Composition.** `HB2Physical` with the level-0 writer 22 discharged. -/
theorem hb2_physical_entry [Fintype BStack] [Fintype MatrixTableInterlaceProtectedBridge.Label]
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
  refine hb2_physical_components c A d Δ γ hΔ hγ hγone hsource W0prog w00 v00 W w₀ v₀ Cx ex fx C22 ?_
  intro V E iV dV iE dE G n hcommon hlower hupper hrep
  obtain ⟨T22, hW, hT0, hT, hp0, hd0, hj⟩ := hprem G n hcommon hlower hupper hrep
  exact ⟨T22zero G n c, T22, hW0_discharged (CutoffBitMachine.actualMachine c A d) G n c, hW, hT0, hT,
    hp0, hd0, hj⟩

noncomputable example : Fintype (labelOf W0prog) := inferInstance
noncomputable example : Fintype (ctrlOf W0prog) := inferInstance

#print axioms hW0_discharged
#print axioms hb2_physical_entry

end
end EthInapproximability.CurrentPaper.ClockO
