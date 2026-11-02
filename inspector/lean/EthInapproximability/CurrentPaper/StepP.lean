import EthInapproximability.CurrentPaper.ExitP
import EthInapproximability.CurrentPaper.RoundInstall
import EthInapproximability.CurrentPaper.PhysicalLevelRun

/-! Lane owner:b-weighted-level-9, unit 2, segments 2d/3: ONE round step of the PHYSICAL run.

Level state: `yP G c b j = (physRun G c b (seedState b) j).budget`, `MP … = (physRun …).matrix`
(the admitted `PhysicalLevelRun.physRun`, the sequence `HB2Physical` is stated for). The
parameter identity `hP` needed by the generalized round (`RoundP`/`CleanP`) is the admitted
`PhysicalLevelRun.physParameters_eq`.

Masters: `mSj mb G c b j = update mb .Y (unary (yP j + j))` for a base master region `mb`
satisfying `BaseMasters` (`w 7` = unary |V|, every `nat 3 m`, `N` blank, `C, B, E` = unary
`c, b, |E|`, `Gw` = the graph code). The exit masters of round `j` are EXACTLY `mSj mb G c b (j+1)`
(`exit_masters_p`), so the master region evolves deterministically.

`step_p`: ONE fixed program `stepProgram W w₀ v₀` = `CleanP.clean4JProgram W w₀ v₀` (the complete
residue-free level-`j` round) ; `RoundInstall.installProgram` (charged handoff), from the level-`j`
start bank `ext4 (H0J (C1j G c b (yP j) j (MP j) (mSj mb j))) (Dmw mw)` to the level-`(j+1)` start
bank `ext4 (H0J (C1j G c b (yP (j+1)) (j+1) (MP (j+1)) (mSj mb (j+1)))) (Dmw (rowMajor (physRun (j+1)).matrix.entry))`:
the next state's matrix word sits in cell 55 (the matrix-source input of the next writer 22).
The per-level writer-22 behaviour is the named premise `RoundP.Writer22SpecJ` at this level. -/

namespace EthInapproximability.CurrentPaper.StepP

open Turing BitMachineEncoding BitMachineStackEmbedding
open EthInapproximability.ParameterizedNP.GuardedSourceGraph
open WeightedLevel0Rows WeightedLevel0Persist WeightedLevel0Clean WeightedLevel0Target
open WeightedLevel0Ready WeightedLevel0WriterRun LevelJRows LevelJPersist LevelJClean LevelJReady
open LevelJMasters OuterLevel0Prep OuterLevel0Run LevelJPrep OuterLevel0Bridge LevelJBridge
open OuterLevel0Full NextMasterWords CostUpdateStages CostUpdateMachine CostUpdateEmbed
open Level0CostRound Level0CostRun Level0DimsRound Level0DimsClean RoundP CleanP ExitP
open LevelJRound (Dmw Dmw_other)
open RoundInstall (installProgram installCtrl install_run tgt fH W6)

noncomputable section

set_option maxHeartbeats 8000000
set_option maxRecDepth 8192
set_option synthInstance.maxSize 200000
set_option synthInstance.maxHeartbeats 2000000

variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

abbrev yP (G : EndpointGraph V E) (c b j : ℕ) : ℕ :=
  (PhysicalLevelRun.physRun G c b (Iteration.seedState b) j).budget
abbrev MP (G : EndpointGraph V E) (c b j : ℕ) : Iteration.Matrix :=
  (PhysicalLevelRun.physRun G c b (Iteration.seedState b) j).matrix

theorem hPphys (G : EndpointGraph V E) (c b j : ℕ) :
    Pj G c b (yP G c b j) j (MP G c b j) =
      EffectiveIteration.runParameters G c b (Iteration.seedState b) j :=
  PhysicalLevelRun.physParameters_eq G c b (Iteration.seedState b) j

/-- The admitted level-`j` output word at the physical state is the row-major word of the next
physical state. -/
theorem out_phys (G : EndpointGraph V E) (c b j : ℕ) :
    ProtectedFullBankBridgeScratch.actualPhysicalOutput G c b (yP G c b j) j (MP G c b j) =
      MatrixMaterialization.rowMajor
        (PhysicalLevelRun.physRun G c b (Iteration.seedState b) (j + 1)).matrix.entry := by
  rw [WeightedLevelSameConstructor.physical_output_eq]
  rfl

/-- The base master conditions (kept by every round). -/
def BaseMasters (G : EndpointGraph V E) (c b : ℕ) (mb : WeightedRawWords.Aux → List Bool) : Prop :=
  mb (.w 7) = List.replicate (Fintype.card V) true ∧ (∀ m, mb (.nat 3 m) = []) ∧ mb .N = [] ∧
    mb .C = List.replicate c true ∧ mb .B = List.replicate b true ∧
    mb .E = List.replicate (Fintype.card E) true ∧
    mb .Gw = EncodedGraph.encode (EncodedETHSource.serializeGraph G)

/-- The master region at level `j`. -/
def mSj (mb : WeightedRawWords.Aux → List Bool) (G : EndpointGraph V E) (c b j : ℕ) :
    WeightedRawWords.Aux → List Bool :=
  Function.update mb .Y (List.replicate (yP G c b j + j) true)

theorem mSj_ne (mb : WeightedRawWords.Aux → List Bool) (G : EndpointGraph V E) (c b j : ℕ)
    (a : WeightedRawWords.Aux) (h : a ≠ .Y) : mSj mb G c b j a = mb a :=
  Function.update_of_ne h _ _

theorem cost_succ (G : EndpointGraph V E) (c b j : ℕ) :
    ETHParameterScaleMachineInput.words
        (EffectiveIteration.runParameters G c b (Iteration.seedState b) (j + 1)) 2 =
      List.replicate (yP G c b (j + 1) + (j + 1)) true := by
  have h := congrArg Parameters.Input.cost (hPphys G c b (j + 1))
  show List.replicate (EffectiveIteration.runParameters G c b (Iteration.seedState b) (j + 1)).cost true = _
  rw [← h]
  rfl

theorem exit_master_N_p (G : EndpointGraph V E) (c b yb j : ℕ) (Mx : Iteration.Matrix)
    (mS : WeightedRawWords.Aux → List Bool)
    (F : ETHBinsJoinedScratch.Stack → List Bool)
    (Q : WeightedGraphQJoined.Stack → List Bool) (P : ChosenPrimeRaw.Stack → List Bool) :
    Level0CleanRun.blankBridge (S2J G c b yb j Mx mS F Q P) (mcell .N) = [] := by
  rw [exit_master_j G c b yb j Mx mS F Q P .N (by intro h; cases h)]
  exact (RoundExitJ.G4_comb (levelRowsBankJ G c b yb j Mx mS F Q P)
    (mc .N) (by intro h; cases h) (by intro h; cases h)).trans (clean_N _)

/-- The exit masters of round `j` are the level-`(j+1)` masters. -/
theorem exit_masters_p (G : EndpointGraph V E) (c b j : ℕ) (mb : WeightedRawWords.Aux → List Bool)
    (hmb : BaseMasters G c b mb)
    (F : ETHBinsJoinedScratch.Stack → List Bool)
    (Q : WeightedGraphQJoined.Stack → List Bool) (P : ChosenPrimeRaw.Stack → List Bool)
    (hY : Level0CleanRun.blankBridge (S2J G c b (yP G c b j) j (MP G c b j) (mSj mb G c b j) F Q P)
        (mcell .Y) = ETHParameterScaleMachineInput.words
          (EffectiveIteration.runParameters G c b (Iteration.seedState b) (j + 1)) 2) :
    (fun a => Level0CleanRun.blankBridge
        (S2J G c b (yP G c b j) j (MP G c b j) (mSj mb G c b j) F Q P) (mcell a)) =
      mSj mb G c b (j + 1) := by
  obtain ⟨h7, h3, hNb, _, _, _, _⟩ := hmb
  funext a
  by_cases haY : a = WeightedRawWords.Aux.Y
  · subst haY
    rw [hY, cost_succ]
    show _ = Function.update mb WeightedRawWords.Aux.Y _ WeightedRawWords.Aux.Y
    rw [Function.update_self]
  rw [mSj_ne mb G c b (j + 1) a haY]
  by_cases haN : a = WeightedRawWords.Aux.N
  · subst haN
    rw [exit_master_N_p, hNb]
  by_cases ha7 : a = WeightedRawWords.Aux.w 7
  · subst ha7
    rw [exit_master_w7_j, h7]
  by_cases ha3 : ∃ m, a = WeightedRawWords.Aux.nat 3 m
  · obtain ⟨m, rfl⟩ := ha3
    rw [exit_master_nat3_j G c b (yP G c b j) j (MP G c b j) (mSj mb G c b j)
      (fun m => by rw [mSj_ne mb G c b j _ (by intro h; cases h)]; exact h3 m), h3 m]
  · push Not at ha3
    rw [exit_master_other_j G c b (yP G c b j) j (MP G c b j) (mSj mb G c b j) F Q P a haY haN ha7
      (fun m h => ha3 m h), mSj_ne mb G c b j a haY]

#print axioms exit_masters_p

section Step

variable [Fintype BStack]

/-- ONE fixed round step: the complete level round, then the install. -/
def stepProgram {LW VW : Type} (W : LW → TM2.Stmt (fun _ : H4 => Bool) LW VW) (w₀ : LW) (v₀ : VW) :=
  BitMachineRawSequence.program (clean4JProgram W w₀ v₀) installProgram
    (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan) ((((((WeightedLevelFields15.initialControl, (((), none), WeightedRowFields.rowInit)), ((), none)), ((none : Option Bool), ((none : Option Bool), ((), none)))), ctrl27), (v₀, (costCtrl, (NextDimsMachineTN.dimsCtrl, bridgeCtrl)))), (((), none), (none, ((), none)))) installCtrl

/-- The round's clock at the physical state (literally `CleanP.level_dims_clean_j`'s clock). -/
def roundBoundP [Fintype MatrixTableInterlaceProtectedBridge.Label] (G : EndpointGraph V E) (c b j : ℕ) (mb : WeightedRawWords.Aux → List Bool)
    (mw : List Bool) (T22 : ℕ) : ℕ :=
  (prepBoundJ G c b (yP G c b j) j (MP G c b j) (mSj mb G c b j) +
        (T22 + (costBound (Parameters.scale ((Pj G c b (yP G c b j) j (MP G c b j)))) b c
            (Parameters.bins ((Pj G c b (yP G c b j) j (MP G c b j))))
            (Fintype.card E) ((Pj G c b (yP G c b j) j (MP G c b j))).cost +
          (NextDimsMachineTN.dimsBound (dxJ G c b (yP G c b j) j (MP G c b j)) +
            ProtectedFullBankBridgeScratch.actualPhysicalBudget G c b (yP G c b j) j (MP G c b j) + 1)
              + 1) + 1) + 1) +
        ((mw.length + 1 + 2) +
          ((2 * (ProtectedFullBankBridgeScratch.actualPhysicalOutput G c b (yP G c b j) j (MP G c b j)).length + 2) +
            ((∑ i : Fin Level0CleanRun.nB,
                (((ProtectedFullBankBridgeScratch.actualPhysicalStart G c b (yP G c b j) j (MP G c b j)).stk
                    ((Fintype.equivFin BStack).symm i)).length +
                  BitMachineStackGrowth.perStep bridgeH *
                    ProtectedFullBankBridgeScratch.actualPhysicalBudget G c b (yP G c b j) j (MP G c b j)))
              + Level0CleanRun.nB + 2) + 1) + 1) + 1

/-- The install's clock at the next physical state (literally `RoundInstall.install_run`'s). -/
def installBoundP (G : EndpointGraph V E) (c b j : ℕ) : ℕ :=
  2 * (W6 (Pj G c b (yP G c b (j + 1)) (j + 1) (MP G c b (j + 1))) 0).length +
    2 * (W6 (Pj G c b (yP G c b (j + 1)) (j + 1) (MP G c b (j + 1))) 1).length +
    2 * (W6 (Pj G c b (yP G c b (j + 1)) (j + 1) (MP G c b (j + 1))) 2).length +
    2 * (W6 (Pj G c b (yP G c b (j + 1)) (j + 1) (MP G c b (j + 1))) 5).length +
    3 * (W6 (Pj G c b (yP G c b (j + 1)) (j + 1) (MP G c b (j + 1))) 3).length +
    3 * (W6 (Pj G c b (yP G c b (j + 1)) (j + 1) (MP G c b (j + 1))) 4).length +
    2 * (EncodedGraph.encode (EncodedETHSource.serializeGraph G)).length + 30

theorem step_p [Fintype MatrixTableInterlaceProtectedBridge.Label]
    (G : EndpointGraph V E) (c b j : ℕ) (hb : 1 ≤ b) (hc : 1 ≤ c)
    (mb : WeightedRawWords.Aux → List Bool) (hmb : BaseMasters G c b mb) (mw : List Bool)
    {LW VW : Type} (W : LW → TM2.Stmt (fun _ : H4 => Bool) LW VW) (w₀ : LW) (v₀ : VW) (T22 : ℕ)
    (hW : Writer22SpecJ W w₀ v₀ T22 G c b (yP G c b j) j (MP G c b j) (mSj mb G c b j) mw) :
    ∃ t ≤ roundBoundP G c b j mb mw T22 + installBoundP G c b j + 1,
      ((advance (stepProgram W w₀ v₀))^[t])
          ⟨some (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel (BitMachineCopy.Label.scan))))))))))))), (((((((WeightedLevelFields15.initialControl, (((), none), WeightedRowFields.rowInit)), ((), none)), ((none : Option Bool), ((none : Option Bool), ((), none)))), ctrl27), (v₀, (costCtrl, (NextDimsMachineTN.dimsCtrl, bridgeCtrl)))), (((), none), (none, ((), none)))), installCtrl),
            ext4 (H0J (C1j G c b (yP G c b j) j (MP G c b j) (mSj mb G c b j))) (Dmw mw)⟩ =
        ⟨none, (((((((WeightedLevelFields15.initialControl, (((), none), WeightedRowFields.rowInit)), ((), none)), ((none : Option Bool), ((none : Option Bool), ((), none)))), ctrl27), (v₀, (costCtrl, (NextDimsMachineTN.dimsCtrl, bridgeCtrl)))), (((), none), (none, ((), none)))), installCtrl),
          ext4 (H0J (C1j G c b (yP G c b (j + 1)) (j + 1) (MP G c b (j + 1)) (mSj mb G c b (j + 1))))
            (Dmw (MatrixMaterialization.rowMajor
              (PhysicalLevelRun.physRun G c b (Iteration.seedState b) (j + 1)).matrix.entry))⟩ := by
  have hmb' := hmb
  obtain ⟨h7, h3, _, hC, hB, hE, hG⟩ := hmb'
  have hV : mSj mb G c b j (.w 7) = List.replicate (Fintype.card V) true := by
    rw [mSj_ne mb G c b j _ (by intro h; cases h)]; exact h7
  have hN : ∀ m, mSj mb G c b j (.nat 3 m) = [] := fun m => by
    rw [mSj_ne mb G c b j _ (by intro h; cases h)]; exact h3 m
  have hmC : mSj mb G c b j .C = List.replicate c true := by
    rw [mSj_ne mb G c b j _ (by intro h; cases h)]; exact hC
  have hmB : mSj mb G c b j .B = List.replicate b true := by
    rw [mSj_ne mb G c b j _ (by intro h; cases h)]; exact hB
  have hmE : mSj mb G c b j .E = List.replicate (Fintype.card E) true := by
    rw [mSj_ne mb G c b j _ (by intro h; cases h)]; exact hE
  have hmY : mSj mb G c b j .Y = List.replicate (yP G c b j + j) true := Function.update_self _ _ _
  obtain ⟨F, Q, P, t1, ht1, h1, _, mC, mB, mY, mR, mCo, mE⟩ :=
    level_dims_clean_j G c b (yP G c b j) j (MP G c b j) (hPphys G c b j) hb hc (mSj mb G c b j)
      hV hN hmC hmB hmY hmE mw W w₀ v₀ T22 hW
  -- install
  have hP1 := hPphys G c b (j + 1)
  rw [← hP1] at mC mB mY mR mCo mE
  have hGw : Level0CleanRun.blankBridge (S2J G c b (yP G c b j) j (MP G c b j) (mSj mb G c b j) F Q P)
      (mcell .Gw) = EncodedGraph.encode (EncodedETHSource.serializeGraph G) := by
    rw [exit_master_other_j G c b (yP G c b j) j (MP G c b j) (mSj mb G c b j) F Q P .Gw
      (by intro h; cases h) (by intro h; cases h) (by intro h; cases h) (by intro m h; cases h),
      mSj_ne mb G c b j _ (by intro h; cases h)]
    exact hG
  obtain ⟨t2, ht2, h2⟩ := install_run (Pj G c b (yP G c b (j + 1)) (j + 1) (MP G c b (j + 1)))
    (EncodedETHSource.serializeGraph G)
    (Level0CleanRun.blankBridge (S2J G c b (yP G c b j) j (MP G c b j) (mSj mb G c b j) F Q P))
    (DJc G c b (yP G c b j) j (MP G c b j))
    (ProtectedFullBankBridgeScratch.actualPhysicalOutput G c b (yP G c b j) j (MP G c b j))
    (fun x hx => exit_blank_j G c b (yP G c b j) j (MP G c b j) (mSj mb G c b j) F Q P x hx)
    mC mB mY mE hGw mR mCo (fun k h0 h1 => DJc_spare G c b (yP G c b j) j (MP G c b j) k h0 h1)
  have hmast := exit_masters_p G c b j mb hmb F Q P (by rw [mY, hP1])
  rw [hmast] at h2
  rw [← out_phys]
  obtain ⟨t, ht, q⟩ := BitMachineRawSequence.runs (clean4JProgram W w₀ v₀) installProgram
    _ (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan) ((((((WeightedLevelFields15.initialControl, (((), none), WeightedRowFields.rowInit)), ((), none)), ((none : Option Bool), ((none : Option Bool), ((), none)))), ctrl27), (v₀, (costCtrl, (NextDimsMachineTN.dimsCtrl, bridgeCtrl)))), (((), none), (none, ((), none)))) ((((((WeightedLevelFields15.initialControl, (((), none), WeightedRowFields.rowInit)), ((), none)), ((none : Option Bool), ((none : Option Bool), ((), none)))), ctrl27), (v₀, (costCtrl, (NextDimsMachineTN.dimsCtrl, bridgeCtrl)))), (((), none), (none, ((), none)))) installCtrl installCtrl
    _ _ _ t1 t2 h1 h2
  refine ⟨t, ?_, q⟩
  have e1 : t1 ≤ roundBoundP G c b j mb mw T22 := by unfold roundBoundP; exact ht1
  have e2 : t2 ≤ installBoundP G c b j := by unfold installBoundP; exact ht2
  omega

#print axioms step_p

end Step

end
end EthInapproximability.CurrentPaper.StepP
