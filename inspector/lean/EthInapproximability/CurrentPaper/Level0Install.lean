import EthInapproximability.CurrentPaper.StepP

/-! Lane owner:b-weighted-level-9, unit 2, segment 2d: the level-0 -> level-1 install.

The level-0 round of owner-8 (`Level0DimsClean.clean4Program M c W w₀ v₀`, from the actual branch
packet, writer-22 premise owner-5 `Writer22Spec` at level 0) followed by the charged install
(`RoundInstall.installProgram`), ONE fixed program `program0 M c W w₀ v₀`, reaches EXACTLY the
level-1 start bank of the PHYSICAL run in the shape of `StepP.step_p`:
`ext4 (H0J (C1j G c b (yP 1) 1 (MP 1) (mSj mb1 G c b 1))) (Dmw (rowMajor (physRun 1).matrix.entry))`
with `b = sourceDepth n` and the base masters `mb1 = update (masterC M G n c) .N []` (owner-3's
level-0 master region with the unary `n` master cleared, as owner-4's clean does).

Transport: owner-3's level-0 phase-1 bank `C1def` equals `C1j` at level 0 with masters `masterC`
(they differ only in the foreign bank on the save region, blank on both sides), hence owner-6's
`S2 M G n c F Q P = S2J G c b y₀ 0 M₀ (masterC M G n c) F Q P`, and the generalized exit lemmas
(`ExitP`) apply at level 0. -/

namespace EthInapproximability.CurrentPaper.Level0Install

open Turing BitMachineEncoding BitMachineStackEmbedding
open EthInapproximability.ParameterizedNP.GuardedSourceGraph
open WeightedLevel0Rows WeightedLevel0Persist WeightedLevel0Clean WeightedLevel0Target
open WeightedLevel0Ready WeightedLevel0WriterRun LevelJRows LevelJPersist LevelJClean LevelJReady
open LevelJMasters OuterLevel0Prep OuterLevel0Run LevelJPrep OuterLevel0Bridge LevelJBridge
open OuterLevel0Full NextMasterWords CostUpdateStages CostUpdateMachine CostUpdateEmbed
open Level0CostRound Level0CostRun Level0DimsRound Level0DimsClean RoundP CleanP ExitP StepP
open LevelJRound (Dmw Dmw_other)
open RoundInstall (installProgram installCtrl install_run tgt fH W6)

noncomputable section

set_option maxHeartbeats 3000000
set_option maxRecDepth 8192
set_option synthInstance.maxSize 200000
set_option synthInstance.maxHeartbeats 2000000

variable (M : BitMachine.Machine)
variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

theorem C1def_eq (G : EndpointGraph V E) (n c : ℕ) :
    C1def M G n c = C1j G c (EffectiveIteration.sourceDepth n)
      (Iteration.seedState (EffectiveIteration.sourceDepth n)).budget 0
      (Iteration.seedState (EffectiveIteration.sourceDepth n)).matrix (masterC M G n c) := by
  funext x
  unfold C1def C1j
  by_cases h : ∃ k, rawEmb k = x
  · obtain ⟨k, rfl⟩ := h
    rw [bank_at, bank_at]
    rfl
  · rw [bank_outside _ _ _ _ h, bank_outside _ _ _ _ h]
    rcases x with x | (j | a)
    · exact absurd ⟨Sum.inl x, rfl⟩ h
    · rfl
    · exact absurd ⟨Sum.inr a, rfl⟩ h

theorem rows_eq (G : EndpointGraph V E) (n c : ℕ)
    (F : ETHBinsJoinedScratch.Stack → List Bool)
    (Q : WeightedGraphQJoined.Stack → List Bool) (P : ChosenPrimeRaw.Stack → List Bool) :
    level0RowsBank M G n c F Q P = levelRowsBankJ G c (EffectiveIteration.sourceDepth n)
      (Iteration.seedState (EffectiveIteration.sourceDepth n)).budget 0
      (Iteration.seedState (EffectiveIteration.sourceDepth n)).matrix (masterC M G n c) F Q P := by
  unfold level0RowsBank levelRowsBankJ C3def C3j C2def C2j
  rw [C1def_eq]
  rfl

theorem S2_eq (G : EndpointGraph V E) (n c : ℕ)
    (F : ETHBinsJoinedScratch.Stack → List Bool)
    (Q : WeightedGraphQJoined.Stack → List Bool) (P : ChosenPrimeRaw.Stack → List Bool) :
    S2 M G n c F Q P = S2J G c (EffectiveIteration.sourceDepth n)
      (Iteration.seedState (EffectiveIteration.sourceDepth n)).budget 0
      (Iteration.seedState (EffectiveIteration.sourceDepth n)).matrix (masterC M G n c) F Q P := by
  dsimp only [S2, S22, S2J, S22J]
  rw [rows_eq]
  rfl

#print axioms S2_eq

/-- The base masters after round 0: owner-3's level-0 masters with `N` cleared. -/
def mb1 (G : EndpointGraph V E) (n c : ℕ) : WeightedRawWords.Aux → List Bool :=
  Function.update (masterC M G n c) WeightedRawWords.Aux.N []

theorem masterC_nat3 (G : EndpointGraph V E) (n c m : ℕ) :
    masterC M G n c (WeightedRawWords.Aux.nat 3 m) = [] := by
  simp [masterC, WeightedVertexWord.masterBankKV, WeightedRawWords.masterBank, Function.update_apply]

theorem masterC_w7 (G : EndpointGraph V E) (n c : ℕ) :
    masterC M G n c (WeightedRawWords.Aux.w 7) = List.replicate (Fintype.card V) true := by
  simp [masterC, WeightedVertexWord.masterBankKV]

theorem base1 (G : EndpointGraph V E) (n c : ℕ) :
    BaseMasters G c (EffectiveIteration.sourceDepth n) (mb1 M G n c) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [mb1, Function.update_of_ne (by intro h; cases h)]; exact masterC_w7 M G n c
  · intro m; rw [mb1, Function.update_of_ne (by intro h; cases h)]; exact masterC_nat3 M G n c m
  · rw [mb1, Function.update_self]
  all_goals
    rw [mb1, Function.update_of_ne (by intro h; cases h)]
    simp [masterC, WeightedVertexWord.masterBankKV, WeightedRawWords.masterBank, Function.update_apply]

/-- The exit masters of round 0 are the level-1 masters of the physical run. -/
theorem exit_masters_0 (G : EndpointGraph V E) (n c : ℕ)
    (F : ETHBinsJoinedScratch.Stack → List Bool)
    (Q : WeightedGraphQJoined.Stack → List Bool) (P : ChosenPrimeRaw.Stack → List Bool)
    (hY : Level0CleanRun.blankBridge (S2 M G n c F Q P) (mcell .Y) =
      ETHParameterScaleMachineInput.words (rp G n c (0 + 1)) 2) :
    (fun a => Level0CleanRun.blankBridge (S2 M G n c F Q P) (mcell a)) =
      mSj (mb1 M G n c) G c (EffectiveIteration.sourceDepth n) 1 := by
  rw [S2_eq] at hY ⊢
  funext a
  by_cases haY : a = WeightedRawWords.Aux.Y
  · subst haY
    rw [hY]
    rw [show ETHParameterScaleMachineInput.words (rp G n c (0 + 1)) 2 =
        List.replicate (yP G c (EffectiveIteration.sourceDepth n) (0 + 1) + (0 + 1)) true from
      cost_succ G c (EffectiveIteration.sourceDepth n) 0]
    show _ = Function.update (mb1 M G n c) WeightedRawWords.Aux.Y _ WeightedRawWords.Aux.Y
    rw [Function.update_self]
  rw [mSj_ne (mb1 M G n c) G c (EffectiveIteration.sourceDepth n) 1 a haY]
  by_cases haN : a = WeightedRawWords.Aux.N
  · subst haN
    rw [exit_master_N_p, mb1, Function.update_self]
  rw [mb1, Function.update_of_ne haN]
  by_cases ha7 : a = WeightedRawWords.Aux.w 7
  · subst ha7
    rw [exit_master_w7_j, masterC_w7]
  by_cases ha3 : ∃ m, a = WeightedRawWords.Aux.nat 3 m
  · obtain ⟨m, rfl⟩ := ha3
    rw [exit_master_nat3_j G c (EffectiveIteration.sourceDepth n)
      (Iteration.seedState (EffectiveIteration.sourceDepth n)).budget 0
      (Iteration.seedState (EffectiveIteration.sourceDepth n)).matrix (masterC M G n c)
      (fun m => masterC_nat3 M G n c m), masterC_nat3]
  · push Not at ha3
    exact exit_master_other_j G c (EffectiveIteration.sourceDepth n)
      (Iteration.seedState (EffectiveIteration.sourceDepth n)).budget 0
      (Iteration.seedState (EffectiveIteration.sourceDepth n)).matrix (masterC M G n c) F Q P a haY haN ha7
      (fun m h => ha3 m h)

#print axioms exit_masters_0

theorem out_phys0 (G : EndpointGraph V E) (n c : ℕ) :
    ProtectedFullBankBridgeScratch.actualPhysicalOutput G c (EffectiveIteration.sourceDepth n)
        (Iteration.seedState (EffectiveIteration.sourceDepth n)).budget 0
        (Iteration.seedState (EffectiveIteration.sourceDepth n)).matrix =
      MatrixMaterialization.rowMajor
        (PhysicalLevelRun.physRun G c (EffectiveIteration.sourceDepth n)
          (Iteration.seedState (EffectiveIteration.sourceDepth n)) 1).matrix.entry :=
  out_phys G c (EffectiveIteration.sourceDepth n) 0

section Step0

variable [Fintype BStack]

/-- ONE fixed program: owner-8's complete level-0 round from the packet, then the install. -/
def program0 (c : ℕ) {LW VW : Type} (W : LW → TM2.Stmt (fun _ : HStack => Bool) LW VW)
    (w₀ : LW) (v₀ : VW) :=
  BitMachineRawSequence.program (clean4Program M c W w₀ v₀) installProgram
    (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)
    ((((((((none, ((), ((WeightedRawWords.level0Ctrl, (WeightedRawWords.edgesCtrl, WeightedRawWords.tailCtrl)), WeightedRawWords.kCtrl M))), WeightedVertexWord.vertexCtrl), (WeightedLevelFields15.initialControl, (((), none), WeightedRowFields.rowInit))), ((), none)), ((none : Option Bool), ((none : Option Bool), ((), none)))), ctrl27), (v₀, (costCtrl, (NextDimsMachineTN.dimsCtrl, bridgeCtrl)))), (none, ((), none)))
    installCtrl

/-- The level-0 round's clock (literally `Level0DimsClean.level0_dims_clean`'s). -/
def level0BoundP [Fintype MatrixTableInterlaceProtectedBridge.Label] (G : EndpointGraph V E)
    (n c T22 : ℕ) : ℕ :=
  (prepBound M G n c +
        (T22 + (costBound (Parameters.scale (P0 G n c)) (EffectiveIteration.sourceDepth n) c
            (Parameters.bins (P0 G n c)) (Fintype.card E)
            (Iteration.seedState (EffectiveIteration.sourceDepth n)).budget +
          (NextDimsMachineTN.dimsBound (dx G n c) +
            ProtectedFullBankBridgeScratch.actualPhysicalBudget G c
              (EffectiveIteration.sourceDepth n)
              (Iteration.seedState (EffectiveIteration.sourceDepth n)).budget 0
              (Iteration.seedState (EffectiveIteration.sourceDepth n)).matrix + 1) + 1) + 1) + 1) +
        ((2 * (ProtectedFullBankBridgeScratch.actualPhysicalOutput G c (EffectiveIteration.sourceDepth n)
            (Iteration.seedState (EffectiveIteration.sourceDepth n)).budget 0
            (Iteration.seedState (EffectiveIteration.sourceDepth n)).matrix).length + 2) +
          ((∑ i : Fin Level0CleanRun.nB,
              (((ProtectedFullBankBridgeScratch.actualPhysicalStart G c (EffectiveIteration.sourceDepth n)
                (Iteration.seedState (EffectiveIteration.sourceDepth n)).budget 0
                (Iteration.seedState (EffectiveIteration.sourceDepth n)).matrix).stk
                  ((Fintype.equivFin BStack).symm i)).length +
                BitMachineStackGrowth.perStep bridgeH *
                  ProtectedFullBankBridgeScratch.actualPhysicalBudget G c (EffectiveIteration.sourceDepth n)
                    (Iteration.seedState (EffectiveIteration.sourceDepth n)).budget 0
                    (Iteration.seedState (EffectiveIteration.sourceDepth n)).matrix)) + Level0CleanRun.nB + 2) + 1) + 1

theorem level0_step [Fintype MatrixTableInterlaceProtectedBridge.Label]
    (G : EndpointGraph V E) (n c : ℕ) (hc : 1 ≤ c) {LW VW : Type}
    (W : LW → TM2.Stmt (fun _ : HStack => Bool) LW VW) (w₀ : LW) (v₀ : VW) (T22 : ℕ)
    (hW : Writer22Spec M W w₀ v₀ T22 G n c) :
    ∃ t ≤ level0BoundP M G n c T22 + installBoundP G c (EffectiveIteration.sourceDepth n) 0 + 1,
      ((advance (program0 M c W w₀ v₀))^[t])
          ⟨some (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel (.inl (.scan 0))))))))))),
            (((((((((none, ((), ((WeightedRawWords.level0Ctrl, (WeightedRawWords.edgesCtrl, WeightedRawWords.tailCtrl)), WeightedRawWords.kCtrl M))), WeightedVertexWord.vertexCtrl), (WeightedLevelFields15.initialControl, (((), none), WeightedRowFields.rowInit))), ((), none)), ((none : Option Bool), ((none : Option Bool), ((), none)))), ctrl27), (v₀, (costCtrl, (NextDimsMachineTN.dimsCtrl, bridgeCtrl)))), (none, ((), none))), installCtrl),
            ext4 (H0 (SourceOriginalBranchPackets.packet n (EncodedGraph.encode (EncodedETHSource.serializeGraph G)))) blank57⟩ =
        ⟨none, (((((((((none, ((), ((WeightedRawWords.level0Ctrl, (WeightedRawWords.edgesCtrl, WeightedRawWords.tailCtrl)), WeightedRawWords.kCtrl M))), WeightedVertexWord.vertexCtrl), (WeightedLevelFields15.initialControl, (((), none), WeightedRowFields.rowInit))), ((), none)), ((none : Option Bool), ((none : Option Bool), ((), none)))), ctrl27), (v₀, (costCtrl, (NextDimsMachineTN.dimsCtrl, bridgeCtrl)))), (none, ((), none))), installCtrl),
          ext4 (H0J (C1j G c (EffectiveIteration.sourceDepth n)
              (yP G c (EffectiveIteration.sourceDepth n) 1) 1 (MP G c (EffectiveIteration.sourceDepth n) 1)
              (mSj (mb1 M G n c) G c (EffectiveIteration.sourceDepth n) 1)))
            (Dmw (MatrixMaterialization.rowMajor
              (PhysicalLevelRun.physRun G c (EffectiveIteration.sourceDepth n)
                (Iteration.seedState (EffectiveIteration.sourceDepth n)) 1).matrix.entry))⟩ := by
  obtain ⟨F, Q, P, t1, ht1, h1, _, mC, mB, mY, mR, mCo, mE⟩ := level0_dims_clean M G n c hc W w₀ v₀ T22 hW
  have hP1 := hPphys G c (EffectiveIteration.sourceDepth n) 1
  have hC' : Level0CleanRun.blankBridge (S2 M G n c F Q P) (mcell .C) =
      W6 (Pj G c (EffectiveIteration.sourceDepth n) (yP G c (EffectiveIteration.sourceDepth n) 1) 1
        (MP G c (EffectiveIteration.sourceDepth n) 1)) 0 := by rw [hP1]; exact mC
  have hB' : Level0CleanRun.blankBridge (S2 M G n c F Q P) (mcell .B) =
      W6 (Pj G c (EffectiveIteration.sourceDepth n) (yP G c (EffectiveIteration.sourceDepth n) 1) 1
        (MP G c (EffectiveIteration.sourceDepth n) 1)) 1 := by rw [hP1]; exact mB
  have hY' : Level0CleanRun.blankBridge (S2 M G n c F Q P) (mcell .Y) =
      W6 (Pj G c (EffectiveIteration.sourceDepth n) (yP G c (EffectiveIteration.sourceDepth n) 1) 1
        (MP G c (EffectiveIteration.sourceDepth n) 1)) 2 := by rw [hP1]; exact mY
  have hE' : Level0CleanRun.blankBridge (S2 M G n c F Q P) (mcell .E) =
      W6 (Pj G c (EffectiveIteration.sourceDepth n) (yP G c (EffectiveIteration.sourceDepth n) 1) 1
        (MP G c (EffectiveIteration.sourceDepth n) 1)) 5 := by rw [hP1]; exact mE
  have hR' : D1 G n c 0 =
      W6 (Pj G c (EffectiveIteration.sourceDepth n) (yP G c (EffectiveIteration.sourceDepth n) 1) 1
        (MP G c (EffectiveIteration.sourceDepth n) 1)) 3 := by rw [hP1]; exact mR
  have hCo' : D1 G n c 1 =
      W6 (Pj G c (EffectiveIteration.sourceDepth n) (yP G c (EffectiveIteration.sourceDepth n) 1) 1
        (MP G c (EffectiveIteration.sourceDepth n) 1)) 4 := by rw [hP1]; exact mCo
  have hGw : Level0CleanRun.blankBridge (S2 M G n c F Q P) (mcell .Gw) =
      EncodedGraph.encode (EncodedETHSource.serializeGraph G) := by
    rw [S2_eq, exit_master_other_j G c (EffectiveIteration.sourceDepth n)
      (Iteration.seedState (EffectiveIteration.sourceDepth n)).budget 0
      (Iteration.seedState (EffectiveIteration.sourceDepth n)).matrix (masterC M G n c) F Q P .Gw
      (by intro h; cases h) (by intro h; cases h) (by intro h; cases h) (by intro m h; cases h)]
    simp [masterC, WeightedVertexWord.masterBankKV, WeightedRawWords.masterBank, Function.update_apply]
  have hS : ∀ x, (∀ a, x ≠ mcell a) → Level0CleanRun.blankBridge (S2 M G n c F Q P) x = [] := by
    intro x hx
    rw [S2_eq]
    exact exit_blank_j G c (EffectiveIteration.sourceDepth n)
      (Iteration.seedState (EffectiveIteration.sourceDepth n)).budget 0
      (Iteration.seedState (EffectiveIteration.sourceDepth n)).matrix (masterC M G n c) F Q P x hx
  obtain ⟨t2, ht2, h2⟩ := install_run
    (Pj G c (EffectiveIteration.sourceDepth n) (yP G c (EffectiveIteration.sourceDepth n) 1) 1
      (MP G c (EffectiveIteration.sourceDepth n) 1))
    (EncodedETHSource.serializeGraph G) (Level0CleanRun.blankBridge (S2 M G n c F Q P)) (D1 G n c)
    (ProtectedFullBankBridgeScratch.actualPhysicalOutput G c (EffectiveIteration.sourceDepth n)
      (Iteration.seedState (EffectiveIteration.sourceDepth n)).budget 0
      (Iteration.seedState (EffectiveIteration.sourceDepth n)).matrix)
    hS hC' hB' hY' hE' hGw hR' hCo' (fun k h0 h1 => D1_spare G n c k h0 h1)
  rw [exit_masters_0 M G n c F Q P mY] at h2
  rw [← out_phys0]
  obtain ⟨t, ht, q⟩ := BitMachineRawSequence.runs (clean4Program M c W w₀ v₀) installProgram
    _ (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan) _ _ installCtrl installCtrl
    _ _ _ t1 t2 h1 h2
  refine ⟨t, ?_, q⟩
  have e1 : t1 ≤ level0BoundP M G n c T22 := by unfold level0BoundP; exact ht1
  have e2 : t2 ≤ installBoundP G c (EffectiveIteration.sourceDepth n) 0 := by
    unfold installBoundP; exact ht2
  omega

#print axioms level0_step

end Step0

end
end EthInapproximability.CurrentPaper.Level0Install
