import EthInapproximability.CurrentPaper.Level0CostRound

/-! Lane owner:b-weighted-level-6, unit 2, segment 2b, piece 5: the composed
level-0 round with the cost-word update (see `Level0CostRound` for the cells).

ONE fixed program `roundProgram M c W w₀ v₀` on `H2`: owner-5 `prepProgram M c`
; `W` ; `costOn costEmb` ; owner-5 `bridgeH`, each lifted, three charged
handoffs. Premises: owner-5 `Writer22Spec` (writer 22) and `1 ≤ c`. -/

namespace EthInapproximability.CurrentPaper.Level0CostRun

open Turing BitMachineEncoding BitMachineStackEmbedding
open EthInapproximability.ParameterizedNP.GuardedSourceGraph
open WeightedLevel0Rows WeightedLevel0Persist WeightedLevel0Clean WeightedLevel0Ready
open OuterLevel0Prep OuterLevel0Run OuterLevel0Bridge OuterLevel0Full NextMasterWords
open CostUpdateStages CostUpdateMachine CostUpdateEmbed Level0CostRound

noncomputable section

set_option maxHeartbeats 8000000
set_option maxRecDepth 8192
set_option synthInstance.maxSize 200000
set_option synthInstance.maxHeartbeats 2000000

variable (M : BitMachine.Machine)
variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- ONE fixed level-0 round program (prep ; writer 22 ; cost update ; physical step). -/
def roundProgram (c : ℕ) {LW VW : Type} (W : LW → TM2.Stmt (fun _ : HStack => Bool) LW VW)
    (w₀ : LW) (v₀ : VW) :=
  BitMachineRawSequence.program (lift (prepProgram M c))
    (BitMachineRawSequence.program (lift W)
      (BitMachineRawSequence.program (costOn costEmb) (lift bridgeH)
        MatrixTableInterlaceProtectedBridge.start costCtrl bridgeCtrl)
      (BitMachineRawSequence.leftLabel costStart) v₀ (costCtrl, bridgeCtrl))
    (BitMachineRawSequence.leftLabel w₀)
    ((((((none, ((), ((WeightedRawWords.level0Ctrl, (WeightedRawWords.edgesCtrl, WeightedRawWords.tailCtrl)), WeightedRawWords.kCtrl M))), WeightedVertexWord.vertexCtrl), (WeightedLevelFields15.initialControl, (((), none), WeightedRowFields.rowInit))), ((), none)), ((none : Option Bool), ((none : Option Bool), ((), none)))), ctrl27)
    (v₀, (costCtrl, bridgeCtrl))

/-- The level-`j` raw parameter record of the run from the indexing seed. -/
abbrev rp (G : EndpointGraph V E) (n c j : ℕ) : Parameters.Input :=
  EffectiveIteration.runParameters G c (EffectiveIteration.sourceDepth n)
    (Iteration.seedState (EffectiveIteration.sourceDepth n)) j

/-- The bank handed to the physical step: the prep exit, writer 22 = `d.rawBits`,
master Y = the level-1 cost word. -/
abbrev S2 (G : EndpointGraph V E) (n c : ℕ)
    (F : ETHBinsJoinedScratch.Stack → List Bool)
    (Q : WeightedGraphQJoined.Stack → List Bool) (P : ChosenPrimeRaw.Stack → List Bool) :
    HStack → List Bool :=
  Function.update (S22 M G n c F Q P) (mcell .Y)
    (ETHParameterScaleMachineInput.words (rp G n c (0 + 1)) 2)

theorem mcell_Y_ne (a : WeightedRawWords.Aux) (h : a ≠ .Y) : mcell a ≠ mcell .Y :=
  fun e => h (mcell_inj e)

theorem level0_round (G : EndpointGraph V E) (n c : ℕ) (hc : 1 ≤ c) {LW VW : Type}
    (W : LW → TM2.Stmt (fun _ : HStack => Bool) LW VW) (w₀ : LW) (v₀ : VW) (T22 : ℕ)
    (hW : Writer22Spec M W w₀ v₀ T22 G n c) :
    ∃ F : ETHBinsJoinedScratch.Stack → List Bool,
    ∃ Q : WeightedGraphQJoined.Stack → List Bool,
    ∃ P : ChosenPrimeRaw.Stack → List Bool,
    ∃ t ≤ prepBound M G n c +
        (T22 + (costBound (Parameters.scale (P0 G n c)) (EffectiveIteration.sourceDepth n) c
            (Parameters.bins (P0 G n c)) (Fintype.card E)
            (Iteration.seedState (EffectiveIteration.sourceDepth n)).budget +
          ProtectedFullBankBridgeScratch.actualPhysicalBudget G c
            (EffectiveIteration.sourceDepth n)
            (Iteration.seedState (EffectiveIteration.sourceDepth n)).budget 0
            (Iteration.seedState (EffectiveIteration.sourceDepth n)).matrix + 1) + 1) + 1,
      ∃ z : MatrixTableInterlaceProtectedBridge.Config,
        ((advance (roundProgram M c W w₀ v₀))^[t])
          ⟨some (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel (.inl (.scan 0))))))))),
            (((((((none, ((), ((WeightedRawWords.level0Ctrl, (WeightedRawWords.edgesCtrl, WeightedRawWords.tailCtrl)), WeightedRawWords.kCtrl M))), WeightedVertexWord.vertexCtrl), (WeightedLevelFields15.initialControl, (((), none), WeightedRowFields.rowInit))), ((), none)), ((none : Option Bool), ((none : Option Bool), ((), none)))), ctrl27), (v₀, (costCtrl, bridgeCtrl))),
            ext (H0 (SourceOriginalBranchPackets.packet n (EncodedGraph.encode (EncodedETHSource.serializeGraph G))))⟩ =
          ⟨none, (((((((none, ((), ((WeightedRawWords.level0Ctrl, (WeightedRawWords.edgesCtrl, WeightedRawWords.tailCtrl)), WeightedRawWords.kCtrl M))), WeightedVertexWord.vertexCtrl), (WeightedLevelFields15.initialControl, (((), none), WeightedRowFields.rowInit))), ((), none)), ((none : Option Bool), ((none : Option Bool), ((), none)))), ctrl27), (v₀, (costCtrl, z.var))),
            ext (bank pEmb (S2 M G n c F Q P) z.stk)⟩ ∧
        z.stk (.inr MatrixTableInterlaceOuterJoin.secondOutput) =
          ProtectedFullBankBridgeScratch.actualPhysicalOutput G c (EffectiveIteration.sourceDepth n)
            (Iteration.seedState (EffectiveIteration.sourceDepth n)).budget 0
            (Iteration.seedState (EffectiveIteration.sourceDepth n)).matrix ∧
        level0Facts M G n c F Q P ∧
        bank pEmb (S2 M G n c F Q P) z.stk (mcell .C) =
          ETHParameterScaleMachineInput.words (rp G n c (0 + 1)) 0 ∧
        bank pEmb (S2 M G n c F Q P) z.stk (mcell .B) =
          ETHParameterScaleMachineInput.words (rp G n c (0 + 1)) 1 ∧
        bank pEmb (S2 M G n c F Q P) z.stk (mcell .Y) =
          ETHParameterScaleMachineInput.words (rp G n c (0 + 1)) 2 ∧
        bank pEmb (S2 M G n c F Q P) z.stk (mcell .E) =
          ETHParameterScaleMachineInput.words (rp G n c (0 + 1)) 5 := by
  obtain ⟨F, Q, P, t1, ht1, h1, hf⟩ := level0_prep_run M G n c
  obtain ⟨t2, ht2, v₁, h2⟩ := hW F Q P hf
  obtain ⟨t3, ht3, h3⟩ := cost_embedded costEmb (ext (S22 M G n c F Q P))
    (Parameters.scale (P0 G n c)) (EffectiveIteration.sourceDepth n) c
    (Parameters.bins (P0 G n c)) (Fintype.card E)
    (Iteration.seedState (EffectiveIteration.sourceDepth n)).budget
    (level0_cost_inputs M G n c F Q P hf)
  rw [costEmb_cell5, level0_cost_word G n c hc, ext_update] at h3
  have hS : ∀ x : BStack, x ≠ .inl (.inl (.inl 22)) →
      S2 M G n c F Q P (pEmb x) = exitBank G n c (G4 (level0RowsBank M G n c F Q P)) (pEmb x) := by
    intro x hx
    dsimp only [S2, S22]
    rw [Function.update_of_ne (fun e => mcell_outside .Y ⟨x, e⟩)]
    exact Function.update_of_ne (fun e => hx (pEmb.injective e)) _ _
  have h22 : S2 M G n c F Q P (pEmb (.inl (.inl (.inl 22)))) =
      (ProtectedFullBankBridgeScratch.actualD G c (EffectiveIteration.sourceDepth n)
        (Iteration.seedState (EffectiveIteration.sourceDepth n)).budget 0
        (Iteration.seedState (EffectiveIteration.sourceDepth n)).matrix).rawBits := by
    dsimp only [S2, S22]
    rw [Function.update_of_ne (fun e => mcell_outside .Y ⟨_, e⟩)]
    exact Function.update_self _ _ _
  obtain ⟨t4, ht4, z, h4, hl, hout⟩ :=
    level0_physical_handoff M G n c F Q P hf (S2 M G n c F Q P) hS h22
  rw [hl] at h4
  have h1' := lift_run (prepProgram M c) _ _ _ _ _ _ t1 h1
  have h2' := lift_run W _ _ _ _ _ _ t2 h2
  have h4' := lift_run bridgeH _ _ _ _ _ _ t4 h4
  obtain ⟨u3, hu3, q3⟩ := BitMachineRawSequence.runs (costOn costEmb) (lift bridgeH)
    _ _ _ _ _ _ _ _ _ _ _ h3 h4'
  obtain ⟨u2, hu2, q2⟩ := BitMachineRawSequence.runs (lift W) _
    _ _ _ _ _ _ _ _ _ _ _ h2' q3
  obtain ⟨u1, hu1, q1⟩ := BitMachineRawSequence.runs (lift (prepProgram M c)) _
    _ _ _ _ _ _ _ _ _ _ _ h1' q2
  obtain ⟨hC, hB, hE⟩ := exit_masters M G n c F Q P
    (ProtectedFullBankBridgeScratch.actualD G c (EffectiveIteration.sourceDepth n)
      (Iteration.seedState (EffectiveIteration.sourceDepth n)).budget 0
      (Iteration.seedState (EffectiveIteration.sourceDepth n)).matrix).rawBits
  have hC' : S2 M G n c F Q P (mcell .C) = List.replicate c true := by
    dsimp only [S2]
    rw [Function.update_of_ne (mcell_Y_ne .C (by decide))]
    exact hC
  have hB' : S2 M G n c F Q P (mcell .B) =
      List.replicate (EffectiveIteration.sourceDepth n) true := by
    dsimp only [S2]
    rw [Function.update_of_ne (mcell_Y_ne .B (by decide))]
    exact hB
  have hE' : S2 M G n c F Q P (mcell .E) = List.replicate (Fintype.card E) true := by
    dsimp only [S2]
    rw [Function.update_of_ne (mcell_Y_ne .E (by decide))]
    exact hE
  obtain ⟨mC, mB, mE⟩ := bridge_next_masters G c (EffectiveIteration.sourceDepth n) 0
    (S2 M G n c F Q P) z.stk hC' hB' hE'
  have mY : bank pEmb (S2 M G n c F Q P) z.stk (mcell .Y) =
      ETHParameterScaleMachineInput.words (rp G n c (0 + 1)) 2 := by
    rw [bank_master]
    exact Function.update_self _ _ _
  exact ⟨F, Q, P, u1, by omega, z, q1, hout, hf, mC, mB, mY, mE⟩

#print axioms level0_round

end
end EthInapproximability.CurrentPaper.Level0CostRun
