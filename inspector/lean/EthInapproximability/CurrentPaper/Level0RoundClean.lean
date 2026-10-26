import EthInapproximability.CurrentPaper.Level0CostRun

/-! Lane owner:b-weighted-level-6, unit 2, segment 2e: the level-0 round with
the admitted physical step's residue CLEARED.

Piece 1 (`level0_round_growth`): `Level0CostRun.level0_round` (the same program,
start, clock and exit bank; proof replayed) plus the growth bound of the
bridge-region residue: every cell of the admitted step's final bank `z.stk`
is at most its length in the admitted `actualPhysicalStart` plus
`perStep bridgeH * actualPhysicalBudget` (`BitMachineStackGrowth.run_growth` of
the SAME embedded run; the start identity is owner-5's argument, restated).

Piece 2 (`level0_clean`): ONE fixed program = the round (lifted into
`H3 = H2 ⊕ Fin 2`) ; a charged copy of the admitted output word (cell
`oc secondOutput`) into the fresh cell `outCell` ; a charged clear of the WHOLE
bridge region (every cell `pEmb x`), charged through piece 1. Exit bank EXACT and
free of the residue: `Function.update (ext3 (ext (blankBridge S2))) outCell
(actualPhysicalOutput …)` — the prep/cost exit `S2` with the bridge region blank,
the next-level matrix word in `outCell`, everything else blank.

Instance premises (disclosed): `[Fintype MatrixTableInterlaceProtectedBridge.Label]`
(for `perStep`) and `[Fintype BStack]` (to enumerate the bridge region); both
types are finite; the instances are taken as arguments to avoid a global
instance search (owner-5 Probe5 ran away on instance synthesis for this stack). -/

namespace EthInapproximability.CurrentPaper.Level0RoundClean

open Turing BitMachineEncoding BitMachineStackEmbedding
open EthInapproximability.ParameterizedNP.GuardedSourceGraph
open WeightedLevel0Rows WeightedLevel0Persist WeightedLevel0Clean WeightedLevel0Ready
open OuterLevel0Prep OuterLevel0Run OuterLevel0Bridge OuterLevel0Full NextMasterWords
open CostUpdateStages CostUpdateMachine CostUpdateEmbed Level0CostRound Level0CostRun

noncomputable section

set_option maxHeartbeats 8000000
set_option maxRecDepth 8192
set_option synthInstance.maxSize 200000
set_option synthInstance.maxHeartbeats 2000000

variable (M : BitMachine.Machine)
variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

theorem level0_round_growth [Fintype MatrixTableInterlaceProtectedBridge.Label] (G : EndpointGraph V E) (n c : ℕ) (hc : 1 ≤ c) {LW VW : Type}
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
          ETHParameterScaleMachineInput.words (rp G n c (0 + 1)) 5 ∧
        ∀ x : BStack, (z.stk x).length ≤
          ((ProtectedFullBankBridgeScratch.actualPhysicalStart G c (EffectiveIteration.sourceDepth n)
            (Iteration.seedState (EffectiveIteration.sourceDepth n)).budget 0
            (Iteration.seedState (EffectiveIteration.sourceDepth n)).matrix).stk x).length +
            BitMachineStackGrowth.perStep bridgeH * ProtectedFullBankBridgeScratch.actualPhysicalBudget G c (EffectiveIteration.sourceDepth n)
            (Iteration.seedState (EffectiveIteration.sourceDepth n)).budget 0
            (Iteration.seedState (EffectiveIteration.sourceDepth n)).matrix := by
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
  have hstart : ∀ k : BStack, (ProtectedFullBankBridgeScratch.actualPhysicalStart G c (EffectiveIteration.sourceDepth n)
            (Iteration.seedState (EffectiveIteration.sourceDepth n)).budget 0
            (Iteration.seedState (EffectiveIteration.sourceDepth n)).matrix).stk k = S2 M G n c F Q P (pEmb k) := by
    intro k
    rcases k with w | o
    · rw [OuterStartBank.actualPhysicalStart_writer]
      by_cases hw : w = .inl (.inl 22)
      · subst hw
        rw [WeightedLevel0WriterRun.writer_start_22, h22]
      · rw [hS (.inl w) (by intro e; exact hw (Sum.inl.inj e))]
        exact (ready_writer M G n c F Q P hf w hw).symm
    · rw [OuterStartBank.actualPhysicalStart_outer, hS (.inr o) (by intro e; cases e)]
      rfl
  have hgrow : ∀ x : BStack, (z.stk x).length ≤
      ((ProtectedFullBankBridgeScratch.actualPhysicalStart G c (EffectiveIteration.sourceDepth n)
            (Iteration.seedState (EffectiveIteration.sourceDepth n)).budget 0
            (Iteration.seedState (EffectiveIteration.sourceDepth n)).matrix).stk x).length +
        BitMachineStackGrowth.perStep bridgeH * ProtectedFullBankBridgeScratch.actualPhysicalBudget G c (EffectiveIteration.sourceDepth n)
            (Iteration.seedState (EffectiveIteration.sourceDepth n)).budget 0
            (Iteration.seedState (EffectiveIteration.sourceDepth n)).matrix := by
    intro x
    have hg := BitMachineStackGrowth.run_growth bridgeH
      (⟨some MatrixTableInterlaceProtectedBridge.start,
        ((MatrixWeightedOrderPreparation.initial, MatrixWeightedOrderWriter.writerInitial),
          (OuterStartBank.outerVar, none)), S2 M G n c F Q P⟩ :
        TM2.Cfg (fun _ : HStack => Bool) MatrixTableInterlaceProtectedBridge.Label
          MatrixTableInterlaceProtectedBridge.Control) t4 (pEmb x)
    rw [h4] at hg
    dsimp only at hg
    rw [bank_at, ← hstart x] at hg
    have hm := Nat.mul_le_mul_left (BitMachineStackGrowth.perStep bridgeH) ht4
    omega
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
  exact ⟨F, Q, P, u1, by omega, z, q1, hout, hf, mC, mB, mY, mE, hgrow⟩

#print axioms level0_round_growth

end
end EthInapproximability.CurrentPaper.Level0RoundClean
