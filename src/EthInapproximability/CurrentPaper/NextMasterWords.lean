import EthInapproximability.CurrentPaper.OuterLevel0Full
import EthInapproximability.CurrentPaper.NextCostWords

/-! Lane owner:b-weighted-level-6, unit 2, segment 2a.

Words 0, 1 and 5 of level `j+1` (`c`, `b`, `|E|`, by the frozen
`PhysicalLevelWords.words_succ`) are the master cells `C`, `B`, `E` of the
global stack `HStack` (owner-5 `OuterLevel0Prep`). These cells lie OUTSIDE
the bridge region (the image of `pEmb`), so the embedded admitted physical
step `bridgeH` never touches them: for EVERY bank `S` and EVERY final bridge
bank `T`, `bank pEmb S T` agrees with `S` on them (`bank_master`). At the
level-0 composite exit (`OuterLevel0Full.level0_full`, bank
`bank pEmb (update (exitBank …) w22 d.rawBits) z.stk`) they hold exactly the
level-`(j+1)` words 0, 1, 5 for EVERY `j` (`level0_full_next_masters`).
No new machine; pure bank identities plus a corollary of `level0_full`. -/

namespace EthInapproximability.CurrentPaper.NextMasterWords

open Turing BitMachineEncoding BitMachineStackEmbedding
open EthInapproximability.ParameterizedNP.GuardedSourceGraph
open WeightedLevel0Rows WeightedLevel0Persist WeightedLevel0Clean WeightedLevel0Ready
open OuterLevel0Prep OuterLevel0Bridge OuterLevel0Full

noncomputable section

set_option maxHeartbeats 8000000
set_option maxRecDepth 8192
set_option synthInstance.maxSize 200000
set_option synthInstance.maxHeartbeats 2000000

/-- Every master cell lies outside the bridge region. -/
theorem mcell_outside (a : WeightedRawWords.Aux) : ¬ ∃ x : BStack, pEmb x = mcell a := by
  rintro ⟨x, hx⟩
  rcases x with w | o
  · change (Sum.inl (wEmb w) : HStack) = Sum.inl (Sum.inl (mc a)) at hx
    have h1 : wEmb w = Sum.inl (mc a) := Sum.inl.inj hx
    rcases w with (k | i) | e
    · change (Sum.inl (wc k) : GStack) = Sum.inl (mc a) at h1
      exact wc_ne_mc k a (Sum.inl.inj h1)
    · change (Sum.inr (Sum.inl i) : GStack) = Sum.inl (mc a) at h1
      cases h1
    · change (Sum.inr (Sum.inr e) : GStack) = Sum.inl (mc a) at h1
      cases h1
  · change (Sum.inr (Sum.inl o) : HStack) = Sum.inl (Sum.inl (mc a)) at hx
    cases hx

/-- The admitted physical step (embedded by `pEmb`) leaves every master cell
unchanged: for ANY bank `S` and ANY final bridge bank `T`. -/
theorem bank_master (S : HStack → List Bool) (T : BStack → List Bool)
    (a : WeightedRawWords.Aux) :
    bank pEmb S T (mcell a) = S (mcell a) :=
  bank_outside _ _ _ _ (mcell_outside a)

theorem w22_ne_mcell (a : WeightedRawWords.Aux) : w22 ≠ mcell a :=
  fun h => mcell_outside a ⟨_, h⟩

variable (M : BitMachine.Machine)
variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- Per-level form: whatever bank `S` the round hands to the bridge and
whatever the bridge's final bank `T`, if `S` holds unary `c`, `b`, `|E|` in the
masters `C`, `B`, `E`, then after the bridge these cells hold the level-`(j+1)`
raw words 0, 1, 5, for every `j`. -/
theorem bridge_next_masters (G : EndpointGraph V E) (c b j : ℕ)
    (S : HStack → List Bool) (T : BStack → List Bool)
    (hC : S (mcell .C) = List.replicate c true)
    (hB : S (mcell .B) = List.replicate b true)
    (hE : S (mcell .E) = List.replicate (Fintype.card E) true) :
    bank pEmb S T (mcell .C) =
        ETHParameterScaleMachineInput.words
          (EffectiveIteration.runParameters G c b (Iteration.seedState b) (j + 1)) 0 ∧
    bank pEmb S T (mcell .B) =
        ETHParameterScaleMachineInput.words
          (EffectiveIteration.runParameters G c b (Iteration.seedState b) (j + 1)) 1 ∧
    bank pEmb S T (mcell .E) =
        ETHParameterScaleMachineInput.words
          (EffectiveIteration.runParameters G c b (Iteration.seedState b) (j + 1)) 5 := by
  obtain ⟨w0, w1, _, _, _, w5⟩ := PhysicalLevelWords.words_succ G c b j
  refine ⟨?_, ?_, ?_⟩
  · rw [bank_master, hC, w0]
  · rw [bank_master, hB, w1]
  · rw [bank_master, hE, w5]

/-- At the level-0 composite exit bank the masters `C`, `B`, `E` hold unary
`c`, `b(n)`, `|E|` (owner-4 `ready_master`, `masterC_values`), whatever the
writer-22 word `v` and the final bridge bank `T`. -/
theorem exit_masters (G : EndpointGraph V E) (n c : ℕ)
    (F : ETHBinsJoinedScratch.Stack → List Bool)
    (Q : WeightedGraphQJoined.Stack → List Bool) (P : ChosenPrimeRaw.Stack → List Bool)
    (v : List Bool) :
    Function.update (exitBank G n c (G4 (level0RowsBank M G n c F Q P))) w22 v (mcell .C) =
        List.replicate c true ∧
    Function.update (exitBank G n c (G4 (level0RowsBank M G n c F Q P))) w22 v (mcell .B) =
        List.replicate (EffectiveIteration.sourceDepth n) true ∧
    Function.update (exitBank G n c (G4 (level0RowsBank M G n c F Q P))) w22 v (mcell .E) =
        List.replicate (Fintype.card E) true := by
  have hv := WeightedLevel0Masters.masterC_values M G n c
  refine ⟨?_, ?_, ?_⟩
  · rw [Function.update_of_ne (w22_ne_mcell _).symm]
    change G4 (level0RowsBank M G n c F Q P) (Sum.inl (mc .C)) = _
    rw [WeightedLevel0Masters.ready_master M G n c F Q P .C
      (by intro h; cases h) (by intro h; cases h) (by intro m h; cases h)]
    exact hv.1
  · rw [Function.update_of_ne (w22_ne_mcell _).symm]
    change G4 (level0RowsBank M G n c F Q P) (Sum.inl (mc .B)) = _
    rw [WeightedLevel0Masters.ready_master M G n c F Q P .B
      (by intro h; cases h) (by intro h; cases h) (by intro m h; cases h)]
    exact hv.2.1
  · rw [Function.update_of_ne (w22_ne_mcell _).symm]
    change G4 (level0RowsBank M G n c F Q P) (Sum.inl (mc .E)) = _
    rw [WeightedLevel0Masters.ready_master M G n c F Q P .E
      (by intro h; cases h) (by intro h; cases h) (by intro m h; cases h)]
    exact hv.2.2.2.1

/-- Segment 2a on the ACTUAL level-0 run: the same conclusion as
`OuterLevel0Full.level0_full` (same program, start, clock, exit bank), plus:
in its exit bank the masters `C`, `B`, `E` hold the level-`(j+1)` raw words
0, 1, 5 for every `j` (`b = sourceDepth n`). -/
theorem level0_full_next_masters (G : EndpointGraph V E) (n c : ℕ) {LW VW : Type}
    (W : LW → TM2.Stmt (fun _ : HStack => Bool) LW VW) (w₀ : LW) (v₀ : VW) (T22 : ℕ)
    (hW : Writer22Spec M W w₀ v₀ T22 G n c) :
    ∃ F : ETHBinsJoinedScratch.Stack → List Bool,
    ∃ Q : WeightedGraphQJoined.Stack → List Bool,
    ∃ P : ChosenPrimeRaw.Stack → List Bool,
    ∃ t ≤ prepBound M G n c +
        (T22 + ProtectedFullBankBridgeScratch.actualPhysicalBudget G c
          (EffectiveIteration.sourceDepth n)
          (Iteration.seedState (EffectiveIteration.sourceDepth n)).budget 0
          (Iteration.seedState (EffectiveIteration.sourceDepth n)).matrix + 1) + 1,
      ∃ z : MatrixTableInterlaceProtectedBridge.Config,
        ((advance (level0Program M c W w₀ v₀))^[t])
          ⟨some (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel (.inl (.scan 0))))))))),
            ((((((((none, ((), ((WeightedRawWords.level0Ctrl, (WeightedRawWords.edgesCtrl, WeightedRawWords.tailCtrl)), WeightedRawWords.kCtrl M))), WeightedVertexWord.vertexCtrl), (WeightedLevelFields15.initialControl, (((), none), WeightedRowFields.rowInit))), ((), none)), ((none : Option Bool), ((none : Option Bool), ((), none)))), ctrl27)), (v₀, bridgeCtrl)),
            H0 (SourceOriginalBranchPackets.packet n (EncodedGraph.encode (EncodedETHSource.serializeGraph G)))⟩ =
          ⟨none, ((((((((none, ((), ((WeightedRawWords.level0Ctrl, (WeightedRawWords.edgesCtrl, WeightedRawWords.tailCtrl)), WeightedRawWords.kCtrl M))), WeightedVertexWord.vertexCtrl), (WeightedLevelFields15.initialControl, (((), none), WeightedRowFields.rowInit))), ((), none)), ((none : Option Bool), ((none : Option Bool), ((), none)))), ctrl27)), (v₀, z.var)),
            bank pEmb (Function.update (exitBank G n c (G4 (level0RowsBank M G n c F Q P))) w22
              (ProtectedFullBankBridgeScratch.actualD G c (EffectiveIteration.sourceDepth n)
                (Iteration.seedState (EffectiveIteration.sourceDepth n)).budget 0
                (Iteration.seedState (EffectiveIteration.sourceDepth n)).matrix).rawBits) z.stk⟩ ∧
        z.stk (.inr MatrixTableInterlaceOuterJoin.secondOutput) =
          ProtectedFullBankBridgeScratch.actualPhysicalOutput G c (EffectiveIteration.sourceDepth n)
            (Iteration.seedState (EffectiveIteration.sourceDepth n)).budget 0
            (Iteration.seedState (EffectiveIteration.sourceDepth n)).matrix ∧
        level0Facts M G n c F Q P ∧
        ∀ j : ℕ,
          bank pEmb (Function.update (exitBank G n c (G4 (level0RowsBank M G n c F Q P))) w22
              (ProtectedFullBankBridgeScratch.actualD G c (EffectiveIteration.sourceDepth n)
                (Iteration.seedState (EffectiveIteration.sourceDepth n)).budget 0
                (Iteration.seedState (EffectiveIteration.sourceDepth n)).matrix).rawBits) z.stk
              (mcell .C) =
            ETHParameterScaleMachineInput.words
              (EffectiveIteration.runParameters G c (EffectiveIteration.sourceDepth n)
                (Iteration.seedState (EffectiveIteration.sourceDepth n)) (j + 1)) 0 ∧
          bank pEmb (Function.update (exitBank G n c (G4 (level0RowsBank M G n c F Q P))) w22
              (ProtectedFullBankBridgeScratch.actualD G c (EffectiveIteration.sourceDepth n)
                (Iteration.seedState (EffectiveIteration.sourceDepth n)).budget 0
                (Iteration.seedState (EffectiveIteration.sourceDepth n)).matrix).rawBits) z.stk
              (mcell .B) =
            ETHParameterScaleMachineInput.words
              (EffectiveIteration.runParameters G c (EffectiveIteration.sourceDepth n)
                (Iteration.seedState (EffectiveIteration.sourceDepth n)) (j + 1)) 1 ∧
          bank pEmb (Function.update (exitBank G n c (G4 (level0RowsBank M G n c F Q P))) w22
              (ProtectedFullBankBridgeScratch.actualD G c (EffectiveIteration.sourceDepth n)
                (Iteration.seedState (EffectiveIteration.sourceDepth n)).budget 0
                (Iteration.seedState (EffectiveIteration.sourceDepth n)).matrix).rawBits) z.stk
              (mcell .E) =
            ETHParameterScaleMachineInput.words
              (EffectiveIteration.runParameters G c (EffectiveIteration.sourceDepth n)
                (Iteration.seedState (EffectiveIteration.sourceDepth n)) (j + 1)) 5 := by
  obtain ⟨F, Q, P, t, ht, z, hrun, hout, hf⟩ := level0_full M G n c W w₀ v₀ T22 hW
  refine ⟨F, Q, P, t, ht, z, hrun, hout, hf, fun j => ?_⟩
  obtain ⟨hC, hB, hE⟩ := exit_masters M G n c F Q P
    (ProtectedFullBankBridgeScratch.actualD G c (EffectiveIteration.sourceDepth n)
      (Iteration.seedState (EffectiveIteration.sourceDepth n)).budget 0
      (Iteration.seedState (EffectiveIteration.sourceDepth n)).matrix).rawBits
  exact bridge_next_masters G c (EffectiveIteration.sourceDepth n) j _ z.stk hC hB hE

#print axioms mcell_outside
#print axioms bank_master
#print axioms bridge_next_masters
#print axioms exit_masters
#print axioms level0_full_next_masters

end
end EthInapproximability.CurrentPaper.NextMasterWords
