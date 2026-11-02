import EthInapproximability.CurrentPaper.OuterLevel0Run
import EthInapproximability.CurrentPaper.OuterLevel0Bridge

/-! Lane owner:b-weighted-level-5, unit 2, segment 1 (1c-c-outer), piece E.

ONE fixed level-0 program `level0Program M c W w₀ v₀` = `prepProgram M c` ;
`W` (the writer-22 program, a PARAMETER) ; the embedded admitted physical step
`bridgeH`, with the writer-22 behaviour as the ONE named premise
`Writer22Spec`: from the exact prep exit bank, `W` halts within `T22` steps on
the bank that differs from it ONLY in writer 22, which then holds `d.rawBits`
(lane owner:b-stage4-entry-program-3). Conclusion: from the branch packet, one
run of the composite reaches a halted configuration whose bank is
`bank pEmb S₂₂ z.stk` (the admitted physical step's final bank `z.stk` on the
bridge region, the writer-22 exit bank `S₂₂` elsewhere) and whose second-output
cell is the admitted `actualPhysicalOutput`, within
`prepBound + (T22 + actualPhysicalBudget + 1) + 1`. -/

namespace EthInapproximability.CurrentPaper.OuterLevel0Full

open Turing BitMachineEncoding BitMachineStackEmbedding
open EthInapproximability.ParameterizedNP.GuardedSourceGraph
open WeightedLevel0Rows WeightedLevel0Persist WeightedLevel0Clean WeightedLevel0Ready
open OuterLevel0Prep OuterLevel0Run OuterLevel0Bridge

noncomputable section

set_option maxHeartbeats 8000000
set_option maxRecDepth 8192
set_option synthInstance.maxSize 200000
set_option synthInstance.maxHeartbeats 2000000

variable (M : BitMachine.Machine)
variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- Writer 22 of the bridge stack, as a global cell. -/
def w22 : HStack := pEmb (.inl (.inl (.inl 22)))

/-- The writer-22 interface (THE named premise): from the exact prep exit bank the
fixed program `W` halts within `T22` steps on the SAME bank with writer 22 set to
`d.rawBits` (every other cell, including all of `W`'s scratch, restored). -/
def Writer22Spec {LW VW : Type} (W : LW → TM2.Stmt (fun _ : HStack => Bool) LW VW)
    (w₀ : LW) (v₀ : VW) (T22 : ℕ) (G : EndpointGraph V E) (n c : ℕ) : Prop :=
  ∀ (F : ETHBinsJoinedScratch.Stack → List Bool)
    (Q : WeightedGraphQJoined.Stack → List Bool) (P : ChosenPrimeRaw.Stack → List Bool),
    level0Facts M G n c F Q P →
    ∃ t ≤ T22, ∃ v₁ : VW,
      ((advance W)^[t]) ⟨some w₀, v₀, exitBank G n c (G4 (level0RowsBank M G n c F Q P))⟩ =
        ⟨none, v₁, Function.update (exitBank G n c (G4 (level0RowsBank M G n c F Q P))) w22
          (ProtectedFullBankBridgeScratch.actualD G c (EffectiveIteration.sourceDepth n)
            (Iteration.seedState (EffectiveIteration.sourceDepth n)).budget 0
            (Iteration.seedState (EffectiveIteration.sourceDepth n)).matrix).rawBits⟩

/-- The bridge start control. -/
def bridgeCtrl : MatrixTableInterlaceProtectedBridge.Control :=
  ((MatrixWeightedOrderPreparation.initial, MatrixWeightedOrderWriter.writerInitial),
    (OuterStartBank.outerVar, none))

/-- ONE fixed level-0 program, parameterized by the writer-22 program. -/
def level0Program (c : ℕ) {LW VW : Type} (W : LW → TM2.Stmt (fun _ : HStack => Bool) LW VW)
    (w₀ : LW) (v₀ : VW) :=
  BitMachineRawSequence.program (prepProgram M c)
    (BitMachineRawSequence.program W bridgeH MatrixTableInterlaceProtectedBridge.start v₀ bridgeCtrl)
    (BitMachineRawSequence.leftLabel w₀)
    (((((((none, ((), ((WeightedRawWords.level0Ctrl, (WeightedRawWords.edgesCtrl, WeightedRawWords.tailCtrl)), WeightedRawWords.kCtrl M))), WeightedVertexWord.vertexCtrl), (WeightedLevelFields15.initialControl, (((), none), WeightedRowFields.rowInit))), ((), none)), ((none : Option Bool), ((none : Option Bool), ((), none)))), ctrl27))
    (v₀, bridgeCtrl)

theorem level0_full (G : EndpointGraph V E) (n c : ℕ) {LW VW : Type}
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
        level0Facts M G n c F Q P := by
  obtain ⟨F, Q, P, t1, ht1, h1, hf⟩ := level0_prep_run M G n c
  obtain ⟨t2, ht2, v₁, h2⟩ := hW F Q P hf
  have hS : ∀ x : BStack, x ≠ .inl (.inl (.inl 22)) →
      Function.update (exitBank G n c (G4 (level0RowsBank M G n c F Q P))) w22
        (ProtectedFullBankBridgeScratch.actualD G c (EffectiveIteration.sourceDepth n)
          (Iteration.seedState (EffectiveIteration.sourceDepth n)).budget 0
          (Iteration.seedState (EffectiveIteration.sourceDepth n)).matrix).rawBits (pEmb x) =
        exitBank G n c (G4 (level0RowsBank M G n c F Q P)) (pEmb x) := by
    intro x hx
    exact Function.update_of_ne (fun e => hx (pEmb.injective e)) _ _
  have h22 : Function.update (exitBank G n c (G4 (level0RowsBank M G n c F Q P))) w22
        (ProtectedFullBankBridgeScratch.actualD G c (EffectiveIteration.sourceDepth n)
          (Iteration.seedState (EffectiveIteration.sourceDepth n)).budget 0
          (Iteration.seedState (EffectiveIteration.sourceDepth n)).matrix).rawBits
        (pEmb (.inl (.inl (.inl 22)))) =
      (ProtectedFullBankBridgeScratch.actualD G c (EffectiveIteration.sourceDepth n)
          (Iteration.seedState (EffectiveIteration.sourceDepth n)).budget 0
          (Iteration.seedState (EffectiveIteration.sourceDepth n)).matrix).rawBits :=
    Function.update_self _ _ _
  obtain ⟨t3, ht3, z, h3, hl, hout⟩ := level0_physical_handoff M G n c F Q P hf _ hS h22
  rw [hl] at h3
  obtain ⟨u2, hu2, q2⟩ := BitMachineRawSequence.runs W bridgeH _ _ _ _ _ _ _ _ _ _ _ h2 h3
  obtain ⟨u1, hu1, q1⟩ := BitMachineRawSequence.runs (prepProgram M c) _ _ _ _ _ _ _ _ _ _ _ _ h1 q2
  exact ⟨F, Q, P, u1, by omega, z, q1, hout, hf⟩

#print axioms level0_full

end
end EthInapproximability.CurrentPaper.OuterLevel0Full
