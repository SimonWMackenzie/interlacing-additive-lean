import EthInapproximability.CurrentPaper.Level0Install
import EthInapproximability.CurrentPaper.FuelLoop

/-! Lane owner:b-weighted-level-9, unit 2, segment 3: the k-round shell on the PHYSICAL run.

Stack `H5 = H4 ⊕ Unit`: the round stack plus one fuel cell. ONE fixed program
`shellProgram M c W₀ w₀₀ v₀₀ W w₀ v₀` = (level-0 round ; install) (`Level0Install.program0`) then
the fuel loop (`FuelLoop.program`) whose body is the physical round step (`StepP.stepProgram`),
both lifted to `H5` (charged handoff). The same `W` (writer 22 at levels `j ≥ 1`, reading cell 55)
serves every level; owner-5's `W₀` serves level 0.

`shell_run`: from the actual branch packet with the fuel cell holding unary `k - 1`, ONE run halts
EXACTLY on the level-`k` start bank of the physical run: installed words of `runParameters k`
(hence unary `y_k + k`, rows and columns of `physRun k`), masters `mSj mb1 k`, and
`rowMajor (physRun k).matrix.entry` in cell 55, fuel cell blank; within
`level0 clock + install clock + 1 + ((k-1) * (T + 1) + 1) + 1` for ONE `T` majorizing every round
step `1 ≤ j < k`. `hb` is discharged by the admitted `IterationComplete.sourceDepth_pos`. -/

namespace EthInapproximability.CurrentPaper.KShell

open Turing BitMachineEncoding BitMachineStackEmbedding
open EthInapproximability.ParameterizedNP.GuardedSourceGraph
open WeightedLevel0Rows WeightedLevel0Persist WeightedLevel0Clean WeightedLevel0Target
open WeightedLevel0Ready WeightedLevel0WriterRun LevelJRows LevelJPersist LevelJClean LevelJReady
open LevelJMasters OuterLevel0Prep OuterLevel0Run LevelJPrep OuterLevel0Bridge LevelJBridge
open OuterLevel0Full NextMasterWords CostUpdateStages CostUpdateMachine CostUpdateEmbed
open Level0CostRound Level0CostRun Level0DimsRound Level0DimsClean RoundP CleanP ExitP StepP
open Level0Install
open LevelJRound (Dmw Dmw_other)
open RoundInstall (installProgram installCtrl)

noncomputable section

set_option maxHeartbeats 3000000
set_option maxRecDepth 8192
set_option synthInstance.maxSize 200000
set_option synthInstance.maxHeartbeats 2000000

abbrev H5 := H4 ⊕ Unit

def i5 : H4 ↪ H5 := ⟨Sum.inl, Sum.inl_injective⟩

def fuel : H5 := .inr ()

def ext5 (X : H4 → List Bool) (u : List Bool) : H5 → List Bool := Sum.elim X (fun _ => u)

def lift5 {L V : Type} (P : L → TM2.Stmt (fun _ : H4 => Bool) L V) :
    L → TM2.Stmt (fun _ : H5 => Bool) L V :=
  fun l => stackStmt i5 (P l)

theorem bank_ext5 (X Y : H4 → List Bool) (u : List Bool) : bank i5 (ext5 X u) Y = ext5 Y u := by
  funext x
  rcases x with x | x
  · exact bank_at i5 (ext5 X u) Y x
  · rw [bank_outside _ _ _ _ (by rintro ⟨k, hk⟩; cases hk)]
    rfl

theorem lift5_run {L V : Type} (P : L → TM2.Stmt (fun _ : H4 => Bool) L V)
    (l l' : Option L) (v v' : V) (X Y : H4 → List Bool) (u : List Bool) (t : ℕ)
    (h : ((advance P)^[t]) (⟨l, v, X⟩ : TM2.Cfg (fun _ : H4 => Bool) L V) = ⟨l', v', Y⟩) :
    ((advance (lift5 P))^[t]) (⟨l, v, ext5 X u⟩ : TM2.Cfg (fun _ : H5 => Bool) L V) =
      ⟨l', v', ext5 Y u⟩ := by
  have r := WeightedRawWords.region_run i5 P ⟨l, v, X⟩ ⟨l', v', Y⟩ t h (ext5 X u) (fun _ => rfl)
  dsimp only at r
  rw [bank_ext5] at r
  exact r

theorem upd5 (X : H4 → List Bool) (u u' : List Bool) :
    Function.update (ext5 X u) fuel u' = ext5 X u' := by
  funext x
  rcases x with x | x
  · rw [Function.update_of_ne (by intro h; cases h)]; rfl
  · rw [show (Sum.inr x : H5) = fuel from rfl, Function.update_self]; rfl

variable (M : BitMachine.Machine)
variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- The level-`j` start bank of the physical run (the shell's loop invariant). -/
def Bk (G : EndpointGraph V E) (n c j : ℕ) : H4 → List Bool :=
  ext4 (H0J (C1j G c (EffectiveIteration.sourceDepth n)
      (yP G c (EffectiveIteration.sourceDepth n) j) j (MP G c (EffectiveIteration.sourceDepth n) j)
      (mSj (mb1 M G n c) G c (EffectiveIteration.sourceDepth n) j)))
    (Dmw (MatrixMaterialization.rowMajor
      (PhysicalLevelRun.physRun G c (EffectiveIteration.sourceDepth n)
        (Iteration.seedState (EffectiveIteration.sourceDepth n)) j).matrix.entry))

section Shell

variable [Fintype BStack]

/-- ONE fixed k-round program (for every `k`). -/
def shellProgram (c : ℕ) {LW₀ VW₀ LW VW : Type}
    (W₀ : LW₀ → TM2.Stmt (fun _ : HStack => Bool) LW₀ VW₀) (w₀₀ : LW₀) (v₀₀ : VW₀)
    (W : LW → TM2.Stmt (fun _ : H4 => Bool) LW VW) (w₀ : LW) (v₀ : VW) :=
  BitMachineRawSequence.program (lift5 (program0 M c W₀ w₀₀ v₀₀))
    (FuelLoop.program (lift5 (stepProgram W w₀ v₀))
      (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan))))))))))))
      (((((((WeightedLevelFields15.initialControl, (((), none), WeightedRowFields.rowInit)), ((), none)), ((none : Option Bool), ((none : Option Bool), ((), none)))), ctrl27), (v₀, (costCtrl, (NextDimsMachineTN.dimsCtrl, bridgeCtrl)))), (((), none), (none, ((), none)))), installCtrl)
      fuel)
    (.inl ())
    ((((((((((none, ((), ((WeightedRawWords.level0Ctrl, (WeightedRawWords.edgesCtrl, WeightedRawWords.tailCtrl)), WeightedRawWords.kCtrl M))), WeightedVertexWord.vertexCtrl), (WeightedLevelFields15.initialControl, (((), none), WeightedRowFields.rowInit))), ((), none)), ((none : Option Bool), ((none : Option Bool), ((), none)))), ctrl27), (v₀₀, (costCtrl, (NextDimsMachineTN.dimsCtrl, bridgeCtrl)))), (none, ((), none))), installCtrl))
    (none, (((((((WeightedLevelFields15.initialControl, (((), none), WeightedRowFields.rowInit)), ((), none)), ((none : Option Bool), ((none : Option Bool), ((), none)))), ctrl27), (v₀, (costCtrl, (NextDimsMachineTN.dimsCtrl, bridgeCtrl)))), (((), none), (none, ((), none)))), installCtrl))

theorem shell_run [Fintype MatrixTableInterlaceProtectedBridge.Label]
    (G : EndpointGraph V E) (n c k : ℕ) (hc : 1 ≤ c) (hk : 1 ≤ k)
    {LW₀ VW₀ LW VW : Type}
    (W₀ : LW₀ → TM2.Stmt (fun _ : HStack => Bool) LW₀ VW₀) (w₀₀ : LW₀) (v₀₀ : VW₀) (T22₀ : ℕ)
    (hW₀ : Writer22Spec M W₀ w₀₀ v₀₀ T22₀ G n c)
    (W : LW → TM2.Stmt (fun _ : H4 => Bool) LW VW) (w₀ : LW) (v₀ : VW) (T22 T : ℕ)
    (hW : ∀ j, 1 ≤ j → j < k →
      Writer22SpecJ W w₀ v₀ T22 G c (EffectiveIteration.sourceDepth n)
        (yP G c (EffectiveIteration.sourceDepth n) j) j (MP G c (EffectiveIteration.sourceDepth n) j)
        (mSj (mb1 M G n c) G c (EffectiveIteration.sourceDepth n) j)
        (MatrixMaterialization.rowMajor
          (PhysicalLevelRun.physRun G c (EffectiveIteration.sourceDepth n)
            (Iteration.seedState (EffectiveIteration.sourceDepth n)) j).matrix.entry))
    (hT : ∀ j, 1 ≤ j → j < k →
      roundBoundP G c (EffectiveIteration.sourceDepth n) j (mb1 M G n c)
          (MatrixMaterialization.rowMajor
            (PhysicalLevelRun.physRun G c (EffectiveIteration.sourceDepth n)
              (Iteration.seedState (EffectiveIteration.sourceDepth n)) j).matrix.entry) T22 +
        installBoundP G c (EffectiveIteration.sourceDepth n) j + 1 ≤ T) :
    ∃ t ≤ (level0BoundP M G n c T22₀ + installBoundP G c (EffectiveIteration.sourceDepth n) 0 + 1) +
        ((k - 1) * (T + 1) + 1) + 1,
      ((advance (shellProgram M c W₀ w₀₀ v₀₀ W w₀ v₀))^[t])
          ⟨some (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel (.inl (.scan 0)))))))))))),
            (((((((((((none, ((), ((WeightedRawWords.level0Ctrl, (WeightedRawWords.edgesCtrl, WeightedRawWords.tailCtrl)), WeightedRawWords.kCtrl M))), WeightedVertexWord.vertexCtrl), (WeightedLevelFields15.initialControl, (((), none), WeightedRowFields.rowInit))), ((), none)), ((none : Option Bool), ((none : Option Bool), ((), none)))), ctrl27), (v₀₀, (costCtrl, (NextDimsMachineTN.dimsCtrl, bridgeCtrl)))), (none, ((), none))), installCtrl)),
              (none, (((((((WeightedLevelFields15.initialControl, (((), none), WeightedRowFields.rowInit)), ((), none)), ((none : Option Bool), ((none : Option Bool), ((), none)))), ctrl27), (v₀, (costCtrl, (NextDimsMachineTN.dimsCtrl, bridgeCtrl)))), (((), none), (none, ((), none)))), installCtrl))),
            ext5 (ext4 (H0 (SourceOriginalBranchPackets.packet n
              (EncodedGraph.encode (EncodedETHSource.serializeGraph G)))) blank57)
              (List.replicate (k - 1) true)⟩ =
        ⟨none,
          (((((((((((none, ((), ((WeightedRawWords.level0Ctrl, (WeightedRawWords.edgesCtrl, WeightedRawWords.tailCtrl)), WeightedRawWords.kCtrl M))), WeightedVertexWord.vertexCtrl), (WeightedLevelFields15.initialControl, (((), none), WeightedRowFields.rowInit))), ((), none)), ((none : Option Bool), ((none : Option Bool), ((), none)))), ctrl27), (v₀₀, (costCtrl, (NextDimsMachineTN.dimsCtrl, bridgeCtrl)))), (none, ((), none))), installCtrl)),
            (none, (((((((WeightedLevelFields15.initialControl, (((), none), WeightedRowFields.rowInit)), ((), none)), ((none : Option Bool), ((none : Option Bool), ((), none)))), ctrl27), (v₀, (costCtrl, (NextDimsMachineTN.dimsCtrl, bridgeCtrl)))), (((), none), (none, ((), none)))), installCtrl))),
          ext5 (Bk M G n c k) []⟩ := by
  have hb := IterationComplete.sourceDepth_pos n
  obtain ⟨t1, ht1, h1⟩ := level0_step M G n c hc W₀ w₀₀ v₀₀ T22₀ hW₀
  have h1' := lift5_run _ _ _ _ _ _ _ (List.replicate (k - 1) true) t1 h1
  let S : ℕ → H5 → List Bool := fun j => ext5 (Bk M G n c (j + 1)) (List.replicate (k - 1 - j) true)
  have hne : ∀ j < k - 1, S j fuel ≠ [] := by
    intro j hj
    show List.replicate (k - 1 - j) true ≠ []
    simp only [ne_eq, List.replicate_eq_nil_iff]
    omega
  have hend : S (k - 1) fuel = [] := by
    show List.replicate (k - 1 - (k - 1)) true = []
    simp
  have hbody : ∀ j < k - 1, ∃ t ≤ T, ((advance (lift5 (stepProgram W w₀ v₀)))^[t])
      ⟨some (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)))))))))))),
        (((((((WeightedLevelFields15.initialControl, (((), none), WeightedRowFields.rowInit)), ((), none)), ((none : Option Bool), ((none : Option Bool), ((), none)))), ctrl27), (v₀, (costCtrl, (NextDimsMachineTN.dimsCtrl, bridgeCtrl)))), (((), none), (none, ((), none)))), installCtrl),
        Function.update (S j) fuel (S j fuel).tail⟩ =
      ⟨none, (((((((WeightedLevelFields15.initialControl, (((), none), WeightedRowFields.rowInit)), ((), none)), ((none : Option Bool), ((none : Option Bool), ((), none)))), ctrl27), (v₀, (costCtrl, (NextDimsMachineTN.dimsCtrl, bridgeCtrl)))), (((), none), (none, ((), none)))), installCtrl),
        S (j + 1)⟩ := by
    intro j hj
    obtain ⟨u, hu, hs⟩ := step_p G c (EffectiveIteration.sourceDepth n) (j + 1) hb hc (mb1 M G n c)
      (base1 M G n c)
      (MatrixMaterialization.rowMajor
        (PhysicalLevelRun.physRun G c (EffectiveIteration.sourceDepth n)
          (Iteration.seedState (EffectiveIteration.sourceDepth n)) (j + 1)).matrix.entry)
      W w₀ v₀ T22 (hW (j + 1) (by omega) (by omega))
    have hs' := lift5_run _ _ _ _ _ _ _ (List.replicate (k - 1 - (j + 1)) true) u hs
    refine ⟨u, le_trans hu (by have := hT (j + 1) (by omega) (by omega); omega), ?_⟩
    have htail : (S j fuel).tail = List.replicate (k - 1 - (j + 1)) true := by
      show (List.replicate (k - 1 - j) true).tail = _
      rw [List.tail_replicate]
      congr 1 <;> omega
    rw [htail, upd5]
    exact hs'
  obtain ⟨t2, ht2, h2⟩ := FuelLoop.loop_run (lift5 (stepProgram W w₀ v₀)) _ _ fuel T (k - 1) S hne hend hbody
  obtain ⟨t, ht, q⟩ := BitMachineRawSequence.runs (lift5 (program0 M c W₀ w₀₀ v₀₀))
    (FuelLoop.program (lift5 (stepProgram W w₀ v₀)) _ _ fuel) _ (.inl ()) _ _ _ _ _ _ _ t1 t2 h1' h2
  have hSk : S (k - 1) = ext5 (Bk M G n c k) [] := by
    show ext5 (Bk M G n c (k - 1 + 1)) (List.replicate (k - 1 - (k - 1)) true) = _
    rw [Nat.sub_add_cancel hk, Nat.sub_self, List.replicate_zero]
  rw [hSk] at q
  exact ⟨t, by omega, q⟩

#print axioms shell_run

end Shell

end
end EthInapproximability.CurrentPaper.KShell
