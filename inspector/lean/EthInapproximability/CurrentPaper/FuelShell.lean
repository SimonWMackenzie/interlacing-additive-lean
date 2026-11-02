import EthInapproximability.CurrentPaper.KShell

/-! Lane owner:b-weighted-level-10, unit 2, segment 3c: the fuel producer and the kept packet.

Stack `H6 = H4 ⊕ Fin 8` (the round stack plus eight private cells; cell `xc 0` is the fuel,
`xc 1` keeps a charged copy of the branch packet, `xc 2` is the copy temporary).

ONE fixed program `fuelShellProgram M c W₀ w₀₀ v₀₀ W w₀ v₀` (the same for every `n`, `G`, `k`):
1. copy the packet (raw-words master `input`) into `xc 1` (charged copy, `2|packet|+2`);
2. owner-9's (level-0 round ; install) `Level0Install.program0`, lifted;
3. copy the level-0 master `K` (unary `kValue M n`, produced by the admitted S5 stage
   `WeightedRawWords.kProgram` inside the frozen level-0 round) into the fuel cell (`2k+2`);
4. pop one fuel mark (one step), leaving unary `k-1`;
5. owner-9's fuel loop (`FuelLoop.program`) of the physical round step (`StepP.stepProgram`).
Four charged handoffs. The start bank is the packet ALONE; the exit bank is EXACT: the level-`k`
start bank of the physical run `KShell.Bk M G n c k` with the packet kept in `xc 1`.
For `M = CutoffBitMachine.actualMachine c A d`, `kValue M n = ETHTailGrowth.repetitions c A d n`
(`kValue_actual`, by `rfl`). -/

namespace EthInapproximability.CurrentPaper.FuelShell

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
open KShell (Bk)

noncomputable section

set_option maxHeartbeats 3000000
set_option maxRecDepth 8192
set_option synthInstance.maxSize 200000
set_option synthInstance.maxHeartbeats 2000000

abbrev H6 := H4 ⊕ Fin 8

def i6 : H4 ↪ H6 := ⟨Sum.inl, Sum.inl_injective⟩

def xc (k : Fin 8) : H6 := .inr k

def blank8 : Fin 8 → List Bool := fun _ => []

def ext6 (X : H4 → List Bool) (D : Fin 8 → List Bool) : H6 → List Bool := Sum.elim X D

def lift6 {L V : Type} (P : L → TM2.Stmt (fun _ : H4 => Bool) L V) :
    L → TM2.Stmt (fun _ : H6 => Bool) L V :=
  fun l => stackStmt i6 (P l)

theorem bank_ext6 (X Y : H4 → List Bool) (D : Fin 8 → List Bool) :
    bank i6 (ext6 X D) Y = ext6 Y D := by
  funext x
  rcases x with x | x
  · exact bank_at i6 (ext6 X D) Y x
  · rw [bank_outside _ _ _ _ (by rintro ⟨k, hk⟩; cases hk)]
    rfl

theorem lift6_run {L V : Type} (P : L → TM2.Stmt (fun _ : H4 => Bool) L V)
    (l l' : Option L) (v v' : V) (X Y : H4 → List Bool) (D : Fin 8 → List Bool) (t : ℕ)
    (h : ((advance P)^[t]) (⟨l, v, X⟩ : TM2.Cfg (fun _ : H4 => Bool) L V) = ⟨l', v', Y⟩) :
    ((advance (lift6 P))^[t]) (⟨l, v, ext6 X D⟩ : TM2.Cfg (fun _ : H6 => Bool) L V) =
      ⟨l', v', ext6 Y D⟩ := by
  have r := WeightedRawWords.region_run i6 P ⟨l, v, X⟩ ⟨l', v', Y⟩ t h (ext6 X D) (fun _ => rfl)
  dsimp only at r
  rw [bank_ext6] at r
  exact r

theorem upd6 (X : H4 → List Bool) (D : Fin 8 → List Bool) (k : Fin 8) (w : List Bool) :
    Function.update (ext6 X D) (xc k) w = ext6 X (Function.update D k w) := by
  funext x
  rcases x with x | x
  · rw [Function.update_of_ne (by intro h; cases h)]; rfl
  · by_cases hx : x = k
    · subst hx
      rw [show (Sum.inr x : H6) = xc x from rfl, Function.update_self]
      show w = Function.update D x w x
      rw [Function.update_self]
    · rw [Function.update_of_ne (by intro h; exact hx (Sum.inr.inj h))]
      show D x = Function.update D k w x
      rw [Function.update_of_ne hx]

/-- The raw-words master cell `a` inside `H6`. -/
def mH6 (a : WeightedRawWords.Aux) : H6 := .inl (RoundInstall.mH a)

theorem mH6_ne_xc (a : WeightedRawWords.Aux) (k : Fin 8) : mH6 a ≠ xc k := by
  intro h; cases h

theorem xc_ne {j k : Fin 8} (h : j ≠ k) : xc j ≠ xc k := fun e => h (Sum.inr.inj e)

/-- A copy `a → b` with the blank temporary `xc 2`. -/
def sl6 (a b : H6) (h1 : a ≠ b) (h2 : a ≠ xc 2) (h3 : b ≠ xc 2) : Fin 3 ↪ H6 where
  toFun
    | 0 => a
    | 1 => b
    | 2 => xc 2
  inj' := by
    intro x y h
    fin_cases x <;> fin_cases y <;> simp_all

def cp6 (a b : H6) (h1 : a ≠ b) (h2 : a ≠ xc 2) (h3 : b ≠ xc 2) :=
  MatrixStage4ScalarPreparationOps.copyProgram (sl6 a b h1 h2 h3)

theorem cp6_run (a b : H6) (h1 : a ≠ b) (h2 : a ≠ xc 2) (h3 : b ≠ xc 2)
    (S : H6 → List Bool) (hb : S b = []) (ht : S (xc 2) = []) :
    ((advance (cp6 a b h1 h2 h3))^[2 * (S a).length + 2])
      (⟨some .scan, none, S⟩ : TM2.Cfg (fun _ : H6 => Bool) BitMachineCopy.Label (Option Bool)) =
      ⟨none, none, Function.update S b (S a)⟩ := by
  have h := MatrixStage4ScalarPreparationOps.copy_run (sl6 a b h1 h2 h3) S ht
  have e0 : (sl6 a b h1 h2 h3) 0 = a := rfl
  have e1 : (sl6 a b h1 h2 h3) 1 = b := rfl
  rw [e0, e1, hb, List.append_nil] at h
  exact h

def cpSave := cp6 (mH6 .input) (xc 1) (mH6_ne_xc _ _) (mH6_ne_xc _ _) (xc_ne (by decide))
def cpK := cp6 (mH6 .K) (xc 0) (mH6_ne_xc _ _) (mH6_ne_xc _ _) (xc_ne (by decide))

/-- One charged pop of the fuel cell. -/
def popP : Unit → TM2.Stmt (fun _ : H6 => Bool) Unit Unit :=
  fun _ => .pop (xc 0) (fun v _ => v) .halt

theorem pop_run (S : H6 → List Bool) :
    ((advance popP)^[1]) (⟨some (), (), S⟩ : TM2.Cfg (fun _ : H6 => Bool) Unit Unit) =
      ⟨none, (), Function.update S (xc 0) (S (xc 0)).tail⟩ := rfl

variable (M : BitMachine.Machine)
variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

theorem kValue_actual (c A d n : ℕ) :
    WeightedRawWords.kValue (CutoffBitMachine.actualMachine c A d) n =
      ETHTailGrowth.repetitions c A d n := rfl

/-- The level-`j` physical start bank keeps the level-0 master `K = unary kValue M n`. -/
theorem Bk_K (G : EndpointGraph V E) (n c j : ℕ) :
    Bk M G n c j (RoundInstall.mH .K) = List.replicate (WeightedRawWords.kValue M n) true := by
  have h1 : Bk M G n c j (RoundInstall.mH .K) =
      mSj (mb1 M G n c) G c (EffectiveIteration.sourceDepth n) j .K :=
    RoundInstall.tgt_master _ _ _ .K
  rw [h1]
  simp only [mSj, mb1, Function.update_apply]
  simp only [reduceCtorEq, if_false]
  exact (WeightedLevel0Masters.masterC_values M G n c).2.2.2.2.2.1

/-- The packet sits in the raw-words master `input` of the level-0 start bank. -/
theorem packet_cell (p : List Bool) : ext4 (H0 p) blank57 (RoundInstall.mH .input) = p := by
  show WeightedRawWords.startBank p (WeightedRawWords.aux .input) = p
  simp [WeightedRawWords.startBank]

section Shell

variable [Fintype BStack]

/-- ONE fixed program (for every `n`, `G`, `k`): save ; level-0 round ; fuel copy ; pop ; loop. -/
def fuelShellProgram (c : ℕ) {LW₀ VW₀ LW VW : Type}
    (W₀ : LW₀ → TM2.Stmt (fun _ : HStack => Bool) LW₀ VW₀) (w₀₀ : LW₀) (v₀₀ : VW₀)
    (W : LW → TM2.Stmt (fun _ : H4 => Bool) LW VW) (w₀ : LW) (v₀ : VW) :=
  BitMachineRawSequence.program cpSave
    (BitMachineRawSequence.program (lift6 (program0 M c W₀ w₀₀ v₀₀))
      (BitMachineRawSequence.program cpK
        (BitMachineRawSequence.program popP
          (FuelLoop.program (lift6 (stepProgram W w₀ v₀)) (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel (BitMachineCopy.Label.scan))))))))))))) (((((((WeightedLevelFields15.initialControl, (((), none), WeightedRowFields.rowInit)), ((), none)), ((none : Option Bool), ((none : Option Bool), ((), none)))), ctrl27), (v₀, (costCtrl, (NextDimsMachineTN.dimsCtrl, bridgeCtrl)))), (((), none), (none, ((), none)))), installCtrl) (xc 0))
          (.inl ()) () (none, (((((((WeightedLevelFields15.initialControl, (((), none), WeightedRowFields.rowInit)), ((), none)), ((none : Option Bool), ((none : Option Bool), ((), none)))), ctrl27), (v₀, (costCtrl, (NextDimsMachineTN.dimsCtrl, bridgeCtrl)))), (((), none), (none, ((), none)))), installCtrl)))
        (BitMachineRawSequence.leftLabel ()) none ((), (none, (((((((WeightedLevelFields15.initialControl, (((), none), WeightedRowFields.rowInit)), ((), none)), ((none : Option Bool), ((none : Option Bool), ((), none)))), ctrl27), (v₀, (costCtrl, (NextDimsMachineTN.dimsCtrl, bridgeCtrl)))), (((), none), (none, ((), none)))), installCtrl))))
      (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan) ((((((((((none, ((), ((WeightedRawWords.level0Ctrl, (WeightedRawWords.edgesCtrl, WeightedRawWords.tailCtrl)), WeightedRawWords.kCtrl M))), WeightedVertexWord.vertexCtrl), (WeightedLevelFields15.initialControl, (((), none), WeightedRowFields.rowInit))), ((), none)), ((none : Option Bool), ((none : Option Bool), ((), none)))), ctrl27), (v₀₀, (costCtrl, (NextDimsMachineTN.dimsCtrl, bridgeCtrl)))), (none, ((), none))), installCtrl))
      (none, ((), (none, (((((((WeightedLevelFields15.initialControl, (((), none), WeightedRowFields.rowInit)), ((), none)), ((none : Option Bool), ((none : Option Bool), ((), none)))), ctrl27), (v₀, (costCtrl, (NextDimsMachineTN.dimsCtrl, bridgeCtrl)))), (((), none), (none, ((), none)))), installCtrl)))))
    (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel ((.inl (.scan 0))))))))))))) none
    (((((((((((none, ((), ((WeightedRawWords.level0Ctrl, (WeightedRawWords.edgesCtrl, WeightedRawWords.tailCtrl)), WeightedRawWords.kCtrl M))), WeightedVertexWord.vertexCtrl), (WeightedLevelFields15.initialControl, (((), none), WeightedRowFields.rowInit))), ((), none)), ((none : Option Bool), ((none : Option Bool), ((), none)))), ctrl27), (v₀₀, (costCtrl, (NextDimsMachineTN.dimsCtrl, bridgeCtrl)))), (none, ((), none))), installCtrl)), (none, ((), (none, (((((((WeightedLevelFields15.initialControl, (((), none), WeightedRowFields.rowInit)), ((), none)), ((none : Option Bool), ((none : Option Bool), ((), none)))), ctrl27), (v₀, (costCtrl, (NextDimsMachineTN.dimsCtrl, bridgeCtrl)))), (((), none), (none, ((), none)))), installCtrl)))))

/-- The produced-fuel shell clock. -/
def fuelShellBound [Fintype MatrixTableInterlaceProtectedBridge.Label]
    (G : EndpointGraph V E) (n c T22₀ T : ℕ) : ℕ :=
  (2 * (SourceOriginalBranchPackets.packet n
      (EncodedGraph.encode (EncodedETHSource.serializeGraph G))).length + 2) +
    ((level0BoundP M G n c T22₀ + installBoundP G c (EffectiveIteration.sourceDepth n) 0 + 1) +
      ((2 * WeightedRawWords.kValue M n + 2) +
        (1 + ((WeightedRawWords.kValue M n - 1) * (T + 1) + 1) + 1) + 1) + 1) + 1

theorem fuel_shell_run [Fintype MatrixTableInterlaceProtectedBridge.Label]
    (G : EndpointGraph V E) (n c : ℕ) (hc : 1 ≤ c) (hk : 1 ≤ WeightedRawWords.kValue M n)
    {LW₀ VW₀ LW VW : Type}
    (W₀ : LW₀ → TM2.Stmt (fun _ : HStack => Bool) LW₀ VW₀) (w₀₀ : LW₀) (v₀₀ : VW₀) (T22₀ : ℕ)
    (hW₀ : Writer22Spec M W₀ w₀₀ v₀₀ T22₀ G n c)
    (W : LW → TM2.Stmt (fun _ : H4 => Bool) LW VW) (w₀ : LW) (v₀ : VW) (T22 T : ℕ)
    (hW : ∀ j, 1 ≤ j → j < WeightedRawWords.kValue M n →
      Writer22SpecJ W w₀ v₀ T22 G c (EffectiveIteration.sourceDepth n)
        (yP G c (EffectiveIteration.sourceDepth n) j) j (MP G c (EffectiveIteration.sourceDepth n) j)
        (mSj (mb1 M G n c) G c (EffectiveIteration.sourceDepth n) j)
        (MatrixMaterialization.rowMajor
          (PhysicalLevelRun.physRun G c (EffectiveIteration.sourceDepth n)
            (Iteration.seedState (EffectiveIteration.sourceDepth n)) j).matrix.entry))
    (hT : ∀ j, 1 ≤ j → j < WeightedRawWords.kValue M n →
      roundBoundP G c (EffectiveIteration.sourceDepth n) j (mb1 M G n c)
          (MatrixMaterialization.rowMajor
            (PhysicalLevelRun.physRun G c (EffectiveIteration.sourceDepth n)
              (Iteration.seedState (EffectiveIteration.sourceDepth n)) j).matrix.entry) T22 +
        installBoundP G c (EffectiveIteration.sourceDepth n) j + 1 ≤ T) :
    ∃ t ≤ fuelShellBound M G n c T22₀ T,
      ((advance (fuelShellProgram M c W₀ w₀₀ v₀₀ W w₀ v₀))^[t])
          ⟨some (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan),
            (none, (((((((((((none, ((), ((WeightedRawWords.level0Ctrl, (WeightedRawWords.edgesCtrl, WeightedRawWords.tailCtrl)), WeightedRawWords.kCtrl M))), WeightedVertexWord.vertexCtrl), (WeightedLevelFields15.initialControl, (((), none), WeightedRowFields.rowInit))), ((), none)), ((none : Option Bool), ((none : Option Bool), ((), none)))), ctrl27), (v₀₀, (costCtrl, (NextDimsMachineTN.dimsCtrl, bridgeCtrl)))), (none, ((), none))), installCtrl)), (none, ((), (none, (((((((WeightedLevelFields15.initialControl, (((), none), WeightedRowFields.rowInit)), ((), none)), ((none : Option Bool), ((none : Option Bool), ((), none)))), ctrl27), (v₀, (costCtrl, (NextDimsMachineTN.dimsCtrl, bridgeCtrl)))), (((), none), (none, ((), none)))), installCtrl)))))),
            ext6 (ext4 (H0 (SourceOriginalBranchPackets.packet n
              (EncodedGraph.encode (EncodedETHSource.serializeGraph G)))) blank57) blank8⟩ =
        ⟨none, (none, (((((((((((none, ((), ((WeightedRawWords.level0Ctrl, (WeightedRawWords.edgesCtrl, WeightedRawWords.tailCtrl)), WeightedRawWords.kCtrl M))), WeightedVertexWord.vertexCtrl), (WeightedLevelFields15.initialControl, (((), none), WeightedRowFields.rowInit))), ((), none)), ((none : Option Bool), ((none : Option Bool), ((), none)))), ctrl27), (v₀₀, (costCtrl, (NextDimsMachineTN.dimsCtrl, bridgeCtrl)))), (none, ((), none))), installCtrl)), (none, ((), (none, (((((((WeightedLevelFields15.initialControl, (((), none), WeightedRowFields.rowInit)), ((), none)), ((none : Option Bool), ((none : Option Bool), ((), none)))), ctrl27), (v₀, (costCtrl, (NextDimsMachineTN.dimsCtrl, bridgeCtrl)))), (((), none), (none, ((), none)))), installCtrl)))))),
          ext6 (Bk M G n c (WeightedRawWords.kValue M n))
            (Function.update blank8 1 (SourceOriginalBranchPackets.packet n
              (EncodedGraph.encode (EncodedETHSource.serializeGraph G))))⟩ := by
  have hb := IterationComplete.sourceDepth_pos n
  set k := WeightedRawWords.kValue M n with hkdef
  set pk := SourceOriginalBranchPackets.packet n
    (EncodedGraph.encode (EncodedETHSource.serializeGraph G)) with hpk
  set Dsv : Fin 8 → List Bool := Function.update blank8 1 pk with hDsv
  -- 1. save the packet
  have s1 := cp6_run (mH6 .input) (xc 1) (mH6_ne_xc _ _) (mH6_ne_xc _ _) (xc_ne (by decide))
    (ext6 (ext4 (H0 pk) blank57) blank8) rfl rfl
  have hsrc : ext6 (ext4 (H0 pk) blank57) blank8 (mH6 .input) = pk := packet_cell pk
  rw [hsrc, upd6] at s1
  -- 2. level-0 round ; install
  obtain ⟨t1, ht1, h1⟩ := level0_step M G n c hc W₀ w₀₀ v₀₀ T22₀ hW₀
  have h1' := lift6_run _ _ _ _ _ _ _ Dsv t1 h1
  -- 3. copy master K into the fuel cell
  have s3 := cp6_run (mH6 .K) (xc 0) (mH6_ne_xc _ _) (mH6_ne_xc _ _) (xc_ne (by decide))
    (ext6 (Bk M G n c 1) Dsv) (by simp [ext6, xc, hDsv, blank8]) (by simp [ext6, xc, hDsv, blank8])
  have hK : ext6 (Bk M G n c 1) Dsv (mH6 .K) = List.replicate k true := Bk_K M G n c 1
  rw [hK, upd6, List.length_replicate] at s3
  -- 4. pop one mark
  have s4 := pop_run (ext6 (Bk M G n c 1) (Function.update Dsv 0 (List.replicate k true)))
  have h0 : ext6 (Bk M G n c 1) (Function.update Dsv 0 (List.replicate k true)) (xc 0) =
      List.replicate k true := by
    show Function.update Dsv 0 (List.replicate k true) 0 = _
    rw [Function.update_self]
  rw [h0, List.tail_replicate, upd6, Function.update_idem] at s4
  -- 5. the fuel loop
  let S : ℕ → H6 → List Bool := fun j =>
    ext6 (Bk M G n c (j + 1)) (Function.update Dsv 0 (List.replicate (k - 1 - j) true))
  have hne : ∀ j < k - 1, S j (xc 0) ≠ [] := by
    intro j hj
    show Function.update Dsv 0 (List.replicate (k - 1 - j) true) 0 ≠ []
    rw [Function.update_self]
    simp only [ne_eq, List.replicate_eq_nil_iff]
    omega
  have hend : S (k - 1) (xc 0) = [] := by
    show Function.update Dsv 0 (List.replicate (k - 1 - (k - 1)) true) 0 = []
    rw [Function.update_self]
    simp
  have hbody : ∀ j < k - 1, ∃ t ≤ T, ((advance (lift6 (stepProgram W w₀ v₀)))^[t])
      ⟨some (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel (BitMachineCopy.Label.scan))))))))))))), (((((((WeightedLevelFields15.initialControl, (((), none), WeightedRowFields.rowInit)), ((), none)), ((none : Option Bool), ((none : Option Bool), ((), none)))), ctrl27), (v₀, (costCtrl, (NextDimsMachineTN.dimsCtrl, bridgeCtrl)))), (((), none), (none, ((), none)))), installCtrl), Function.update (S j) (xc 0) (S j (xc 0)).tail⟩ =
      ⟨none, (((((((WeightedLevelFields15.initialControl, (((), none), WeightedRowFields.rowInit)), ((), none)), ((none : Option Bool), ((none : Option Bool), ((), none)))), ctrl27), (v₀, (costCtrl, (NextDimsMachineTN.dimsCtrl, bridgeCtrl)))), (((), none), (none, ((), none)))), installCtrl), S (j + 1)⟩ := by
    intro j hj
    obtain ⟨u, hu, hs⟩ := step_p G c (EffectiveIteration.sourceDepth n) (j + 1) hb hc (mb1 M G n c)
      (base1 M G n c)
      (MatrixMaterialization.rowMajor
        (PhysicalLevelRun.physRun G c (EffectiveIteration.sourceDepth n)
          (Iteration.seedState (EffectiveIteration.sourceDepth n)) (j + 1)).matrix.entry)
      W w₀ v₀ T22 (hW (j + 1) (by omega) (by omega))
    have hs' := lift6_run _ _ _ _ _ _ _
      (Function.update Dsv 0 (List.replicate (k - 1 - (j + 1)) true)) u hs
    refine ⟨u, le_trans hu (by have := hT (j + 1) (by omega) (by omega); omega), ?_⟩
    have htail : (S j (xc 0)).tail = List.replicate (k - 1 - (j + 1)) true := by
      show (Function.update Dsv 0 (List.replicate (k - 1 - j) true) 0).tail = _
      rw [Function.update_self, List.tail_replicate]
      congr 1
    rw [htail, upd6, Function.update_idem]
    exact hs'
  obtain ⟨t5, ht5, h5⟩ := FuelLoop.loop_run (lift6 (stepProgram W w₀ v₀)) _ _ (xc 0) T (k - 1)
    S hne hend hbody
  -- compose (innermost first)
  obtain ⟨u4, hu4, r4⟩ := BitMachineRawSequence.runs popP
    (FuelLoop.program (lift6 (stepProgram W w₀ v₀)) _ _ (xc 0)) () (.inl ()) _ _ _ _ _ _ _ 1 t5 s4 h5
  obtain ⟨u3, hu3, r3⟩ := BitMachineRawSequence.runs cpK _ _ _ _ _ _ _ _ _ _ _ _ s3 r4
  obtain ⟨u2, hu2, r2⟩ := BitMachineRawSequence.runs (lift6 (program0 M c W₀ w₀₀ v₀₀)) _ _ _ _ _ _ _
    _ _ _ _ _ h1' r3
  obtain ⟨u1, hu1, r1⟩ := BitMachineRawSequence.runs cpSave _ _ _ _ _ _ _ _ _ _ _ _ s1 r2
  have hSk : S (k - 1) = ext6 (Bk M G n c k) (Function.update blank8 1 pk) := by
    show ext6 (Bk M G n c (k - 1 + 1))
      (Function.update Dsv 0 (List.replicate (k - 1 - (k - 1)) true)) = _
    rw [Nat.sub_add_cancel hk, Nat.sub_self, List.replicate_zero]
    congr 1
    rw [hDsv]
    exact Function.update_eq_self_iff.2 (by simp [blank8])
  rw [hSk] at r1
  refine ⟨u1, ?_, r1⟩
  unfold fuelShellBound
  rw [← hkdef, ← hpk]
  omega

#print axioms fuel_shell_run

end Shell

#print axioms Bk_K
#print axioms kValue_actual

end
end EthInapproximability.CurrentPaper.FuelShell
