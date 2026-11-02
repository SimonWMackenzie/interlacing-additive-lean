import EthInapproximability.CurrentPaper.FuelShell

/-! Lane owner:b-weighted-level-10, unit 2, segment 3d (bank level): the emission of the exact
`HB2Physical` output word.

Stack `H7 = H6 ⊕ Fin 16` (FuelShell's stack plus sixteen emission cells `yc i`). The emission
program `emitProgram` is ONE fixed program (independent of `n`, `G`, `k`):
1. parse the kept packet (`xc 1`) with the admitted `BitMachineBankCodec.parser 2` (embedded):
   unary `n` into `yc 0`, the graph code into `yc 9`;
2. copy master `K` (unary `k`) into `yc 1`;
3. copy consumer raw word 3 (unary rows of `physRun k`) into `yc 2`;
4. copy consumer raw word 4 (unary columns) into `yc 3`;
5. copy cell 55 (`rowMajor (physRun k).matrix.entry`) into `yc 4`;
6. copy consumer raw word 2 (unary `y_k + k`) into `yc 5`;
7. copy master `K` into the counter `yc 13`;
8. subtract: pop the counter and `yc 5` together until the counter is empty (`k + 1` steps),
   leaving unary `y_k` in `yc 5` (charged subtraction of the `k` marks);
9. serialize `yc 0 … yc 5` with the admitted `BitMachineBankSerialize.program 6` (embedded) into
   the output cell `yc 8`.
Eight charged handoffs; every copy uses the blank temporary `yc 12`.

`hb2_bank_run`: ONE fixed program (`fuelShellProgram` ; `emitProgram`) from the actual branch
packet ALONE reaches a halting bank whose output cell `yc 8` holds EXACTLY
`BitMachineBankCodec.encode ![unary n, unary k, unary rows, unary cols, rowMajor R_k, unary y_k]`
for `st = physRun G c (sourceDepth n) (seedState (sourceDepth n)) k`, `k = kValue M n` — the
output word of `PhysicalLevelRun.HB2Physical` — with the round region equal to `Bk M G n c k`,
every FuelShell private cell blank, the graph code in `yc 9`, and the emission cells blank except
the serializer's consumed bank `yc 0 … yc 5` (named scratch, existential). -/

namespace EthInapproximability.CurrentPaper.Emission

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
open FuelShell

noncomputable section

set_option maxHeartbeats 3000000
set_option maxRecDepth 8192
set_option synthInstance.maxSize 200000
set_option synthInstance.maxHeartbeats 2000000

abbrev H7 := H6 ⊕ Fin 16

instance decH6 : DecidableEq H6 := inferInstance
instance decH7 : DecidableEq H7 := inferInstance

def i7 : H6 ↪ H7 := ⟨Sum.inl, Sum.inl_injective⟩
def yc (i : Fin 16) : H7 := .inr i
def x7 (y : H6) : H7 := .inl y
def r7 (x : H4) : H7 := .inl (.inl x)
def blank16 : Fin 16 → List Bool := fun _ => []
def ext7 (Y : H6 → List Bool) (D : Fin 16 → List Bool) : H7 → List Bool := Sum.elim Y D

def lift7 {L V : Type} (P : L → TM2.Stmt (fun _ : H6 => Bool) L V) :
    L → TM2.Stmt (fun _ : H7 => Bool) L V :=
  fun l => stackStmt i7 (P l)

theorem bank_ext7 (X Y : H6 → List Bool) (D : Fin 16 → List Bool) :
    bank i7 (ext7 X D) Y = ext7 Y D := by
  funext x
  rcases x with x | x
  · exact bank_at i7 (ext7 X D) Y x
  · rw [bank_outside _ _ _ _ (by rintro ⟨k, hk⟩; cases hk)]
    rfl

theorem lift7_run {L V : Type} (P : L → TM2.Stmt (fun _ : H6 => Bool) L V)
    (l l' : Option L) (v v' : V) (X Y : H6 → List Bool) (D : Fin 16 → List Bool) (t : ℕ)
    (h : ((advance P)^[t]) (⟨l, v, X⟩ : TM2.Cfg (fun _ : H6 => Bool) L V) = ⟨l', v', Y⟩) :
    ((advance (lift7 P))^[t]) (⟨l, v, ext7 X D⟩ : TM2.Cfg (fun _ : H7 => Bool) L V) =
      ⟨l', v', ext7 Y D⟩ := by
  have r := WeightedRawWords.region_run i7 P ⟨l, v, X⟩ ⟨l', v', Y⟩ t h (ext7 X D) (fun _ => rfl)
  dsimp only at r
  rw [bank_ext7] at r
  exact r

/-! ## Copies with the blank temporary `yc 12` -/

def sl7 (a b : H7) (h1 : a ≠ b) (h2 : a ≠ yc 12) (h3 : b ≠ yc 12) : Fin 3 ↪ H7 where
  toFun
    | 0 => a
    | 1 => b
    | 2 => yc 12
  inj' := by
    intro x y h
    fin_cases x <;> fin_cases y <;> simp_all

def cp7 (a b : H7) (h1 : a ≠ b) (h2 : a ≠ yc 12) (h3 : b ≠ yc 12) :=
  MatrixStage4ScalarPreparationOps.copyProgram (sl7 a b h1 h2 h3)

theorem cp7_run (a b : H7) (h1 : a ≠ b) (h2 : a ≠ yc 12) (h3 : b ≠ yc 12)
    (S : H7 → List Bool) (hb : S b = []) (ht : S (yc 12) = []) :
    ((advance (cp7 a b h1 h2 h3))^[2 * (S a).length + 2])
      (⟨some .scan, none, S⟩ : TM2.Cfg (fun _ : H7 => Bool) BitMachineCopy.Label (Option Bool)) =
      ⟨none, none, Function.update S b (S a)⟩ := by
  have h := MatrixStage4ScalarPreparationOps.copy_run (sl7 a b h1 h2 h3) S ht
  have e0 : (sl7 a b h1 h2 h3) 0 = a := rfl
  have e1 : (sl7 a b h1 h2 h3) 1 = b := rfl
  rw [e0, e1, hb, List.append_nil] at h
  exact h

theorem r7_ne_yc (x : H4) (i : Fin 16) : r7 x ≠ yc i := by intro h; cases h
theorem yc_ne {i j : Fin 16} (h : i ≠ j) : yc i ≠ yc j := fun e => h (Sum.inr.inj e)
theorem ycne (i j : Fin 16) (h : i ≠ j := by decide) : yc i ≠ yc j := yc_ne h

def cpK1 := cp7 (r7 (RoundInstall.mH .K)) (yc 1) (r7_ne_yc _ _) (r7_ne_yc _ _) (yc_ne (by decide))
def cpRows := cp7 (r7 (RoundInstall.consH (WeightedRawWords.consRaw 3))) (yc 2) (r7_ne_yc _ _)
  (r7_ne_yc _ _) (yc_ne (by decide))
def cpCols := cp7 (r7 (RoundInstall.consH (WeightedRawWords.consRaw 4))) (yc 3) (r7_ne_yc _ _)
  (r7_ne_yc _ _) (yc_ne (by decide))
def cpMat := cp7 (r7 (RoundInstall.fH 55)) (yc 4) (r7_ne_yc _ _) (r7_ne_yc _ _) (yc_ne (by decide))
def cpCost := cp7 (r7 (RoundInstall.consH (WeightedRawWords.consRaw 2))) (yc 5) (r7_ne_yc _ _)
  (r7_ne_yc _ _) (yc_ne (by decide))
def cpK13 := cp7 (r7 (RoundInstall.mH .K)) (yc 13) (r7_ne_yc _ _) (r7_ne_yc _ _) (yc_ne (by decide))

/-! ## The embedded packet parser -/

def pMap : BitMachineBankCodec.Stack 2 → H7 :=
  Sum.elim ![yc 0, yc 9] ![x7 (xc 1), yc 10, yc 11]

def pE : BitMachineBankCodec.Stack 2 ↪ H7 where
  toFun := pMap
  inj' := by
    intro x y h
    rcases x with x | x <;> rcases y with y | y <;> fin_cases x <;> fin_cases y <;>
      simp_all [pMap, yc, x7, xc]

theorem bank_pE (G : H7 → List Bool) (C : BitMachineBankCodec.Stack 2 → List Bool) (y : H7) :
    bank pE G C y =
      if y = yc 0 then C (.inl 0) else if y = yc 9 then C (.inl 1) else
      if y = x7 (xc 1) then C (.inr 0) else if y = yc 10 then C (.inr 1) else
      if y = yc 11 then C (.inr 2) else G y := by
  by_cases h0 : y = yc 0
  · subst h0; exact bank_at pE G C (.inl 0)
  by_cases h9 : y = yc 9
  · subst h9; rw [if_neg (by decide)]; exact bank_at pE G C (.inl 1)
  by_cases h1 : y = x7 (xc 1)
  · subst h1; rw [if_neg (by intro h; cases h), if_neg (by intro h; cases h)]
    exact bank_at pE G C (.inr 0)
  by_cases h10 : y = yc 10
  · subst h10; rw [if_neg (by decide), if_neg (by decide), if_neg (by intro h; cases h)]
    exact bank_at pE G C (.inr 1)
  by_cases h11 : y = yc 11
  · subst h11
    rw [if_neg (by decide), if_neg (by decide), if_neg (by intro h; cases h), if_neg (by decide)]
    exact bank_at pE G C (.inr 2)
  rw [if_neg h0, if_neg h9, if_neg h1, if_neg h10, if_neg h11]
  apply bank_outside
  rintro ⟨k, hk⟩
  rcases k with k | k <;> fin_cases k
  · exact h0 hk.symm
  · exact h9 hk.symm
  · exact h1 hk.symm
  · exact h10 hk.symm
  · exact h11 hk.symm

def parseP : BitMachineBankCodec.ParserLabel 2 →
    TM2.Stmt (fun _ : H7 => Bool) (BitMachineBankCodec.ParserLabel 2) BitMachineBankCodec.Control :=
  fun l => stackStmt pE (BitMachineBankCodec.parser 2 l)

theorem parse_run (Y : H7 → List Bool) (n : ℕ) (w : List Bool)
    (hsrc : Y (x7 (xc 1)) = SourceOriginalBranchPackets.packet n w)
    (h0 : Y (yc 0) = []) (h9 : Y (yc 9) = []) (h10 : Y (yc 10) = []) (h11 : Y (yc 11) = []) :
    ∃ t ≤ 5 * ((SourceOriginalBranchPackets.packet n w).length + 1),
      ((advance parseP)^[t]) (⟨some (.scan 0), none, Y⟩ :
        TM2.Cfg (fun _ : H7 => Bool) (BitMachineBankCodec.ParserLabel 2) BitMachineBankCodec.Control) =
        ⟨none, some true, bank pE Y (BitMachineBankCodec.contents
          (SourceOriginalBranchPackets.bank n w) [] [] [])⟩ := by
  obtain ⟨t, ht, hp⟩ := BitMachineBankCodec.parser_correct 2 (SourceOriginalBranchPackets.packet n w) []
  rw [SourceOriginalBranchPackets.packet_decode] at hp
  have hp' : ((advance (BitMachineBankCodec.parser 2))^[t])
      (BitMachineBankCodec.parserCfg (some (.scan 0)) none (fun _ => [])
        (SourceOriginalBranchPackets.packet n w) [] []) =
      BitMachineBankCodec.parserCfg none (some true) (SourceOriginalBranchPackets.bank n w) [] [] [] := hp
  have hG : ∀ k, (BitMachineBankCodec.parserCfg (some (.scan 0)) none (fun _ => [])
      (SourceOriginalBranchPackets.packet n w) [] [] : TM2.Cfg (fun _ : BitMachineBankCodec.Stack 2 => Bool)
        (BitMachineBankCodec.ParserLabel 2) BitMachineBankCodec.Control).stk k = Y (pE k) := by
    intro k
    rcases k with k | k <;> fin_cases k
    · exact h0.symm
    · exact h9.symm
    · exact hsrc.symm
    · exact h10.symm
    · exact h11.symm
  have r := WeightedRawWords.region_run pE (BitMachineBankCodec.parser 2) _ _ t hp' Y hG
  exact ⟨t, by simpa using ht, r⟩

/-! ## The embedded serializer -/

def sMap : BitMachineBankSerialize.Stack 6 → H7 :=
  Sum.elim ![yc 0, yc 1, yc 2, yc 3, yc 4, yc 5] ![yc 6, yc 7, yc 8]

def sE : BitMachineBankSerialize.Stack 6 ↪ H7 where
  toFun := sMap
  inj' := by
    intro x y h
    rcases x with x | x <;> rcases y with y | y <;> fin_cases x <;> fin_cases y <;>
      simp_all [sMap, yc]

theorem sE_inr (i : Fin 3) : sE (.inr i) = yc (⟨i.val + 6, by omega⟩) := by
  fin_cases i <;> rfl

theorem sE_inl (i : Fin 6) : sE (.inl i) = yc (⟨i.val, by omega⟩) := by
  fin_cases i <;> rfl

theorem bank_sE_out (G : H7 → List Bool) (C : BitMachineBankSerialize.Stack 6 → List Bool) (y : H7)
    (hy : ∀ i : Fin 16, i.val < 9 → y ≠ yc i) : bank sE G C y = G y := by
  apply bank_outside
  rintro ⟨k, hk⟩
  rcases k with k | k
  · rw [sE_inl] at hk; exact hy _ (by simp; omega) hk.symm
  · rw [sE_inr] at hk; exact hy _ (by simp; omega) hk.symm

def serP : BitMachineBankSerialize.Label 6 →
    TM2.Stmt (fun _ : H7 => Bool) (BitMachineBankSerialize.Label 6) (Option Bool) :=
  fun l => stackStmt sE (BitMachineBankSerialize.program 6 l)

theorem ser_run (Y : H7 → List Bool)
    (h6 : Y (yc 6) = []) (h7 : Y (yc 7) = []) (h8 : Y (yc 8) = []) :
    ∃ t ≤ 2 * (BitMachineBankSerialize.encode
        (List.ofFn (fun i : Fin 6 => Y (sE (.inl i))))).length + 2,
      ∃ S' : Fin 6 → List Bool,
      ((advance serP)^[t]) (⟨some (.emit 0), none, Y⟩ :
        TM2.Cfg (fun _ : H7 => Bool) (BitMachineBankSerialize.Label 6) (Option Bool)) =
        ⟨none, none, bank sE Y (BitMachineBankSerialize.contents S' [] []
          (BitMachineBankSerialize.encode (List.ofFn (fun i : Fin 6 => Y (sE (.inl i))))))⟩ := by
  obtain ⟨t, S', ht, hs⟩ := BitMachineBankSerialize.serialize (fun i : Fin 6 => Y (sE (.inl i))) [] []
  rw [List.append_nil] at hs
  have hG : ∀ k, (BitMachineBankSerialize.cfg (some (.emit 0)) none
      (fun i : Fin 6 => Y (sE (.inl i))) [] [] [] : TM2.Cfg (fun _ : BitMachineBankSerialize.Stack 6 => Bool)
        (BitMachineBankSerialize.Label 6) (Option Bool)).stk k = Y (sE k) := by
    intro k
    rcases k with k | k
    · rfl
    · fin_cases k
      · exact h6.symm
      · exact h7.symm
      · exact h8.symm
  have r := WeightedRawWords.region_run sE (BitMachineBankSerialize.program 6) _ _ t hs Y hG
  exact ⟨t, ht, S', r⟩

/-! ## Charged subtraction of the `k` marks -/

def subP : Unit → TM2.Stmt (fun _ : H7 => Bool) Unit (Option Bool) :=
  fun _ => .pop (yc 13) (fun _ b => b)
    (.branch Option.isSome (.pop (yc 5) (fun v _ => v) (.goto (fun _ => ()))) .halt)

theorem sub_run : ∀ (m : ℕ) (Y : H7 → List Bool) (R : List Bool) (v : Option Bool),
    Y (yc 13) = List.replicate m true → Y (yc 5) = List.replicate m true ++ R →
    ((advance subP)^[m + 1]) (⟨some (), v, Y⟩ : TM2.Cfg (fun _ : H7 => Bool) Unit (Option Bool)) =
      ⟨none, none, Function.update (Function.update Y (yc 13) []) (yc 5) R⟩ := by
  intro m
  induction m with
  | zero =>
    intro Y R v h13 h5
    simp only [List.replicate_zero, List.nil_append] at h13 h5
    simp only [Nat.zero_add, Function.iterate_one]
    simp only [advance, TM2.step, subP, TM2.stepAux, h13, List.head?_nil, List.tail_nil,
      Option.isSome_none, cond_false, Option.getD_some]
    congr 1
    funext y
    simp only [Function.update_apply]
    split_ifs <;> simp_all [yc]
  | succ m ih =>
    intro Y R v h13 h5
    rw [Function.iterate_succ_apply]
    have hstep : advance subP (⟨some (), v, Y⟩ : TM2.Cfg (fun _ : H7 => Bool) Unit (Option Bool)) =
        ⟨some (), some true, Function.update (Function.update Y (yc 13) (List.replicate m true)) (yc 5)
          (List.replicate m true ++ R)⟩ := by
      simp only [advance, TM2.step, subP, TM2.stepAux, h13, List.replicate_succ, List.head?_cons,
        List.tail_cons, Option.isSome_some, cond_true, Option.getD_some]
      rw [Function.update_of_ne (ycne 5 13), h5]
      simp only [List.replicate_succ, List.cons_append, List.tail_cons]
    rw [hstep, ih _ R (some true) (by rw [Function.update_of_ne (ycne 13 5),
      Function.update_self]) (by rw [Function.update_self])]
    congr 1
    funext y
    simp only [Function.update_apply]
    split_ifs <;> simp_all [yc]

/-! ## The emission program -/

def emitProgram :=
  BitMachineRawSequence.program parseP
    (BitMachineRawSequence.program cpK1
      (BitMachineRawSequence.program cpRows
        (BitMachineRawSequence.program cpCols
          (BitMachineRawSequence.program cpMat
            (BitMachineRawSequence.program cpCost
              (BitMachineRawSequence.program cpK13
                (BitMachineRawSequence.program subP serP (.emit 0) none none)
                (BitMachineRawSequence.leftLabel ()) none (none, none))
              (BitMachineRawSequence.leftLabel .scan) none (none, (none, none)))
            (BitMachineRawSequence.leftLabel .scan) none (none, (none, (none, none))))
          (BitMachineRawSequence.leftLabel .scan) none (none, (none, (none, (none, none)))))
        (BitMachineRawSequence.leftLabel .scan) none (none, (none, (none, (none, (none, none))))))
      (BitMachineRawSequence.leftLabel .scan) none (none, (none, (none, (none, (none, (none, none)))))))
    (BitMachineRawSequence.leftLabel .scan) none
    (none, (none, (none, (none, (none, (none, (none, none)))))))

variable (M : BitMachine.Machine)
variable {V E : Type} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

/-- The exact output word of `PhysicalLevelRun.HB2Physical` at `k = kValue M n`. -/
def hb2Word (G : EndpointGraph V E) (n c k : ℕ) : List Bool :=
  let st := PhysicalLevelRun.physRun G c (EffectiveIteration.sourceDepth n)
    (Iteration.seedState (EffectiveIteration.sourceDepth n)) k
  BitMachineBankCodec.encode ![List.replicate n true, List.replicate k true,
    List.replicate st.matrix.rows true, List.replicate st.matrix.columns true,
    MatrixMaterialization.rowMajor st.matrix.entry, List.replicate st.budget true]

theorem Bk_raw (G : EndpointGraph V E) (n c j : ℕ) (i : Fin 6) :
    Bk M G n c j (RoundInstall.consH (WeightedRawWords.consRaw i)) =
      ETHParameterScaleMachineInput.words (Pj G c (EffectiveIteration.sourceDepth n)
        (yP G c (EffectiveIteration.sourceDepth n) j) j (MP G c (EffectiveIteration.sourceDepth n) j)) i := by
  have h := RoundInstall.tgt_cons
    (WeightedRawRowsSource.initialBank (Pj G c (EffectiveIteration.sourceDepth n)
        (yP G c (EffectiveIteration.sourceDepth n) j) j (MP G c (EffectiveIteration.sourceDepth n) j))
      (EncodedETHSource.serializeGraph G) WeightedRawWords.noW)
    (mSj (mb1 M G n c) G c (EffectiveIteration.sourceDepth n) j)
    (Dmw (MatrixMaterialization.rowMajor
      (PhysicalLevelRun.physRun G c (EffectiveIteration.sourceDepth n)
        (Iteration.seedState (EffectiveIteration.sourceDepth n)) j).matrix.entry))
    (WeightedRawWords.consRaw i)
  refine h.trans ?_
  rw [WeightedRawWords.consumer_chain]
  fin_cases i <;> simp [Function.update_apply, RoundInstall.consRaw_inj]

theorem Bk_55 (G : EndpointGraph V E) (n c j : ℕ) :
    Bk M G n c j (RoundInstall.fH 55) = MatrixMaterialization.rowMajor
      (PhysicalLevelRun.physRun G c (EffectiveIteration.sourceDepth n)
        (Iteration.seedState (EffectiveIteration.sourceDepth n)) j).matrix.entry := by
  show Dmw _ 55 = _
  simp [Dmw]

section Full

variable [Fintype BStack]

/-- ONE fixed program: the produced-fuel shell, then the emission. -/
def hb2Program (c : ℕ) {LW₀ VW₀ LW VW : Type}
    (W₀ : LW₀ → TM2.Stmt (fun _ : HStack => Bool) LW₀ VW₀) (w₀₀ : LW₀) (v₀₀ : VW₀)
    (W : LW → TM2.Stmt (fun _ : H4 => Bool) LW VW) (w₀ : LW) (v₀ : VW) :=
  BitMachineRawSequence.program (lift7 (fuelShellProgram M c W₀ w₀₀ v₀₀ W w₀ v₀)) emitProgram
    (BitMachineRawSequence.leftLabel (.scan 0))
    (none, (((((((((((none, ((), ((WeightedRawWords.level0Ctrl, (WeightedRawWords.edgesCtrl, WeightedRawWords.tailCtrl)), WeightedRawWords.kCtrl M))), WeightedVertexWord.vertexCtrl), (WeightedLevelFields15.initialControl, (((), none), WeightedRowFields.rowInit))), ((), none)), ((none : Option Bool), ((none : Option Bool), ((), none)))), ctrl27), (v₀₀, (costCtrl, (NextDimsMachineTN.dimsCtrl, bridgeCtrl)))), (none, ((), none))), installCtrl)), (none, ((), (none, (((((((WeightedLevelFields15.initialControl, (((), none), WeightedRowFields.rowInit)), ((), none)), ((none : Option Bool), ((none : Option Bool), ((), none)))), ctrl27), (v₀, (costCtrl, (NextDimsMachineTN.dimsCtrl, bridgeCtrl)))), (((), none), (none, ((), none)))), installCtrl))))))
    (none, (none, (none, (none, (none, (none, (none, (none, none))))))))

/-- The emission clock (literal sum of the component clocks and the eight handoffs). -/
def emitBound (G : EndpointGraph V E) (n c k : ℕ) : ℕ :=
  let st := PhysicalLevelRun.physRun G c (EffectiveIteration.sourceDepth n)
    (Iteration.seedState (EffectiveIteration.sourceDepth n)) k
  5 * ((SourceOriginalBranchPackets.packet n
      (EncodedGraph.encode (EncodedETHSource.serializeGraph G))).length + 1) +
    (2 * k + 2) + (2 * st.matrix.rows + 2) + (2 * st.matrix.columns + 2) +
    (2 * (MatrixMaterialization.rowMajor st.matrix.entry).length + 2) +
    (2 * (st.budget + k) + 2) + (2 * k + 2) + (k + 1) +
    (2 * (hb2Word G n c k).length + 2) + 8

theorem hb2_bank_run [Fintype MatrixTableInterlaceProtectedBridge.Label]
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
    ∃ t ≤ fuelShellBound M G n c T22₀ T + emitBound G n c (WeightedRawWords.kValue M n) + 1,
      ∃ Y : H7 → List Bool,
      ((advance (hb2Program M c W₀ w₀₀ v₀₀ W w₀ v₀))^[t])
          ⟨some (BitMachineRawSequence.leftLabel (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)),
            ((none, (((((((((((none, ((), ((WeightedRawWords.level0Ctrl, (WeightedRawWords.edgesCtrl, WeightedRawWords.tailCtrl)), WeightedRawWords.kCtrl M))), WeightedVertexWord.vertexCtrl), (WeightedLevelFields15.initialControl, (((), none), WeightedRowFields.rowInit))), ((), none)), ((none : Option Bool), ((none : Option Bool), ((), none)))), ctrl27), (v₀₀, (costCtrl, (NextDimsMachineTN.dimsCtrl, bridgeCtrl)))), (none, ((), none))), installCtrl)), (none, ((), (none, (((((((WeightedLevelFields15.initialControl, (((), none), WeightedRowFields.rowInit)), ((), none)), ((none : Option Bool), ((none : Option Bool), ((), none)))), ctrl27), (v₀, (costCtrl, (NextDimsMachineTN.dimsCtrl, bridgeCtrl)))), (((), none), (none, ((), none)))), installCtrl)))))),
              (none, (none, (none, (none, (none, (none, (none, (none, none))))))))),
            ext7 (ext6 (ext4 (H0 (SourceOriginalBranchPackets.packet n
              (EncodedGraph.encode (EncodedETHSource.serializeGraph G)))) blank57) blank8) blank16⟩ =
        ⟨none, ((none, (((((((((((none, ((), ((WeightedRawWords.level0Ctrl, (WeightedRawWords.edgesCtrl, WeightedRawWords.tailCtrl)), WeightedRawWords.kCtrl M))), WeightedVertexWord.vertexCtrl), (WeightedLevelFields15.initialControl, (((), none), WeightedRowFields.rowInit))), ((), none)), ((none : Option Bool), ((none : Option Bool), ((), none)))), ctrl27), (v₀₀, (costCtrl, (NextDimsMachineTN.dimsCtrl, bridgeCtrl)))), (none, ((), none))), installCtrl)), (none, ((), (none, (((((((WeightedLevelFields15.initialControl, (((), none), WeightedRowFields.rowInit)), ((), none)), ((none : Option Bool), ((none : Option Bool), ((), none)))), ctrl27), (v₀, (costCtrl, (NextDimsMachineTN.dimsCtrl, bridgeCtrl)))), (((), none), (none, ((), none)))), installCtrl)))))),
              (none, (none, (none, (none, (none, (none, (none, (none, none))))))))), Y⟩ ∧
      Y (yc 8) = hb2Word G n c (WeightedRawWords.kValue M n) ∧
      (∀ x : H4, Y (r7 x) = Bk M G n c (WeightedRawWords.kValue M n) x) ∧
      (∀ i : Fin 8, Y (x7 (xc i)) = []) ∧
      Y (yc 9) = EncodedGraph.encode (EncodedETHSource.serializeGraph G) ∧
      (∀ i : Fin 16, 6 ≤ i.val → i ≠ 8 → i ≠ 9 → Y (yc i) = []) := by
  set k := WeightedRawWords.kValue M n with hkdef
  set w := EncodedGraph.encode (EncodedETHSource.serializeGraph G) with hw
  set pk := SourceOriginalBranchPackets.packet n w with hpk
  set st := PhysicalLevelRun.physRun G c (EffectiveIteration.sourceDepth n)
    (Iteration.seedState (EffectiveIteration.sourceDepth n)) k with hst
  -- 0. the produced-fuel shell, lifted
  obtain ⟨t0, ht0, h0⟩ := fuel_shell_run M G n c hc hk W₀ w₀₀ v₀₀ T22₀ hW₀ W w₀ v₀ T22 T hW hT
  have h0' := lift7_run _ _ _ _ _ _ _ blank16 t0 h0
  set Y0 : H7 → List Bool := ext7 (ext6 (Bk M G n c k) (Function.update blank8 1 pk)) blank16 with hY0
  have y0c : ∀ j : Fin 16, Y0 (Sum.inr j) = [] := fun _ => rfl
  have y0x : ∀ i : Fin 8, Y0 (Sum.inl (Sum.inr i)) = Function.update blank8 1 pk i := fun _ => rfl
  have y0r : ∀ x : H4, Y0 (Sum.inl (Sum.inl x)) = Bk M G n c k x := fun _ => rfl
  have b8 : ∀ i : Fin 8, blank8 i = [] := fun _ => rfl
  -- 1. parse
  obtain ⟨t1, ht1, s1⟩ := parse_run Y0 n w
    (by show Function.update blank8 1 pk 1 = _; exact Function.update_self _ _ _) rfl rfl rfl rfl
  set Y1 := bank pE Y0 (BitMachineBankCodec.contents (SourceOriginalBranchPackets.bank n w) [] [] [])
    with hY1
  have y1 : ∀ y, Y1 y =
      if y = yc 0 then List.replicate n true else if y = yc 9 then w else
      if y = x7 (xc 1) then [] else if y = yc 10 then [] else if y = yc 11 then [] else Y0 y := by
    intro y
    rw [hY1, bank_pE]
    rfl
  -- 2..7. the copies
  have e2 : Y1 (r7 (RoundInstall.mH .K)) = List.replicate k true := by
    rw [y1]; simp only [r7, yc, x7, xc, reduceCtorEq, Sum.inl.injEq, ↓reduceIte]
    exact Bk_K M G n c k
  have s2 := cp7_run (r7 (RoundInstall.mH .K)) (yc 1) (r7_ne_yc _ _) (r7_ne_yc _ _) (yc_ne (by decide))
    Y1 (by simp [Function.update_apply, y1, r7, yc, x7, xc, y0c, y0x, y0r, b8]) (by simp [Function.update_apply, y1, r7, yc, x7, xc, y0c, y0x, y0r, b8])
  rw [e2, List.length_replicate] at s2
  set Y2 := Function.update Y1 (yc 1) (List.replicate k true) with hY2
  have e3 : Y2 (r7 (RoundInstall.consH (WeightedRawWords.consRaw 3))) =
      List.replicate st.matrix.rows true := by
    simp only [hY2, Function.update_apply, y1, r7, yc, x7, xc, reduceCtorEq, Sum.inl.injEq, ↓reduceIte]
    exact Bk_raw M G n c k 3
  have s3 := cp7_run (r7 (RoundInstall.consH (WeightedRawWords.consRaw 3))) (yc 2) (r7_ne_yc _ _)
    (r7_ne_yc _ _) (yc_ne (by decide)) Y2 (by simp [hY2, Function.update_apply, y1, r7, yc, x7, xc, y0c, y0x, y0r, b8]) (by simp [hY2, Function.update_apply, y1, r7, yc, x7, xc, y0c, y0x, y0r, b8])
  rw [e3, List.length_replicate] at s3
  set Y3 := Function.update Y2 (yc 2) (List.replicate st.matrix.rows true) with hY3
  have e4 : Y3 (r7 (RoundInstall.consH (WeightedRawWords.consRaw 4))) =
      List.replicate st.matrix.columns true := by
    simp only [hY3, hY2, Function.update_apply, y1, r7, yc, x7, xc, reduceCtorEq, Sum.inl.injEq,
      ↓reduceIte]
    exact Bk_raw M G n c k 4
  have s4 := cp7_run (r7 (RoundInstall.consH (WeightedRawWords.consRaw 4))) (yc 3) (r7_ne_yc _ _)
    (r7_ne_yc _ _) (yc_ne (by decide)) Y3 (by simp [hY3, hY2, Function.update_apply, y1, r7, yc, x7, xc, y0c, y0x, y0r, b8]) (by simp [hY3, hY2, Function.update_apply, y1, r7, yc, x7, xc, y0c, y0x, y0r, b8])
  rw [e4, List.length_replicate] at s4
  set Y4 := Function.update Y3 (yc 3) (List.replicate st.matrix.columns true) with hY4
  have e5 : Y4 (r7 (RoundInstall.fH 55)) = MatrixMaterialization.rowMajor st.matrix.entry := by
    simp only [hY4, hY3, hY2, Function.update_apply, y1, r7, yc, x7, xc, reduceCtorEq, Sum.inl.injEq,
      ↓reduceIte]
    exact Bk_55 M G n c k
  have s5 := cp7_run (r7 (RoundInstall.fH 55)) (yc 4) (r7_ne_yc _ _) (r7_ne_yc _ _) (yc_ne (by decide))
    Y4 (by simp [hY4, hY3, hY2, Function.update_apply, y1, r7, yc, x7, xc, y0c, y0x, y0r, b8]) (by simp [hY4, hY3, hY2, Function.update_apply, y1, r7, yc, x7, xc, y0c, y0x, y0r, b8])
  rw [e5] at s5
  set Y5 := Function.update Y4 (yc 4) (MatrixMaterialization.rowMajor st.matrix.entry) with hY5
  have e6 : Y5 (r7 (RoundInstall.consH (WeightedRawWords.consRaw 2))) =
      List.replicate (st.budget + k) true := by
    simp only [hY5, hY4, hY3, hY2, Function.update_apply, y1, r7, yc, x7, xc, reduceCtorEq,
      Sum.inl.injEq, ↓reduceIte]
    exact Bk_raw M G n c k 2
  have s6 := cp7_run (r7 (RoundInstall.consH (WeightedRawWords.consRaw 2))) (yc 5) (r7_ne_yc _ _)
    (r7_ne_yc _ _) (yc_ne (by decide)) Y5 (by simp [hY5, hY4, hY3, hY2, Function.update_apply, y1, r7, yc, x7, xc, y0c, y0x, y0r, b8]) (by simp [hY5, hY4, hY3, hY2, Function.update_apply, y1, r7, yc, x7, xc, y0c, y0x, y0r, b8])
  rw [e6, List.length_replicate] at s6
  set Y6 := Function.update Y5 (yc 5) (List.replicate (st.budget + k) true) with hY6
  have e7 : Y6 (r7 (RoundInstall.mH .K)) = List.replicate k true := by
    simp only [hY6, hY5, hY4, hY3, hY2, Function.update_apply, r7, yc, reduceCtorEq, ↓reduceIte]
    exact e2
  have s7 := cp7_run (r7 (RoundInstall.mH .K)) (yc 13) (r7_ne_yc _ _) (r7_ne_yc _ _) (yc_ne (by decide))
    Y6 (by simp [hY6, hY5, hY4, hY3, hY2, Function.update_apply, y1, r7, yc, x7, xc, y0c, y0x, y0r, b8]) (by simp [hY6, hY5, hY4, hY3, hY2, Function.update_apply, y1, r7, yc, x7, xc, y0c, y0x, y0r, b8])
  rw [e7, List.length_replicate] at s7
  set Y7 := Function.update Y6 (yc 13) (List.replicate k true) with hY7
  -- 8. subtract the k marks
  have s8 := sub_run k Y7 (List.replicate st.budget true) none (by rw [hY7, Function.update_self])
    (by rw [hY7, Function.update_of_ne (ycne 5 13), hY6, Function.update_self, Nat.add_comm,
      List.replicate_add])
  set Y8 := Function.update (Function.update Y7 (yc 13) []) (yc 5) (List.replicate st.budget true)
    with hY8
  -- 9. serialize
  have y8b : ∀ i : Fin 6, Y8 (sE (.inl i)) =
      ![List.replicate n true, List.replicate k true, List.replicate st.matrix.rows true,
        List.replicate st.matrix.columns true, MatrixMaterialization.rowMajor st.matrix.entry,
        List.replicate st.budget true] i := by
    intro i
    rw [sE_inl]
    fin_cases i <;> simp [hY8, hY7, hY6, hY5, hY4, hY3, hY2, Function.update_apply, yc, y1]
  have hwords : (fun i : Fin 6 => Y8 (sE (.inl i))) =
      ![List.replicate n true, List.replicate k true, List.replicate st.matrix.rows true,
        List.replicate st.matrix.columns true, MatrixMaterialization.rowMajor st.matrix.entry,
        List.replicate st.budget true] := funext y8b
  have henc : BitMachineBankSerialize.encode (List.ofFn (fun i : Fin 6 => Y8 (sE (.inl i)))) =
      hb2Word G n c k := by
    rw [hwords]
    unfold hb2Word
    rw [BitMachineBankCodec.encode_eq_list]
    rfl
  have y8o : ∀ i : Fin 16, 6 ≤ i.val → i ≠ 9 → Y8 (yc i) = [] := by
    intro i h6 h9
    fin_cases i <;> first
      | (exfalso; simp at h6; done)
      | (exfalso; exact h9 rfl)
      | simp [hY8, hY7, hY6, hY5, hY4, hY3, hY2, Function.update_apply, y1, r7, yc, x7, xc, y0c, y0x, y0r, b8]
  obtain ⟨t9, ht9, S', s9⟩ := ser_run Y8 (y8o 6 (by decide) (by decide))
    (y8o 7 (by decide) (by decide)) (y8o 8 (by decide) (by decide))
  rw [henc] at ht9 s9
  -- compose the emission (innermost first)
  obtain ⟨u8, hu8, r8⟩ := BitMachineRawSequence.runs subP serP () (.emit 0) _ _ _ _ _ _ _ (k + 1) t9 s8 s9
  obtain ⟨u7, hu7, r7'⟩ := BitMachineRawSequence.runs cpK13 _ _ _ _ _ _ _ _ _ _ _ _ s7 r8
  obtain ⟨u6, hu6, r6⟩ := BitMachineRawSequence.runs cpCost _ _ _ _ _ _ _ _ _ _ _ _ s6 r7'
  obtain ⟨u5, hu5, r5⟩ := BitMachineRawSequence.runs cpMat _ _ _ _ _ _ _ _ _ _ _ _ s5 r6
  obtain ⟨u4, hu4, r4⟩ := BitMachineRawSequence.runs cpCols _ _ _ _ _ _ _ _ _ _ _ _ s4 r5
  obtain ⟨u3, hu3, r3⟩ := BitMachineRawSequence.runs cpRows _ _ _ _ _ _ _ _ _ _ _ _ s3 r4
  obtain ⟨u2, hu2, r2⟩ := BitMachineRawSequence.runs cpK1 _ _ _ _ _ _ _ _ _ _ _ _ s2 r3
  obtain ⟨u1, hu1, r1⟩ := BitMachineRawSequence.runs parseP _ _ _ _ _ _ _ _ _ _ _ _ s1 r2
  obtain ⟨u0, hu0, r0⟩ := BitMachineRawSequence.runs
    (lift7 (fuelShellProgram M c W₀ w₀₀ v₀₀ W w₀ v₀)) emitProgram _ _ _ _ _ _ _ _ _ _ _ h0' r1
  refine ⟨u0, ?_, _, r0, ?_, ?_, ?_, ?_, ?_⟩
  · have hb : emitBound G n c k = 5 * ((SourceOriginalBranchPackets.packet n w).length + 1) + (2 * k + 2) + (2 * st.matrix.rows + 2) +
        (2 * st.matrix.columns + 2) + (2 * (MatrixMaterialization.rowMajor st.matrix.entry).length + 2) +
        (2 * (st.budget + k) + 2) + (2 * k + 2) + (k + 1) + (2 * (hb2Word G n c k).length + 2) + 8 := rfl
    rw [hb]
    omega
  · -- the output cell
    show bank sE Y8 _ (sE (.inr 2)) = _
    rw [bank_at]
    simp [BitMachineBankSerialize.contents]
  · intro x
    rw [bank_sE_out _ _ _ (fun i _ => r7_ne_yc x i)]
    simp [hY8, hY7, hY6, hY5, hY4, hY3, hY2, Function.update_apply, y1, r7, yc, x7, xc, y0c, y0x, y0r, b8]
  · intro i
    rw [bank_sE_out _ _ _ (fun j _ h => by cases h)]
    by_cases hi : i = 1 <;> simp [hi, hY8, hY7, hY6, hY5, hY4, hY3, hY2, Function.update_apply, y1, r7, yc, x7, xc, y0c, y0x, y0r, b8]
  · rw [bank_sE_out _ _ _ (fun j hj h => by
      have := Sum.inr.inj h; subst this; simp at hj)]
    simp [hY8, hY7, hY6, hY5, hY4, hY3, hY2, Function.update_apply, y1, r7, yc, x7, xc, y0c, y0x, y0r, b8]
  · intro i h6 h8 h9
    by_cases h67 : i.val < 9
    · have hi : i = 6 ∨ i = 7 := by
        rcases i with ⟨i, hi⟩
        simp only [ne_eq, Fin.ext_iff] at h8 ⊢
        simp at h6 h67 h8
        omega
      rcases hi with rfl | rfl
      · rw [show yc 6 = sE (.inr 0) from rfl, bank_at]; rfl
      · rw [show yc 7 = sE (.inr 1) from rfl, bank_at]; rfl
    · rw [bank_sE_out _ _ _ (fun j hj h => by
        have := Sum.inr.inj h; subst this; omega)]
      exact y8o i h6 h9

#print axioms hb2_bank_run

end Full

#print axioms parse_run
#print axioms ser_run
#print axioms sub_run
#print axioms Bk_raw
#print axioms Bk_55

end
end EthInapproximability.CurrentPaper.Emission
