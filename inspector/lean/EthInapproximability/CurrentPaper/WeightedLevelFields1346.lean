import EthInapproximability.CurrentPaper.WeightedLevelStagePrefix

/-! Lane owner:b-weighted-level-2, unit 2, segment 2 (partial): persistent
writer fields 1 (`uniform`), 3 (`fullBoundary`), 4 (`fullDivisor`) and
6 (`diagonalDivisor`) physically produced on the SAME reached bank.

ONE fixed controller: the frozen `WeightedLevelStagePrefix.program` (checked
privately by lane owner:b-weighted-level, unedited), then a fixed tail:

1. charged pop-until-empty clear of writer 1, 3, 4, 6 (their reached content
   is not assumed blank);
2. a fixed constant writer pushes the unary word `182` (a constant of the
   construction, `eq` of `fullDivisor`) into the blank writer 30;
3. charged unary multiplication writer30 x writer29 -> writer4
   (`182 * binBase`);
4. charged unary multiplication writer21 x writer4 -> writer3
   (`cols * (182 * binBase)`);
5. two charged copies writer21 -> writer6 (`2 * cols`);
6. constant `[true]` into writer 1, a charged copy writer28 -> writer31
   (fuel `s`), and the admitted weighted power machine
   (`binBase ^ s` into writer 1; fuel consumed);
7. charged pop-until-empty clear of writer 30.

All scratch (save 4..6, writer 30..32) is blank before and after. Every
operand is read from the cells the frozen controller physically produced
(`binBase` 29, `cols` 21, `s` 28). The identities with the SAME
`ProtectedFullBankBridgeScratch.actualD` are arithmetic facts about
`MatrixWeightedEntrySemantic.actualInput`. -/

namespace EthInapproximability.CurrentPaper.WeightedLevelFields1346

open Turing BitMachineEncoding BitMachineStackEmbedding
open MatrixStage4ScalarPreparationOps
open EthInapproximability.ParameterizedNP.GuardedSourceGraph
open WeightedLevelColumnSave

noncomputable section

set_option synthInstance.maxSize 200000
set_option synthInstance.maxHeartbeats 2000000

/-! ## Cell disequalities -/

theorem wcell_ne {j k : Fin 64} (h : j ≠ k) : wcell j ≠ wcell k := by
  intro e
  exact h (WeightedColumnActualStage.writerSlots.injective (Sum.inl_injective e))

theorem save_ne_wcell (j : Fin 7) (k : Fin 64) : save j ≠ wcell k := by
  intro e; cases e

theorem wcell_ne_save (k : Fin 64) (j : Fin 7) : wcell k ≠ save j := by
  intro e; cases e

theorem save_ne {i j : Fin 7} (h : i ≠ j) : save i ≠ save j := by
  intro e; exact h (Sum.inr_injective e)

/-! ## Phase 1: clear writer 1, 3, 4, 6 -/

def clearCells4 : Fin 4 ↪ Stack :=
  ⟨![wcell 1, wcell 3, wcell 4, wcell 6], by
    intro x y h
    fin_cases x <;> fin_cases y <;> simp_all [wcell]⟩

inductive ClearLabel where
  | clear (i : Fin 5)
  | done
  deriving DecidableEq, Fintype

def clearProgram : ClearLabel →
    TM2.Stmt (fun _ : Stack => Bool) ClearLabel (Unit × Option Bool)
  | .clear i => if h : i.val < 4 then
      BitMachineClearBank.clearStep (clearCells4 ⟨i.val, h⟩)
        (.clear i) (.clear ⟨i.val + 1, by omega⟩)
    else BitMachineClearBank.finishStep (fun _ => ()) .done
  | .done => .halt

def clearCost4 (S : Stack → List Bool) : ℕ :=
  (∑ i : Fin 4, (S (clearCells4 i)).length) + 6

theorem clear4_run (S : Stack → List Bool) :
    ((advance clearProgram)^[clearCost4 S])
      (⟨some (.clear 0), ((), none), S⟩ :
        TM2.Cfg (fun _ : Stack => Bool) ClearLabel (Unit × Option Bool)) =
      ⟨none, ((), none), BitMachineClearBank.cleared clearCells4 S⟩ := by
  have hs (i : Fin 4) : clearProgram (.clear i.castSucc) =
      BitMachineClearBank.clearStep (clearCells4 i)
        (.clear i.castSucc) (.clear i.succ) := by
    simp only [clearProgram, Fin.val_castSucc, dif_pos i.isLt]
    rfl
  have hf : clearProgram (.clear (Fin.last 4)) =
      BitMachineClearBank.finishStep (fun _ => ()) .done := by
    simp only [clearProgram, Fin.val_last, lt_self_iff_false, ↓reduceDIte]
  have hr := BitMachineClearBank.clear_bank_run clearProgram
    (fun _ => ()) ClearLabel.done 4 clearCells4 clearCells4.injective
    ClearLabel.clear hs hf () S
  have hd : advance clearProgram
      (⟨some .done, ((), none), BitMachineClearBank.cleared clearCells4 S⟩ :
        TM2.Cfg (fun _ : Stack => Bool) ClearLabel (Unit × Option Bool)) =
      ⟨none, ((), none), BitMachineClearBank.cleared clearCells4 S⟩ := rfl
  rw [clearCost4, show (∑ i : Fin 4, (S (clearCells4 i)).length) + 6 =
      1 + ((∑ i : Fin 4, (S (clearCells4 i)).length) + 4 + 1) by omega,
    Function.iterate_add_apply, hr]
  exact hd

theorem mem_clearCells4 (k : Stack) :
    (∃ i, clearCells4 i = k) ↔
      (k = wcell 1 ∨ k = wcell 3 ∨ k = wcell 4 ∨ k = wcell 6) := by
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr rfl))
  · rintro (rfl | rfl | rfl | rfl)
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩
    · exact ⟨3, rfl⟩

theorem cleared4_other (S : Stack → List Bool) (k : Stack)
    (h1 : k ≠ wcell 1) (h3 : k ≠ wcell 3) (h4 : k ≠ wcell 4) (h6 : k ≠ wcell 6) :
    BitMachineClearBank.cleared clearCells4 S k = S k := by
  have hn : ¬ ∃ i, clearCells4 i = k := by
    rw [mem_clearCells4]
    rintro (h | h | h | h)
    · exact h1 h
    · exact h3 h
    · exact h4 h
    · exact h6 h
  simp only [BitMachineClearBank.cleared, if_neg hn]

theorem cleared4_at (S : Stack → List Bool) (k : Stack)
    (hk : k = wcell 1 ∨ k = wcell 3 ∨ k = wcell 4 ∨ k = wcell 6) :
    BitMachineClearBank.cleared clearCells4 S k = [] := by
  have hn : ∃ i, clearCells4 i = k := (mem_clearCells4 k).2 hk
  simp only [BitMachineClearBank.cleared, if_pos hn]

/-! ## A fixed unary constant writer -/

def constProgram (n : ℕ) (cell : Stack) :
    Fin (n + 1) → TM2.Stmt (fun _ : Stack => Bool) (Fin (n + 1)) Unit :=
  fun i => if h : i.val < n then
      .push cell (fun _ => true) (.goto (fun _ => ⟨i.val + 1, by omega⟩))
    else .halt

theorem const_steps (n : ℕ) (cell : Stack) :
    ∀ k m (hm : m + k = n) (S : Stack → List Bool),
      ((advance (constProgram n cell))^[k])
        (⟨some ⟨m, by omega⟩, (), S⟩ :
          TM2.Cfg (fun _ : Stack => Bool) (Fin (n + 1)) Unit) =
        ⟨some ⟨n, by omega⟩, (),
          Function.update S cell (List.replicate k true ++ S cell)⟩ := by
  intro k
  induction k with
  | zero =>
      intro m hm S
      have hmn : m = n := by omega
      subst hmn
      simp
  | succ k ih =>
      intro m hm S
      have hlt : m < n := by omega
      have hstep : advance (constProgram n cell)
          (⟨some ⟨m, by omega⟩, (), S⟩ :
            TM2.Cfg (fun _ : Stack => Bool) (Fin (n + 1)) Unit) =
          ⟨some ⟨m + 1, by omega⟩, (),
            Function.update S cell (true :: S cell)⟩ := by
        simp [advance, TM2.step, TM2.stepAux, constProgram, hlt]
      rw [Function.iterate_succ_apply, hstep, ih (m + 1) (by omega)]
      rw [Function.update_idem, Function.update_self,
        List.replicate_succ', List.append_assoc]
      rfl

theorem const_run (n : ℕ) (cell : Stack) (S : Stack → List Bool)
    (hblank : S cell = []) :
    ((advance (constProgram n cell))^[n + 1])
      (⟨some 0, (), S⟩ : TM2.Cfg (fun _ : Stack => Bool) (Fin (n + 1)) Unit) =
      ⟨none, (), Function.update S cell (List.replicate n true)⟩ := by
  have h := const_steps n cell n 0 (by omega) S
  rw [hblank, List.append_nil] at h
  have e0 : (0 : Fin (n + 1)) = ⟨0, by omega⟩ := Fin.ext (by simp)
  rw [Function.iterate_succ_apply', e0, h]
  simp [advance, TM2.step, TM2.stepAux, constProgram]

/-! ## Pop-until-empty clear of writer 30 -/

inductive PopLabel where
  | pop | stop
  deriving DecidableEq, Fintype

def popProgram : PopLabel →
    TM2.Stmt (fun _ : Stack => Bool) PopLabel (Unit × Option Bool)
  | .pop => BitMachineClearBank.clearStep (wcell 30) PopLabel.pop PopLabel.stop
  | .stop => .halt

theorem pop_run (S : Stack → List Bool) :
    ((advance popProgram)^[(S (wcell 30)).length + 2])
      (⟨some PopLabel.pop, ((), none), S⟩ :
        TM2.Cfg (fun _ : Stack => Bool) PopLabel (Unit × Option Bool)) =
      ⟨none, ((), none), Function.update S (wcell 30) []⟩ := by
  have h := BitMachineClearBank.clear_one_run popProgram (wcell 30)
    PopLabel.pop PopLabel.stop rfl () S
  rw [show (S (wcell 30)).length + 2 = 1 + ((S (wcell 30)).length + 1) by omega,
    Function.iterate_add_apply, h]
  rfl

/-! ## Slot tables -/

def mul4 : Fin 6 ↪ Stack :=
  ⟨![wcell 30, wcell 29, save 4, save 5, save 6, wcell 4], by
    intro x y h
    fin_cases x <;> fin_cases y <;> simp_all [wcell, save]⟩

def mul3 : Fin 6 ↪ Stack :=
  ⟨![wcell 21, wcell 4, save 4, save 5, save 6, wcell 3], by
    intro x y h
    fin_cases x <;> fin_cases y <;> simp_all [wcell, save]⟩

def copy6 : Fin 3 ↪ Stack :=
  ⟨![wcell 21, wcell 6, save 4], by
    intro x y h
    fin_cases x <;> fin_cases y <;> simp_all [wcell, save]⟩

def copyFuel : Fin 3 ↪ Stack :=
  ⟨![wcell 28, wcell 31, save 4], by
    intro x y h
    fin_cases x <;> fin_cases y <;> simp_all [wcell, save]⟩

def powMap : MatrixWeightedPower.Stack → Stack :=
  Sum.elim ![wcell 1, wcell 29, save 4, save 5, save 6, wcell 32] ![wcell 31]

def powSlots : MatrixWeightedPower.Stack ↪ Stack :=
  ⟨powMap, by
    intro x y h
    rcases x with x | x <;> rcases y with y | y <;>
      fin_cases x <;> fin_cases y <;> simp_all [powMap, wcell, save]⟩

/-! ## The fixed tail controller (right-nested raw sequence) -/

abbrev CC := Unit × Option Bool
abbrev CopyC := Option Bool

def seq10 := BitMachineRawSequence.program (weightedPowerProgram powSlots)
  popProgram PopLabel.pop ((false, false) : MatrixWeightedPower.Control)
  ((((), none)) : CC)
def init10 : MatrixWeightedPower.Control × CC := ((false, false), ((), none))
def start10 : BitMachineRawSequence.Label MatrixWeightedPower.Label PopLabel :=
  BitMachineRawSequence.leftLabel (Sum.inr MatrixWeightedPower.Admin.test)

def seq9 := BitMachineRawSequence.program (copyProgram copyFuel) seq10 start10
  (none : CopyC) init10
def init9 := ((none : CopyC), init10)
def start9 : BitMachineRawSequence.Label BitMachineCopy.Label
    (BitMachineRawSequence.Label MatrixWeightedPower.Label PopLabel) :=
  BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan

def seq8 := BitMachineRawSequence.program (constProgram 1 (wcell 1)) seq9 start9
  () init9
def init8 := ((), init9)
def start8 : BitMachineRawSequence.Label (Fin 2) (BitMachineRawSequence.Label
    BitMachineCopy.Label
    (BitMachineRawSequence.Label MatrixWeightedPower.Label PopLabel)) :=
  BitMachineRawSequence.leftLabel 0

def seq7 := BitMachineRawSequence.program (copyProgram copy6) seq8 start8
  (none : CopyC) init8
def init7 := ((none : CopyC), init8)
def start7 := BitMachineRawSequence.leftLabel (LB := BitMachineRawSequence.Label (Fin 2)
  (BitMachineRawSequence.Label BitMachineCopy.Label
    (BitMachineRawSequence.Label MatrixWeightedPower.Label PopLabel)))
  BitMachineCopy.Label.scan

def seq6 := BitMachineRawSequence.program (copyProgram copy6) seq7 start7
  (none : CopyC) init7
def init6 := ((none : CopyC), init7)
def start6 := BitMachineRawSequence.leftLabel (LB := BitMachineRawSequence.Label
  BitMachineCopy.Label (BitMachineRawSequence.Label (Fin 2)
  (BitMachineRawSequence.Label BitMachineCopy.Label
    (BitMachineRawSequence.Label MatrixWeightedPower.Label PopLabel))))
  BitMachineCopy.Label.scan

def seq5 := BitMachineRawSequence.program (multiplyProgram mul3) seq6 start6
  false init6
def init5 := (false, init6)
def start5 := BitMachineRawSequence.leftLabel (LB := BitMachineRawSequence.Label
  BitMachineCopy.Label (BitMachineRawSequence.Label
  BitMachineCopy.Label (BitMachineRawSequence.Label (Fin 2)
  (BitMachineRawSequence.Label BitMachineCopy.Label
    (BitMachineRawSequence.Label MatrixWeightedPower.Label PopLabel)))))
  MatrixAddressMachine.Label.outer

def seq4 := BitMachineRawSequence.program (multiplyProgram mul4) seq5 start5
  false init5
def init4 := (false, init5)
def start4 := BitMachineRawSequence.leftLabel (LB := BitMachineRawSequence.Label
  MatrixAddressMachine.Label (BitMachineRawSequence.Label
  BitMachineCopy.Label (BitMachineRawSequence.Label
  BitMachineCopy.Label (BitMachineRawSequence.Label (Fin 2)
  (BitMachineRawSequence.Label BitMachineCopy.Label
    (BitMachineRawSequence.Label MatrixWeightedPower.Label PopLabel))))))
  MatrixAddressMachine.Label.outer

def seq3 := BitMachineRawSequence.program (constProgram 182 (wcell 30)) seq4 start4
  () init4
def init3 := ((), init4)
def start3 := BitMachineRawSequence.leftLabel (LB := BitMachineRawSequence.Label
  MatrixAddressMachine.Label (BitMachineRawSequence.Label
  MatrixAddressMachine.Label (BitMachineRawSequence.Label
  BitMachineCopy.Label (BitMachineRawSequence.Label
  BitMachineCopy.Label (BitMachineRawSequence.Label (Fin 2)
  (BitMachineRawSequence.Label BitMachineCopy.Label
    (BitMachineRawSequence.Label MatrixWeightedPower.Label PopLabel)))))))
  (0 : Fin 183)

/-- The fixed tail controller. -/
def tailProgram := BitMachineRawSequence.program clearProgram seq3 start3
  ((((), none)) : CC) init3
def tailInitial := (((((), none)) : CC), init3)
def tailStart := BitMachineRawSequence.leftLabel (LB := BitMachineRawSequence.Label
  (Fin 183) (BitMachineRawSequence.Label
  MatrixAddressMachine.Label (BitMachineRawSequence.Label
  MatrixAddressMachine.Label (BitMachineRawSequence.Label
  BitMachineCopy.Label (BitMachineRawSequence.Label
  BitMachineCopy.Label (BitMachineRawSequence.Label (Fin 2)
  (BitMachineRawSequence.Label BitMachineCopy.Label
    (BitMachineRawSequence.Label MatrixWeightedPower.Label PopLabel))))))))
  (ClearLabel.clear 0)

/-- Exit bank of the tail: exactly four writer cells replaced. -/
def fieldsBank (S : Stack → List Bool) (B C s : ℕ) : Stack → List Bool :=
  Function.update (Function.update (Function.update (Function.update S
    (wcell 1) (List.replicate (B ^ s) true))
    (wcell 3) (List.replicate (C * (182 * B)) true))
    (wcell 4) (List.replicate (182 * B) true))
    (wcell 6) (List.replicate (2 * C) true)

def tailCost (S : Stack → List Bool) (B C s : ℕ) : ℕ :=
  clearCost4 S + (182 + 1) + MatrixAddressMachine.exactTime 182 B 0 +
    MatrixAddressMachine.exactTime C (182 * B) 0 + (2 * C + 2) + (2 * C + 2) +
    (1 + 1) + (2 * s + 2) + MatrixWeightedPower.powerBound B s + (182 + 2) + 9

theorem tail_run (S : Stack → List Bool) (B C s : ℕ)
    (h29 : S (wcell 29) = List.replicate B true)
    (h21 : S (wcell 21) = List.replicate C true)
    (h28 : S (wcell 28) = List.replicate s true)
    (hs4 : S (save 4) = []) (hs5 : S (save 5) = []) (hs6 : S (save 6) = [])
    (h30 : S (wcell 30) = []) (h31 : S (wcell 31) = []) (h32 : S (wcell 32) = []) :
    ∃ t ≤ tailCost S B C s,
      ((advance tailProgram)^[t])
        (⟨some tailStart, tailInitial, S⟩ : TM2.Cfg (fun _ : Stack => Bool) _ _) =
        ⟨none, tailInitial, fieldsBank S B C s⟩ := by
  -- phase banks
  let S1 := BitMachineClearBank.cleared clearCells4 S
  let S2 := Function.update S1 (wcell 30) (List.replicate 182 true)
  let S3 := Function.update S2 (wcell 4) (List.replicate (182 * B) true)
  let S4 := Function.update S3 (wcell 3) (List.replicate (C * (182 * B)) true)
  let S5 := Function.update S4 (wcell 6) (List.replicate C true)
  let S6 := Function.update S4 (wcell 6) (List.replicate (2 * C) true)
  let S7 := Function.update S6 (wcell 1) (List.replicate 1 true)
  let S8 := Function.update S7 (wcell 31) (List.replicate s true)
  let S9 := Function.update (Function.update S8 (wcell 1)
    (List.replicate (B ^ s) true)) (wcell 31) []
  let S10 := Function.update S9 (wcell 30) []
  -- frame facts on S1
  have o1 (k : Stack) (h1 : k ≠ wcell 1) (h3 : k ≠ wcell 3) (h4 : k ≠ wcell 4)
      (h6 : k ≠ wcell 6) : S1 k = S k := cleared4_other S k h1 h3 h4 h6
  have c4 : S1 (wcell 4) = [] := cleared4_at S _ (Or.inr (Or.inr (Or.inl rfl)))
  have c3 : S1 (wcell 3) = [] := cleared4_at S _ (Or.inr (Or.inl rfl))
  have c6 : S1 (wcell 6) = [] := cleared4_at S _ (Or.inr (Or.inr (Or.inr rfl)))
  have c1 : S1 (wcell 1) = [] := cleared4_at S _ (Or.inl rfl)
  have r1 := clear4_run S
  -- phase 2: constant 182 into writer 30
  have e30 : S1 (wcell 30) = [] := by
    rw [o1 (wcell 30) (wcell_ne (by decide)) (wcell_ne (by decide)) (wcell_ne (by decide))
      (wcell_ne (by decide))]
    exact h30
  have r2 := const_run 182 (wcell 30) S1 e30
  -- phase 3: 182 * B into writer 4
  have m4 := multiply_run mul4 S2 182 B
    (by show S2 (wcell 30) = _; simp only [S2, Function.update_self])
    (by
      show S2 (wcell 29) = _
      simp only [S2, Function.update_of_ne (wcell_ne (by decide) : wcell 29 ≠ wcell 30)]
      rw [o1 (wcell 29) (wcell_ne (by decide)) (wcell_ne (by decide)) (wcell_ne (by decide))
        (wcell_ne (by decide))]
      exact h29)
    (by
      show S2 (save 4) = _
      simp only [S2, Function.update_of_ne (save_ne_wcell 4 30)]
      rw [o1 (save 4) (save_ne_wcell _ _) (save_ne_wcell _ _) (save_ne_wcell _ _)
        (save_ne_wcell _ _)]
      exact hs4)
    (by
      show S2 (save 5) = _
      simp only [S2, Function.update_of_ne (save_ne_wcell 5 30)]
      rw [o1 (save 5) (save_ne_wcell _ _) (save_ne_wcell _ _) (save_ne_wcell _ _)
        (save_ne_wcell _ _)]
      exact hs5)
    (by
      show S2 (save 6) = _
      simp only [S2, Function.update_of_ne (save_ne_wcell 6 30)]
      rw [o1 (save 6) (save_ne_wcell _ _) (save_ne_wcell _ _) (save_ne_wcell _ _)
        (save_ne_wcell _ _)]
      exact hs6)
  have e4 : S2 (mul4 5) = [] := by
    show S2 (wcell 4) = []
    simp only [S2, Function.update_of_ne (wcell_ne (by decide) : wcell 4 ≠ wcell 30)]
    exact c4
  rw [e4, List.append_nil] at m4
  -- phase 4: C * (182 * B) into writer 3
  have m3 := multiply_run mul3 S3 C (182 * B)
    (by
      show S3 (wcell 21) = _
      simp only [S3, S2,
        Function.update_of_ne (wcell_ne (by decide) : wcell 21 ≠ wcell 4),
        Function.update_of_ne (wcell_ne (by decide) : wcell 21 ≠ wcell 30)]
      rw [o1 (wcell 21) (wcell_ne (by decide)) (wcell_ne (by decide)) (wcell_ne (by decide))
        (wcell_ne (by decide))]
      exact h21)
    (by show S3 (wcell 4) = _; simp only [S3, Function.update_self])
    (by
      show S3 (save 4) = _
      simp only [S3, S2, Function.update_of_ne (save_ne_wcell 4 4),
        Function.update_of_ne (save_ne_wcell 4 30)]
      rw [o1 (save 4) (save_ne_wcell _ _) (save_ne_wcell _ _) (save_ne_wcell _ _)
        (save_ne_wcell _ _)]
      exact hs4)
    (by
      show S3 (save 5) = _
      simp only [S3, S2, Function.update_of_ne (save_ne_wcell 5 4),
        Function.update_of_ne (save_ne_wcell 5 30)]
      rw [o1 (save 5) (save_ne_wcell _ _) (save_ne_wcell _ _) (save_ne_wcell _ _)
        (save_ne_wcell _ _)]
      exact hs5)
    (by
      show S3 (save 6) = _
      simp only [S3, S2, Function.update_of_ne (save_ne_wcell 6 4),
        Function.update_of_ne (save_ne_wcell 6 30)]
      rw [o1 (save 6) (save_ne_wcell _ _) (save_ne_wcell _ _) (save_ne_wcell _ _)
        (save_ne_wcell _ _)]
      exact hs6)
  have e3 : S3 (mul3 5) = [] := by
    show S3 (wcell 3) = []
    simp only [S3, S2,
      Function.update_of_ne (wcell_ne (by decide) : wcell 3 ≠ wcell 4),
      Function.update_of_ne (wcell_ne (by decide) : wcell 3 ≠ wcell 30)]
    exact c3
  rw [e3, List.append_nil] at m3
  -- phases 5-6: two copies of cols into writer 6
  have s4_21 : S4 (wcell 21) = List.replicate C true := by
    simp only [S4, S3, S2,
      Function.update_of_ne (wcell_ne (by decide) : wcell 21 ≠ wcell 3),
      Function.update_of_ne (wcell_ne (by decide) : wcell 21 ≠ wcell 4),
      Function.update_of_ne (wcell_ne (by decide) : wcell 21 ≠ wcell 30)]
    rw [o1 (wcell 21) (wcell_ne (by decide)) (wcell_ne (by decide)) (wcell_ne (by decide))
      (wcell_ne (by decide))]
    exact h21
  have s4_save4 : S4 (save 4) = [] := by
    simp only [S4, S3, S2, Function.update_of_ne (save_ne_wcell 4 3),
      Function.update_of_ne (save_ne_wcell 4 4),
      Function.update_of_ne (save_ne_wcell 4 30)]
    rw [o1 (save 4) (save_ne_wcell _ _) (save_ne_wcell _ _) (save_ne_wcell _ _)
      (save_ne_wcell _ _)]
    exact hs4
  have s4_6 : S4 (wcell 6) = [] := by
    simp only [S4, S3, S2,
      Function.update_of_ne (wcell_ne (by decide) : wcell 6 ≠ wcell 3),
      Function.update_of_ne (wcell_ne (by decide) : wcell 6 ≠ wcell 4),
      Function.update_of_ne (wcell_ne (by decide) : wcell 6 ≠ wcell 30)]
    exact c6
  have k5 := copy_run copy6 S4 s4_save4
  have k5' : ((advance (copyProgram copy6))^[2 * C + 2])
      (⟨some .scan, none, S4⟩ : TM2.Cfg (fun _ : Stack => Bool)
        BitMachineCopy.Label (Option Bool)) = ⟨none, none, S5⟩ := by
    have ha : S4 (copy6 0) = List.replicate C true := s4_21
    have hb : S4 (copy6 1) = [] := s4_6
    rw [ha, hb, List.append_nil, List.length_replicate] at k5
    exact k5
  have s5_21 : S5 (copy6 0) = List.replicate C true := by
    show S5 (wcell 21) = _
    simp only [S5, Function.update_of_ne (wcell_ne (by decide) : wcell 21 ≠ wcell 6)]
    exact s4_21
  have s5_save4 : S5 (copy6 2) = [] := by
    show S5 (save 4) = _
    simp only [S5, Function.update_of_ne (save_ne_wcell 4 6)]
    exact s4_save4
  have k6 := copy_run copy6 S5 s5_save4
  have k6' : ((advance (copyProgram copy6))^[2 * C + 2])
      (⟨some .scan, none, S5⟩ : TM2.Cfg (fun _ : Stack => Bool)
        BitMachineCopy.Label (Option Bool)) = ⟨none, none, S6⟩ := by
    have hb : S5 (copy6 1) = List.replicate C true := by
      show S5 (wcell 6) = _
      simp only [S5, Function.update_self]
    rw [s5_21, hb, List.length_replicate, List.replicate_append_replicate] at k6
    rw [k6]
    show (⟨none, none, Function.update S5 (wcell 6)
      (List.replicate (C + C) true)⟩ : TM2.Cfg (fun _ : Stack => Bool)
        BitMachineCopy.Label (Option Bool)) = ⟨none, none, S6⟩
    simp only [S5, S6, Function.update_idem, two_mul]
  -- phase 7: constant [true] into writer 1
  have s6_1 : S6 (wcell 1) = [] := by
    simp only [S6, S4, S3, S2,
      Function.update_of_ne (wcell_ne (by decide) : wcell 1 ≠ wcell 6),
      Function.update_of_ne (wcell_ne (by decide) : wcell 1 ≠ wcell 3),
      Function.update_of_ne (wcell_ne (by decide) : wcell 1 ≠ wcell 4),
      Function.update_of_ne (wcell_ne (by decide) : wcell 1 ≠ wcell 30)]
    exact c1
  have r7 := const_run 1 (wcell 1) S6 s6_1
  -- phase 8: fuel copy writer 28 -> writer 31
  have s7_28 : S7 (copyFuel 0) = List.replicate s true := by
    show S7 (wcell 28) = _
    simp only [S7, S6, S4, S3, S2,
      Function.update_of_ne (wcell_ne (by decide) : wcell 28 ≠ wcell 1),
      Function.update_of_ne (wcell_ne (by decide) : wcell 28 ≠ wcell 6),
      Function.update_of_ne (wcell_ne (by decide) : wcell 28 ≠ wcell 3),
      Function.update_of_ne (wcell_ne (by decide) : wcell 28 ≠ wcell 4),
      Function.update_of_ne (wcell_ne (by decide) : wcell 28 ≠ wcell 30)]
    rw [o1 (wcell 28) (wcell_ne (by decide)) (wcell_ne (by decide)) (wcell_ne (by decide))
      (wcell_ne (by decide))]
    exact h28
  have s7_31 : S7 (copyFuel 1) = [] := by
    show S7 (wcell 31) = _
    simp only [S7, S6, S4, S3, S2,
      Function.update_of_ne (wcell_ne (by decide) : wcell 31 ≠ wcell 1),
      Function.update_of_ne (wcell_ne (by decide) : wcell 31 ≠ wcell 6),
      Function.update_of_ne (wcell_ne (by decide) : wcell 31 ≠ wcell 3),
      Function.update_of_ne (wcell_ne (by decide) : wcell 31 ≠ wcell 4),
      Function.update_of_ne (wcell_ne (by decide) : wcell 31 ≠ wcell 30)]
    rw [o1 (wcell 31) (wcell_ne (by decide)) (wcell_ne (by decide)) (wcell_ne (by decide))
      (wcell_ne (by decide))]
    exact h31
  have s7_save4 : S7 (copyFuel 2) = [] := by
    show S7 (save 4) = _
    simp only [S7, S6, S4, S3, S2, Function.update_of_ne (save_ne_wcell 4 1),
      Function.update_of_ne (save_ne_wcell 4 6),
      Function.update_of_ne (save_ne_wcell 4 3),
      Function.update_of_ne (save_ne_wcell 4 4),
      Function.update_of_ne (save_ne_wcell 4 30)]
    rw [o1 (save 4) (save_ne_wcell _ _) (save_ne_wcell _ _) (save_ne_wcell _ _)
      (save_ne_wcell _ _)]
    exact hs4
  have k8 := copy_run copyFuel S7 s7_save4
  rw [s7_28, s7_31, List.append_nil, List.length_replicate] at k8
  -- phase 9: weighted power binBase ^ s into writer 1
  have pw := weighted_power_run powSlots S8 B s
    (by
      show S8 (wcell 1) = _
      simp only [S8, S7,
        Function.update_of_ne (wcell_ne (by decide) : wcell 1 ≠ wcell 31),
        Function.update_self, List.replicate_one])
    (by
      show S8 (wcell 29) = _
      simp only [S8, S7, S6, S4, S3, S2,
        Function.update_of_ne (wcell_ne (by decide) : wcell 29 ≠ wcell 31),
        Function.update_of_ne (wcell_ne (by decide) : wcell 29 ≠ wcell 1),
        Function.update_of_ne (wcell_ne (by decide) : wcell 29 ≠ wcell 6),
        Function.update_of_ne (wcell_ne (by decide) : wcell 29 ≠ wcell 3),
        Function.update_of_ne (wcell_ne (by decide) : wcell 29 ≠ wcell 4),
        Function.update_of_ne (wcell_ne (by decide) : wcell 29 ≠ wcell 30)]
      rw [o1 (wcell 29) (wcell_ne (by decide)) (wcell_ne (by decide)) (wcell_ne (by decide))
        (wcell_ne (by decide))]
      exact h29)
    (by
      show S8 (save 4) = _
      simp only [S8, S7, S6, S4, S3, S2, Function.update_of_ne (save_ne_wcell 4 31),
        Function.update_of_ne (save_ne_wcell 4 1),
        Function.update_of_ne (save_ne_wcell 4 6),
        Function.update_of_ne (save_ne_wcell 4 3),
        Function.update_of_ne (save_ne_wcell 4 4),
        Function.update_of_ne (save_ne_wcell 4 30)]
      rw [o1 (save 4) (save_ne_wcell _ _) (save_ne_wcell _ _) (save_ne_wcell _ _)
        (save_ne_wcell _ _)]
      exact hs4)
    (by
      show S8 (save 5) = _
      simp only [S8, S7, S6, S4, S3, S2, Function.update_of_ne (save_ne_wcell 5 31),
        Function.update_of_ne (save_ne_wcell 5 1),
        Function.update_of_ne (save_ne_wcell 5 6),
        Function.update_of_ne (save_ne_wcell 5 3),
        Function.update_of_ne (save_ne_wcell 5 4),
        Function.update_of_ne (save_ne_wcell 5 30)]
      rw [o1 (save 5) (save_ne_wcell _ _) (save_ne_wcell _ _) (save_ne_wcell _ _)
        (save_ne_wcell _ _)]
      exact hs5)
    (by
      show S8 (save 6) = _
      simp only [S8, S7, S6, S4, S3, S2, Function.update_of_ne (save_ne_wcell 6 31),
        Function.update_of_ne (save_ne_wcell 6 1),
        Function.update_of_ne (save_ne_wcell 6 6),
        Function.update_of_ne (save_ne_wcell 6 3),
        Function.update_of_ne (save_ne_wcell 6 4),
        Function.update_of_ne (save_ne_wcell 6 30)]
      rw [o1 (save 6) (save_ne_wcell _ _) (save_ne_wcell _ _) (save_ne_wcell _ _)
        (save_ne_wcell _ _)]
      exact hs6)
    (by
      show S8 (wcell 32) = _
      simp only [S8, S7, S6, S4, S3, S2,
        Function.update_of_ne (wcell_ne (by decide) : wcell 32 ≠ wcell 31),
        Function.update_of_ne (wcell_ne (by decide) : wcell 32 ≠ wcell 1),
        Function.update_of_ne (wcell_ne (by decide) : wcell 32 ≠ wcell 6),
        Function.update_of_ne (wcell_ne (by decide) : wcell 32 ≠ wcell 3),
        Function.update_of_ne (wcell_ne (by decide) : wcell 32 ≠ wcell 4),
        Function.update_of_ne (wcell_ne (by decide) : wcell 32 ≠ wcell 30)]
      rw [o1 (wcell 32) (wcell_ne (by decide)) (wcell_ne (by decide)) (wcell_ne (by decide))
        (wcell_ne (by decide))]
      exact h32)
    (by show S8 (wcell 31) = _; simp only [S8, Function.update_self])
  obtain ⟨t9, ht9, r9⟩ := pw
  -- phase 10: clear writer 30
  have s9_30 : S9 (wcell 30) = List.replicate 182 true := by
    simp only [S9, S8, S7, S6, S4, S3, S2,
      Function.update_of_ne (wcell_ne (by decide) : wcell 30 ≠ wcell 31),
      Function.update_of_ne (wcell_ne (by decide) : wcell 30 ≠ wcell 1),
      Function.update_of_ne (wcell_ne (by decide) : wcell 30 ≠ wcell 6),
      Function.update_of_ne (wcell_ne (by decide) : wcell 30 ≠ wcell 3),
      Function.update_of_ne (wcell_ne (by decide) : wcell 30 ≠ wcell 4),
      Function.update_self]
  have r10 := pop_run S9
  rw [s9_30, List.length_replicate] at r10
  -- sequencing, right to left
  obtain ⟨u10, hu10, q10⟩ := BitMachineRawSequence.runs
    (weightedPowerProgram powSlots) popProgram
    (Sum.inr MatrixWeightedPower.Admin.test) PopLabel.pop
    ((false, false) : MatrixWeightedPower.Control) (false, false)
    ((((), none)) : CC) ((), none) S8 S9 S10 t9 (182 + 2) r9 r10
  obtain ⟨u9, hu9, q9⟩ := BitMachineRawSequence.runs
    (copyProgram copyFuel) seq10 BitMachineCopy.Label.scan start10
    (none : CopyC) none init10 init10 S7 S8 S10 (2 * s + 2) u10 k8 q10
  obtain ⟨u8, hu8, q8⟩ := BitMachineRawSequence.runs
    (constProgram 1 (wcell 1)) seq9 0 start9 () () init9 init9 S6 S7 S10
    (1 + 1) u9 r7 q9
  obtain ⟨u7, hu7, q7⟩ := BitMachineRawSequence.runs
    (copyProgram copy6) seq8 BitMachineCopy.Label.scan start8
    (none : CopyC) none init8 init8 S5 S6 S10 (2 * C + 2) u8 k6' q8
  obtain ⟨u6, hu6, q6⟩ := BitMachineRawSequence.runs
    (copyProgram copy6) seq7 BitMachineCopy.Label.scan start7
    (none : CopyC) none init7 init7 S4 S5 S10 (2 * C + 2) u7 k5' q7
  obtain ⟨u5, hu5, q5⟩ := BitMachineRawSequence.runs
    (multiplyProgram mul3) seq6 MatrixAddressMachine.Label.outer start6
    false false init6 init6 S3 S4 S10
    (MatrixAddressMachine.exactTime C (182 * B) 0) u6 m3 q6
  obtain ⟨u4, hu4, q4⟩ := BitMachineRawSequence.runs
    (multiplyProgram mul4) seq5 MatrixAddressMachine.Label.outer start5
    false false init5 init5 S2 S3 S10
    (MatrixAddressMachine.exactTime 182 B 0) u5 m4 q5
  obtain ⟨u3, hu3, q3⟩ := BitMachineRawSequence.runs
    (constProgram 182 (wcell 30)) seq4 0 start4 () () init4 init4 S1 S2 S10
    (182 + 1) u4 r2 q4
  obtain ⟨u2, hu2, q2⟩ := BitMachineRawSequence.runs
    clearProgram seq3 (ClearLabel.clear 0) start3
    ((((), none)) : CC) ((), none) init3 init3 S S1 S10
    (clearCost4 S) u3 r1 q3
  have hfin : S10 = fieldsBank S B C s := by
    funext k
    simp only [S10, S9, S8, S7, S6, S4, S3, S2, fieldsBank, Function.update_apply]
    by_cases k1 : k = wcell 1
    · subst k1; simp [wcell]
    by_cases k3 : k = wcell 3
    · subst k3; simp [wcell]
    by_cases k4 : k = wcell 4
    · subst k4; simp [wcell]
    by_cases k6 : k = wcell 6
    · subst k6; simp [wcell]
    by_cases k30 : k = wcell 30
    · subst k30; simp [wcell]; exact h30
    by_cases k31 : k = wcell 31
    · subst k31; simp [wcell]; exact h31
    simp only [k1, k3, k4, k6, k30, k31, ↓reduceIte]
    exact cleared4_other S k k1 k3 k4 k6
  refine ⟨u2, ?_, ?_⟩
  · unfold tailCost
    omega
  · rw [← hfin]
    exact q2

#print axioms clear4_run
#print axioms const_run
#print axioms tail_run

end
end EthInapproximability.CurrentPaper.WeightedLevelFields1346
