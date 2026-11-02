import EthInapproximability.CurrentPaper.RoundExitJ
import EthInapproximability.CurrentPaper.WeightedRawWordsHandoff

/-! Lane owner:b-weighted-level-9, unit 2, segment 2d (install): the charged install step between
two rounds, on the round stack `H4 = H2 ⊕ Fin 57`.

ONE fixed program `installProgram` (nine charged pieces, eight charged handoffs), all on `H4`:
copy master `C` into consumer raw cell 0, `B` into 1, `Y` into 2, `E` into 5 (masters kept);
copy fresh cell 0 into consumer raw cell 3 and fresh cell 1 into raw cell 4, then clear fresh
cells 0 and 1 (a MOVE); copy master `Gw` into the consumer parser input cell and push the guard
bit `true` on top of it. Every copy uses the blank temporary fresh cell 56. Cell 55 (the output
word of the previous round, the matrix-source input of the next round's writer 22) is untouched.

`install_run` (generic in the parameter record `i` and the graph code `g`): from any bank
`update (ext4 S D) (.inr 55) out` whose `HStack` part `S` is blank off the master region and whose
masters `C, B, Y, E, Gw` and fresh cells 0, 1 hold the six words of `i` and `encode g`, the run
halts EXACTLY on `ext4 (H0J (bank rawEmb blank (Sum.elim (initialBank i g noW) mS'))) (Dmw out)`
with `mS' a = S (mcell a)`: the admitted consumer start bank of `i` (six raw words and the guarded
graph code, `WeightedRawWords.consumer_chain`), the master region unchanged, cell 55 = `out`, every
other cell blank. `C1j … = bank rawEmb blank (Sum.elim (initialBank (stepParameters …) g noW) mS)`
by definition, so this is the next round's start bank whenever `i` is its parameter record. -/

namespace EthInapproximability.CurrentPaper.RoundInstall

open Turing BitMachineEncoding BitMachineStackEmbedding
open EthInapproximability.ParameterizedNP.GuardedSourceGraph
open WeightedLevel0Rows WeightedLevel0Ready LevelJRows LevelJReady LevelJPrep OuterLevel0Prep
open Level0CostRound Level0DimsRound Level0DimsClean LevelJRound

noncomputable section

set_option maxHeartbeats 8000000
set_option maxRecDepth 8192
set_option synthInstance.maxSize 200000
set_option synthInstance.maxHeartbeats 2000000

/-! ## Cells of `H4` -/

def fH (k : Fin 57) : H4 := .inr k
def consH (x : WeightedRawWords.Cons) : H4 := .inl (.inl (.inl (.inl (.inl x))))
def mH (a : WeightedRawWords.Aux) : H4 := .inl (.inl (mcell a))

theorem consH_inj {x y : WeightedRawWords.Cons} : consH x = consH y ↔ x = y := by
  constructor
  · intro h
    simpa [consH] using h
  · rintro rfl; rfl

theorem mH_inj {a b : WeightedRawWords.Aux} : mH a = mH b ↔ a = b := by
  constructor
  · intro h
    exact mcell_inj (Sum.inl.inj (Sum.inl.inj h))
  · rintro rfl; rfl

theorem fH_inj {k l : Fin 57} : fH k = fH l ↔ k = l := by
  constructor
  · intro h; exact Sum.inr.inj h
  · rintro rfl; rfl

theorem consH_ne_mH (x : WeightedRawWords.Cons) (a : WeightedRawWords.Aux) : consH x ≠ mH a := by
  intro h; cases h
theorem mH_ne_consH (x : WeightedRawWords.Cons) (a : WeightedRawWords.Aux) : mH a ≠ consH x := by
  intro h; cases h
theorem consH_ne_fH (x : WeightedRawWords.Cons) (k : Fin 57) : consH x ≠ fH k := by
  intro h; cases h
theorem fH_ne_consH (x : WeightedRawWords.Cons) (k : Fin 57) : fH k ≠ consH x := by
  intro h; cases h
theorem mH_ne_fH (a : WeightedRawWords.Aux) (k : Fin 57) : mH a ≠ fH k := by
  intro h; cases h
theorem fH_ne_mH (a : WeightedRawWords.Aux) (k : Fin 57) : fH k ≠ mH a := by
  intro h; cases h

theorem consRaw_inj {j k : Fin 6} : WeightedRawWords.consRaw j = WeightedRawWords.consRaw k ↔ j = k := by
  constructor
  · intro h
    have h' : WeightedRawWords.rawCell j = WeightedRawWords.rawCell k := by
      rw [← WeightedRawWords.consRaw_eq, ← WeightedRawWords.consRaw_eq, h]
    exact (WeightedRawWords.rawCell_inj' j k).1 h'
  · rintro rfl; rfl

theorem consRaw_ne_pIn (j : Fin 6) : WeightedRawWords.consRaw j ≠ WeightedRawWords.pInCons := by
  intro h
  apply WeightedRawWords.rawCell_ne_pIn j
  rw [← WeightedRawWords.consRaw_eq]
  show WeightedRawWords.cons (WeightedRawWords.consRaw j) = WeightedRawWords.cons WeightedRawWords.pInCons
  rw [h]

theorem pIn_ne_consRaw (j : Fin 6) : WeightedRawWords.pInCons ≠ WeightedRawWords.consRaw j :=
  (consRaw_ne_pIn j).symm

/-- The simp set deciding equalities between the named install cells. -/
theorem cell_facts : True := trivial

/-! ## The copy pieces -/

def sl (a b : H4) (h1 : a ≠ b) (h2 : a ≠ fH 56) (h3 : b ≠ fH 56) : Fin 3 ↪ H4 where
  toFun
    | 0 => a
    | 1 => b
    | 2 => fH 56
  inj' := by
    intro x y h
    fin_cases x <;> fin_cases y <;> simp_all

def cp (a b : H4) (h1 : a ≠ b) (h2 : a ≠ fH 56) (h3 : b ≠ fH 56) :=
  MatrixStage4ScalarPreparationOps.copyProgram (sl a b h1 h2 h3)

theorem cp_run (a b : H4) (h1 : a ≠ b) (h2 : a ≠ fH 56) (h3 : b ≠ fH 56)
    (S : H4 → List Bool) (hb : S b = []) (ht : S (fH 56) = []) :
    ((advance (cp a b h1 h2 h3))^[2 * (S a).length + 2])
      (⟨some .scan, none, S⟩ : TM2.Cfg (fun _ : H4 => Bool) BitMachineCopy.Label (Option Bool)) =
      ⟨none, none, Function.update S b (S a)⟩ := by
  have h := MatrixStage4ScalarPreparationOps.copy_run (sl a b h1 h2 h3) S ht
  have e0 : (sl a b h1 h2 h3) 0 = a := rfl
  have e1 : (sl a b h1 h2 h3) 1 = b := rfl
  rw [e0, e1, hb, List.append_nil] at h
  exact h

/-- Push `true` on top of the parser input cell (fixed unary push of length 1). -/
theorem push1_run (target : H4) (S : H4 → List Bool) :
    ((advance (SourceClauseFixedUnary.program target 1))^[1 + 1])
      (⟨some (0 : SourceClauseFixedUnary.Label 1), (), S⟩ :
        TM2.Cfg (fun _ : H4 => Bool) (SourceClauseFixedUnary.Label 1) Unit) =
      ⟨none, (), Function.update S target (true :: S target)⟩ := by
  have h := SourceClauseFixedUnary.run_from target S (0 : SourceClauseFixedUnary.Label 1)
    1 (by simp) (S target)
  have hs : SourceClauseFixedUnary.state target S (0 : SourceClauseFixedUnary.Label 1)
      (S target) = ⟨some 0, (), S⟩ := by
    simp [SourceClauseFixedUnary.state]
  rw [hs] at h
  exact h

def r (j : Fin 6) : H4 := consH (WeightedRawWords.consRaw j)
def pH : H4 := consH WeightedRawWords.pInCons

theorem r_ne_t (j : Fin 6) : r j ≠ fH 56 := consH_ne_fH _ _
theorem m_ne_t (a : WeightedRawWords.Aux) : mH a ≠ fH 56 := mH_ne_fH _ _
theorem m_ne_r (a : WeightedRawWords.Aux) (j : Fin 6) : mH a ≠ r j := mH_ne_consH _ _
theorem f_ne_r (k : Fin 57) (j : Fin 6) : fH k ≠ r j := fH_ne_consH _ _
theorem f_ne_t (k : Fin 57) (hk : k ≠ 56) : fH k ≠ fH 56 := fun h => hk (fH_inj.1 h)

def cpC := cp (mH .C) (r 0) (m_ne_r _ _) (m_ne_t _) (r_ne_t _)
def cpB := cp (mH .B) (r 1) (m_ne_r _ _) (m_ne_t _) (r_ne_t _)
def cpY := cp (mH .Y) (r 2) (m_ne_r _ _) (m_ne_t _) (r_ne_t _)
def cpE := cp (mH .E) (r 5) (m_ne_r _ _) (m_ne_t _) (r_ne_t _)
def cp3 := cp (fH 0) (r 3) (f_ne_r _ _) (f_ne_t 0 (by decide)) (r_ne_t _)
def cp4 := cp (fH 1) (r 4) (f_ne_r _ _) (f_ne_t 1 (by decide)) (r_ne_t _)
def cells01 : Fin 2 → H4 := ![fH 0, fH 1]
theorem cells01_inj : Function.Injective cells01 := by
  intro a b h
  fin_cases a <;> fin_cases b <;> simp_all [cells01, fH]
def clr01 := WeightedRawWords.clearProgram cells01
def cpG := cp (mH .Gw) pH (mH_ne_consH _ _) (m_ne_t _) (consH_ne_fH _ _)
def push1 := SourceClauseFixedUnary.program pH 1

def P8 := BitMachineRawSequence.program cpG push1 (0 : SourceClauseFixedUnary.Label 1) none ()
def P7 := BitMachineRawSequence.program clr01 P8
  (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan) ((), none) (none, ())
def P6 := BitMachineRawSequence.program cp4 P7
  (BitMachineRawSequence.leftLabel (0 : Fin (2 + 2))) none (((), none), (none, ()))
def P5 := BitMachineRawSequence.program cp3 P6
  (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan) none (none, (((), none), (none, ())))
def P4 := BitMachineRawSequence.program cpE P5
  (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan) none
  (none, (none, (((), none), (none, ()))))
def P3 := BitMachineRawSequence.program cpY P4
  (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan) none
  (none, (none, (none, (((), none), (none, ())))))
def P2 := BitMachineRawSequence.program cpB P3
  (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan) none
  (none, (none, (none, (none, (((), none), (none, ()))))))
/-- ONE fixed install program. -/
def installProgram := BitMachineRawSequence.program cpC P2
  (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan) none
  (none, (none, (none, (none, (none, (((), none), (none, ())))))))

/-- Its (constant) control. -/
abbrev installCtrl :=
  ((none : Option Bool), ((none : Option Bool), ((none : Option Bool), ((none : Option Bool),
    ((none : Option Bool), ((none : Option Bool), (((), (none : Option Bool)), ((none : Option Bool), ()))))))))

/-! ## The target bank -/

/-- The next round's start bank: consumer region `f`, master region `m`, fresh region `D`. -/
def tgt (f : WeightedRawWords.Cons → List Bool) (m : WeightedRawWords.Aux → List Bool)
    (D : Fin 57 → List Bool) : H4 → List Bool :=
  ext4 (H0J (bank rawEmb (fun _ => []) (Sum.elim f m))) D

theorem tgt_cons (f m D) (x : WeightedRawWords.Cons) : tgt f m D (consH x) = f x := by
  show bank rawEmb (fun _ => []) (Sum.elim f m) (rawEmb (Sum.inl x)) = f x
  rw [bank_at]
  rfl

theorem tgt_master (f m D) (a : WeightedRawWords.Aux) : tgt f m D (mH a) = m a := by
  show bank rawEmb (fun _ => []) (Sum.elim f m) (rawEmb (Sum.inr a)) = m a
  rw [bank_at]
  rfl

theorem tgt_fresh (f m D) (k : Fin 57) : tgt f m D (fH k) = D k := rfl

/-- Off the consumer and master cells, the target is blank on `HStack`. -/
theorem tgt_other (f m D) (h : HStack) (hc : ∀ x, h ≠ .inl (.inl (.inl x)))
    (hm : ∀ a, h ≠ mcell a) : tgt f m D (.inl (.inl h)) = [] := by
  rcases h with (x | g) | o
  · show bank rawEmb (fun _ => []) (Sum.elim f m) x = []
    rw [bank_outside]
    rintro ⟨k, hk⟩
    rcases k with k | a
    · exact hc k (by rw [← hk]; rfl)
    · exact hm a (by rw [← hk]; rfl)
  · rfl
  · rfl

/-! ## The install run -/

abbrev W6 (i : Parameters.Input) := ETHParameterScaleMachineInput.words i

theorem install_run (i : Parameters.Input) (g : EncodedGraph.Graph)
    (S : HStack → List Bool) (D : Fin 57 → List Bool) (out : List Bool)
    (hS : ∀ x, (∀ a, x ≠ mcell a) → S x = [])
    (hC : S (mcell .C) = W6 i 0) (hB : S (mcell .B) = W6 i 1) (hY : S (mcell .Y) = W6 i 2)
    (hE : S (mcell .E) = W6 i 5) (hG : S (mcell .Gw) = EncodedGraph.encode g)
    (hD0 : D 0 = W6 i 3) (hD1 : D 1 = W6 i 4) (hD : ∀ k, k ≠ 0 → k ≠ 1 → D k = []) :
    ∃ t ≤ 2 * (W6 i 0).length + 2 * (W6 i 1).length + 2 * (W6 i 2).length +
        2 * (W6 i 5).length + 3 * (W6 i 3).length + 3 * (W6 i 4).length +
        2 * (EncodedGraph.encode g).length + 30,
      ((advance installProgram)^[t])
        (⟨some (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan), installCtrl,
          Function.update (ext4 S D) (fH 55) out⟩ :
          TM2.Cfg (fun _ : H4 => Bool) _ _) =
        ⟨none, installCtrl,
          tgt (WeightedRawRowsSource.initialBank i g WeightedRawWords.noW) (fun a => S (mcell a))
            (Dmw out)⟩ := by
  set X0 : H4 → List Bool := Function.update (ext4 S D) (fH 55) out with hX0
  have x0m : ∀ a, X0 (mH a) = S (mcell a) := fun a => by
    rw [hX0, Function.update_of_ne (mH_ne_fH _ _)]; rfl
  have x0c : ∀ x, X0 (consH x) = [] := fun x => by
    rw [hX0, Function.update_of_ne (consH_ne_fH _ _)]
    exact hS _ (fun a h => by cases h)
  have x0f : ∀ k, k ≠ 55 → X0 (fH k) = D k := fun k hk => by
    rw [hX0, Function.update_of_ne (fun h => hk (fH_inj.1 h))]; rfl
  have x0t : X0 (fH 56) = [] := by rw [x0f 56 (by decide)]; exact hD 56 (by decide) (by decide)
  -- 1. C → r0
  have s1 := cp_run (mH .C) (r 0) (m_ne_r _ _) (m_ne_t _) (r_ne_t _) X0 (x0c _) x0t
  rw [x0m, hC] at s1
  set X1 := Function.update X0 (r 0) (W6 i 0) with hX1
  have x1 : ∀ y, y ≠ r 0 → X1 y = X0 y := fun y hy => Function.update_of_ne hy _ _
  -- 2. B → r1
  have s2 := cp_run (mH .B) (r 1) (m_ne_r _ _) (m_ne_t _) (r_ne_t _) X1
    (by rw [x1 _ (by simp [r, consH_inj, consRaw_inj])]; exact x0c _)
    (by rw [x1 _ (f_ne_r _ _)]; exact x0t)
  rw [x1 _ (m_ne_r _ _), x0m, hB] at s2
  set X2 := Function.update X1 (r 1) (W6 i 1) with hX2
  have x2 : ∀ y, y ≠ r 1 → X2 y = X1 y := fun y hy => Function.update_of_ne hy _ _
  -- 3. Y → r2
  have s3 := cp_run (mH .Y) (r 2) (m_ne_r _ _) (m_ne_t _) (r_ne_t _) X2
    (by rw [x2 _ (by simp [r, consH_inj, consRaw_inj]), x1 _ (by simp [r, consH_inj, consRaw_inj])]
        exact x0c _)
    (by rw [x2 _ (f_ne_r _ _), x1 _ (f_ne_r _ _)]; exact x0t)
  rw [x2 _ (m_ne_r _ _), x1 _ (m_ne_r _ _), x0m, hY] at s3
  set X3 := Function.update X2 (r 2) (W6 i 2) with hX3
  have x3 : ∀ y, y ≠ r 2 → X3 y = X2 y := fun y hy => Function.update_of_ne hy _ _
  -- 4. E → r5
  have s4 := cp_run (mH .E) (r 5) (m_ne_r _ _) (m_ne_t _) (r_ne_t _) X3
    (by rw [x3 _ (by simp [r, consH_inj, consRaw_inj]), x2 _ (by simp [r, consH_inj, consRaw_inj]),
          x1 _ (by simp [r, consH_inj, consRaw_inj])]
        exact x0c _)
    (by rw [x3 _ (f_ne_r _ _), x2 _ (f_ne_r _ _), x1 _ (f_ne_r _ _)]; exact x0t)
  rw [x3 _ (m_ne_r _ _), x2 _ (m_ne_r _ _), x1 _ (m_ne_r _ _), x0m, hE] at s4
  set X4 := Function.update X3 (r 5) (W6 i 5) with hX4
  have x4 : ∀ y, y ≠ r 5 → X4 y = X3 y := fun y hy => Function.update_of_ne hy _ _
  have x4f : ∀ k, X4 (fH k) = X0 (fH k) := fun k => by
    rw [x4 _ (f_ne_r _ _), x3 _ (f_ne_r _ _), x2 _ (f_ne_r _ _), x1 _ (f_ne_r _ _)]
  -- 5. fresh 0 → r3
  have s5 := cp_run (fH 0) (r 3) (f_ne_r _ _) (f_ne_t 0 (by decide)) (r_ne_t _) X4
    (by rw [x4 _ (by simp [r, consH_inj, consRaw_inj]), x3 _ (by simp [r, consH_inj, consRaw_inj]),
          x2 _ (by simp [r, consH_inj, consRaw_inj]), x1 _ (by simp [r, consH_inj, consRaw_inj])]
        exact x0c _)
    (by rw [x4f]; exact x0t)
  rw [x4f, x0f 0 (by decide), hD0] at s5
  set X5 := Function.update X4 (r 3) (W6 i 3) with hX5
  have x5 : ∀ y, y ≠ r 3 → X5 y = X4 y := fun y hy => Function.update_of_ne hy _ _
  -- 6. fresh 1 → r4
  have s6 := cp_run (fH 1) (r 4) (f_ne_r _ _) (f_ne_t 1 (by decide)) (r_ne_t _) X5
    (by rw [x5 _ (by simp [r, consH_inj, consRaw_inj]), x4 _ (by simp [r, consH_inj, consRaw_inj]),
          x3 _ (by simp [r, consH_inj, consRaw_inj]), x2 _ (by simp [r, consH_inj, consRaw_inj]),
          x1 _ (by simp [r, consH_inj, consRaw_inj])]
        exact x0c _)
    (by rw [x5 _ (f_ne_r _ _), x4f]; exact x0t)
  rw [x5 _ (f_ne_r _ _), x4f, x0f 1 (by decide), hD1] at s6
  set X6 := Function.update X5 (r 4) (W6 i 4) with hX6
  have x6f : ∀ k, X6 (fH k) = X0 (fH k) := fun k => by
    rw [hX6, Function.update_of_ne (f_ne_r _ _), x5 _ (f_ne_r _ _), x4f]
  -- 7. clear fresh 0, 1
  have s7 := WeightedRawWords.clear_run cells01 cells01_inj X6
  have hsum : (∑ k : Fin 2, (X6 (cells01 k)).length) = (W6 i 3).length + (W6 i 4).length := by
    rw [Fin.sum_univ_two]
    show (X6 (fH 0)).length + (X6 (fH 1)).length = _
    rw [x6f, x6f, x0f 0 (by decide), x0f 1 (by decide), hD0, hD1]
  rw [hsum] at s7
  set X7 := BitMachineClearBank.cleared cells01 X6 with hX7
  have x7 : ∀ y, (∀ k, cells01 k ≠ y) → X7 y = X6 y := fun y hy => by
    rw [hX7]; unfold BitMachineClearBank.cleared
    rw [if_neg (fun ⟨k, hk⟩ => hy k hk)]
  have x7f : ∀ k : Fin 2, X7 (cells01 k) = [] := fun k => by
    rw [hX7]; unfold BitMachineClearBank.cleared
    rw [if_pos ⟨k, rfl⟩]
  have c01 : ∀ (x : WeightedRawWords.Cons) (k : Fin 2), cells01 k ≠ consH x := by
    intro x k; fin_cases k <;> exact fH_ne_consH _ _
  have c01m : ∀ (a : WeightedRawWords.Aux) (k : Fin 2), cells01 k ≠ mH a := by
    intro a k; fin_cases k <;> exact fH_ne_mH _ _
  -- 8. Gw → pIn
  have hpr : ∀ j, pH ≠ r j := fun j => by simp [pH, r, consH_inj, pIn_ne_consRaw]
  have x7p : X7 pH = [] := by
    show X7 (consH WeightedRawWords.pInCons) = []
    rw [x7 _ (c01 WeightedRawWords.pInCons)]
    show X6 pH = []
    rw [hX6, Function.update_of_ne (hpr 4), x5 _ (hpr 3), x4 _ (hpr 5),
      x3 _ (hpr 2), x2 _ (hpr 1), x1 _ (hpr 0)]
    exact x0c _
  have x7t : X7 (fH 56) = [] := by
    rw [x7 _ (by intro k; fin_cases k <;> simp [cells01, fH]), x6f]; exact x0t
  have s8 := cp_run (mH .Gw) pH (mH_ne_consH _ _) (m_ne_t _) (consH_ne_fH _ _) X7 x7p x7t
  have x7G : X7 (mH .Gw) = EncodedGraph.encode g := by
    rw [x7 _ (c01m _), hX6, Function.update_of_ne (m_ne_r _ _), x5 _ (m_ne_r _ _),
      x4 _ (m_ne_r _ _), x3 _ (m_ne_r _ _), x2 _ (m_ne_r _ _), x1 _ (m_ne_r _ _), x0m, hG]
  rw [x7G] at s8
  set X8 := Function.update X7 pH (EncodedGraph.encode g) with hX8
  -- 9. push the guard bit
  have s9 := push1_run pH X8
  rw [hX8, Function.update_self, Function.update_idem] at s9
  -- compose
  obtain ⟨u8, hu8, q8⟩ := BitMachineRawSequence.runs cpG push1 BitMachineCopy.Label.scan
    (0 : SourceClauseFixedUnary.Label 1) none none () () X7 _ _ _ _ s8 s9
  obtain ⟨u7, hu7, q7⟩ := BitMachineRawSequence.runs clr01 P8 (0 : Fin (2 + 2))
    (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan) ((), none) ((), none)
    (none, ()) (none, ()) X6 X7 _ _ _ s7 q8
  obtain ⟨u6, hu6, q6⟩ := BitMachineRawSequence.runs cp4 P7 BitMachineCopy.Label.scan
    _ none none _ _ X5 X6 _ _ _ s6 q7
  obtain ⟨u5, hu5, q5⟩ := BitMachineRawSequence.runs cp3 P6 BitMachineCopy.Label.scan
    _ none none _ _ X4 X5 _ _ _ s5 q6
  obtain ⟨u4, hu4, q4⟩ := BitMachineRawSequence.runs cpE P5 BitMachineCopy.Label.scan
    _ none none _ _ X3 X4 _ _ _ s4 q5
  obtain ⟨u3, hu3, q3⟩ := BitMachineRawSequence.runs cpY P4 BitMachineCopy.Label.scan
    _ none none _ _ X2 X3 _ _ _ s3 q4
  obtain ⟨u2, hu2, q2⟩ := BitMachineRawSequence.runs cpB P3 BitMachineCopy.Label.scan
    _ none none _ _ X1 X2 _ _ _ s2 q3
  obtain ⟨u1, hu1, q1⟩ := BitMachineRawSequence.runs cpC P2 BitMachineCopy.Label.scan
    _ none none _ _ X0 X1 _ _ _ s1 q2
  have tr : ∀ k, tgt (WeightedRawRowsSource.initialBank i g WeightedRawWords.noW)
      (fun a => S (mcell a)) (Dmw out) (r k) = W6 i k := by
    intro k
    rw [r, tgt_cons, WeightedRawWords.consumer_chain]
    fin_cases k <;> simp [Function.update_apply, consRaw_inj, consRaw_ne_pIn]
  have hfin : ∀ y, y ≠ pH → X7 y = tgt (WeightedRawRowsSource.initialBank i g WeightedRawWords.noW)
      (fun a => S (mcell a)) (Dmw out) y := by
    intro y hyp
    by_cases hf0 : y = fH 0
    · subst hf0
      rw [show fH 0 = cells01 0 from rfl, x7f, show cells01 0 = fH 0 from rfl, tgt_fresh,
        Dmw_other out 0 (by decide)]
    by_cases hf1 : y = fH 1
    · subst hf1
      rw [show fH 1 = cells01 1 from rfl, x7f, show cells01 1 = fH 1 from rfl, tgt_fresh,
        Dmw_other out 1 (by decide)]
    rw [x7 _ (by
      intro k; fin_cases k
      · exact fun h => hf0 h.symm
      · exact fun h => hf1 h.symm)]
    simp only [hX6, hX5, hX4, hX3, hX2, hX1, Function.update_apply]
    split_ifs with e4 e3 e5 e2 e1 e0
    · rw [e4, tr]
    · rw [e3, tr]
    · rw [e5, tr]
    · rw [e2, tr]
    · rw [e1, tr]
    · rw [e0, tr]
    rw [hX0]
    by_cases h55 : y = fH 55
    · rw [h55, Function.update_self, tgt_fresh]
      unfold Dmw
      rw [Function.update_self]
    rw [Function.update_of_ne h55]
    rcases y with (h | l) | k
    · show S h = _
      by_cases hm : ∃ a, h = mcell a
      · obtain ⟨a, rfl⟩ := hm
        exact (tgt_master (WeightedRawRowsSource.initialBank i g WeightedRawWords.noW)
          (fun a => S (mcell a)) (Dmw out) a).symm
      · push Not at hm
        rw [hS h hm]
        by_cases hc : ∃ x, h = .inl (.inl (.inl x))
        · obtain ⟨x, rfl⟩ := hc
          rw [show (Sum.inl (Sum.inl (Sum.inl (Sum.inl (Sum.inl x)))) : H4) = consH x from rfl,
            tgt_cons, WeightedRawWords.consumer_chain]
          have hx : x ≠ WeightedRawWords.pInCons := fun e => hyp (by rw [e]; rfl)
          have hxk : ∀ k, x ≠ WeightedRawWords.consRaw k := by
            intro k e
            fin_cases k
            · exact e0 (by rw [e]; rfl)
            · exact e1 (by rw [e]; rfl)
            · exact e2 (by rw [e]; rfl)
            · exact e3 (by rw [e]; rfl)
            · exact e4 (by rw [e]; rfl)
            · exact e5 (by rw [e]; rfl)
          simp [Function.update_apply, hx, hxk]
        · push Not at hc
          exact (tgt_other _ _ _ h hc hm).symm
    · rfl
    · show D k = Dmw out k
      have k0 : k ≠ 0 := fun e => hf0 (by rw [e]; rfl)
      have k1 : k ≠ 1 := fun e => hf1 (by rw [e]; rfl)
      have k55 : k ≠ 55 := fun e => h55 (by rw [e]; rfl)
      rw [hD k k0 k1, Dmw_other out k k55]
  refine ⟨u1, by omega, q1.trans ?_⟩
  congr 1
  funext y
  by_cases hyp : y = pH
  · rw [hyp, Function.update_self, pH, tgt_cons, WeightedRawWords.consumer_chain]
    simp [Function.update_apply, pIn_ne_consRaw]
  · rw [Function.update_of_ne hyp]
    exact hfin y hyp

#print axioms install_run

end
end EthInapproximability.CurrentPaper.RoundInstall
