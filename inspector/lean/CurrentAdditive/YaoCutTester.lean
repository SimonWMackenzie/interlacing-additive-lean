import EthInapproximability.CurrentPaper.MatrixStage4ScalarPreparationOps
import EthInapproximability.CurrentPaper.EntryUnaryCompare
import EthInapproximability.CurrentPaper.SourceClauseFixedUnary
import EthInapproximability.CurrentPaper.WeightedRawWordsCore
import EthInapproximability.CurrentPaper.BitMachineRawSequence
import CurrentAdditive.SmallBiasStopping

/-!
Physical public cut test from v27 `yao:bias-parameters`.
The ambient bank is Fin 16. Banks 0..6 are untouched, with candidate j in 4,
scan fuel in 5, and threshold R in 6. Bank 12 receives the verdict. All
other work banks are empty at the input and output.
-/

noncomputable section

namespace CurrentAdditive.SmallBias.YaoCutTester

open Turing EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding

abbrev Bank := Fin 16
def unary (n : ℕ) : List Bool := List.replicate n true

def copyJPower : Fin 3 ↪ Bank := ⟨![4,7,15], by decide⟩
def copyJSum : Fin 3 ↪ Bank := ⟨![4,11,15], by decide⟩
def copyR : Fin 3 ↪ Bank := ⟨![6,9,15], by decide⟩
def powerPlace : MatrixUnaryPower.Stack ↪ Bank :=
  ⟨fun k => match k with
    | .inl 0 => 8
    | .inl 1 => 9
    | .inl 2 => 10
    | .inr () => 7, by decide⟩
def mulPlace : Fin 6 ↪ Bank := ⟨![8,11,9,10,14,13], by decide⟩
def clearCells : Fin 3 → Bank := ![7,8,11]

def p1 := MatrixStage4ScalarPreparationOps.copyProgram copyJPower
def p2 (t : ℕ) := SourceClauseFixedUnary.program (11 : Bank) (t-2)
def p3 := MatrixStage4ScalarPreparationOps.copyProgram copyJSum
def p4 := MatrixStage4ScalarPreparationOps.unaryPowerProgram powerPlace
def p5 := MatrixStage4ScalarPreparationOps.multiplyProgram mulPlace
def p6 := MatrixStage4ScalarPreparationOps.copyProgram copyR
def p7 := EntryUnaryCompare.program (13 : Bank) 9 12 true true false
def p8 := WeightedRawWords.clearProgram clearCells

def q7 := BitMachineRawSequence.program p7 p8 (0 : Fin 5)
  ((none, none) : EntryUnaryCompare.CV) ((), none)
def q6 := BitMachineRawSequence.program p6 q7
  (BitMachineRawSequence.leftLabel EntryUnaryCompare.CL.loop)
  (none : Option Bool) (((none, none) : EntryUnaryCompare.CV), ((), none))
def q5 := BitMachineRawSequence.program p5 q6
  (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)
  false (none, (((none, none) : EntryUnaryCompare.CV), ((), none)))
def q4 := BitMachineRawSequence.program p4 q5
  (BitMachineRawSequence.leftLabel MatrixAddressMachine.Label.outer)
  ((false,false), none) (false, (none, (((none, none) : EntryUnaryCompare.CV), ((), none))))
def q3 := BitMachineRawSequence.program p3 q4
  (BitMachineRawSequence.leftLabel (.inr false : MatrixUnaryPower.Label))
  (none : Option Bool)
  (((false,false), none), (false, (none, (((none, none) : EntryUnaryCompare.CV), ((), none)))))
def q2 (t : ℕ) := BitMachineRawSequence.program (p2 t) q3
  (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)
  () (none, (((false,false), none), (false, (none, (((none, none) : EntryUnaryCompare.CV), ((), none))))))
def program (t : ℕ) := BitMachineRawSequence.program p1 (q2 t)
  (BitMachineRawSequence.leftLabel (0 : SourceClauseFixedUnary.Label (t-2)))
  (none : Option Bool)
  ((), (none, (((false,false), none), (false, (none, (((none, none) : EntryUnaryCompare.CV), ((), none)))))))

def S1 (S : Bank → List Bool) (j : ℕ) := Function.update S 7 (unary j)
def S2 (S : Bank → List Bool) (j t : ℕ) := Function.update (S1 S j) 11 (unary (t-2))
def S3 (S : Bank → List Bool) (j t : ℕ) := Function.update (S2 S j t) 11 (unary (t+j-2))
def S4 (S : Bank → List Bool) (j t : ℕ) := Function.update (S3 S j t) 8 (unary (2^j))
def S5 (S : Bank → List Bool) (j t : ℕ) :=
  Function.update (S4 S j t) 13 (unary (2^j*(t+j-2)))
def S6 (S : Bank → List Bool) (j t R : ℕ) :=
  Function.update (S5 S j t) 9 (unary R)
def S7 (S : Bank → List Bool) (j t R : ℕ) :=
  Function.update (Function.update (Function.update (S6 S j t R) 13 []) 9 [])
    12 [decide (2^j*(t+j-2) ≤ R)]
def finalBank (S : Bank → List Bool) (j t R : ℕ) :=
  Function.update S 12 [decide (2^j*(t+j-2) ≤ R)]

theorem stage1 (S : Bank → List Bool) (j : ℕ)
    (hj : S 4 = unary j) (h7 : S 7 = []) (h15 : S 15 = []) :
    ((advance p1)^[2*j+2])
      (⟨some BitMachineCopy.Label.scan, none, S⟩ : TM2.Cfg (fun _ : Bank => Bool) _ _) =
      ⟨none, none, S1 S j⟩ := by
  have h := MatrixStage4ScalarPreparationOps.copy_run copyJPower S h15
  simpa [p1, copyJPower, S1, hj, h7, unary] using h

theorem stage2 (S : Bank → List Bool) (j t : ℕ)
    (h11 : S 11 = []) :
    ((advance (p2 t))^[(t-2)+1])
      (⟨some (0 : SourceClauseFixedUnary.Label (t-2)), (), S1 S j⟩ :
        TM2.Cfg (fun _ : Bank => Bool) _ _) =
      ⟨none, (), S2 S j t⟩ := by
  have h := SourceClauseFixedUnary.run (11 : Bank) (S1 S j) (t-2)
    (by simp [S1, h11])
  simpa [p2, S2, unary] using h

theorem stage3 (S : Bank → List Bool) (j t : ℕ) (ht : 4 ≤ t)
    (hj : S 4 = unary j) (h15 : S 15 = []) :
    ((advance p3)^[2*j+2])
      (⟨some BitMachineCopy.Label.scan, none, S2 S j t⟩ :
        TM2.Cfg (fun _ : Bank => Bool) _ _) =
      ⟨none, none, S3 S j t⟩ := by
  have h := MatrixStage4ScalarPreparationOps.copy_run copyJSum (S2 S j t)
    (by simp [S2, S1, copyJSum, h15])
  have hnum : j+(t-2) = t+j-2 := by omega
  simpa [p3, copyJSum, S3, S2, S1, hj, unary, hnum,
    List.replicate_append_replicate] using h

theorem stage4 (S : Bank → List Bool) (j t : ℕ)
    (h8 : S 8 = []) (h9 : S 9 = []) (h10 : S 10 = []) :
    ∃ u ≤ 4*2^j+5*j+7,
      ((advance p4)^[u])
        (⟨some (.inr false : MatrixUnaryPower.Label), ((false,false),none), S3 S j t⟩ :
          TM2.Cfg (fun _ : Bank => Bool) _ _) =
        ⟨none, ((false,false),none), S4 S j t⟩ := by
  have h := MatrixStage4ScalarPreparationOps.unary_power_run powerPlace
    (S3 S j t) j (by simp [S3, S2, S1, powerPlace, unary])
    (by simp [S3, S2, S1, powerPlace, h8])
    (by simp [S3, S2, S1, powerPlace, h9])
    (by simp [S3, S2, S1, powerPlace, h10])
  simpa [p4, powerPlace, S4, unary] using h

theorem stage5 (S : Bank → List Bool) (j t : ℕ)
    (h9 : S 9 = []) (h10 : S 10 = []) (h13 : S 13 = [])
    (h14 : S 14 = []) :
    ((advance p5)^[MatrixAddressMachine.exactTime (2^j) (t+j-2) 0])
      (⟨some MatrixAddressMachine.Label.outer, false, S4 S j t⟩ :
        TM2.Cfg (fun _ : Bank => Bool) _ _) =
      ⟨none, false, S5 S j t⟩ := by
  have h := MatrixStage4ScalarPreparationOps.multiply_run mulPlace (S4 S j t)
    (2^j) (t+j-2) (by simp [mulPlace, S4, unary])
    (by simp [mulPlace, S4, S3, unary])
    (by simp [mulPlace, S4, S3, S2, S1, h9])
    (by simp [mulPlace, S4, S3, S2, S1, h10])
    (by simp [mulPlace, S4, S3, S2, S1, h14])
  simpa [p5, mulPlace, S5, S4, S3, S2, S1, unary, h13] using h

theorem stage6 (S : Bank → List Bool) (j t R : ℕ)
    (hR : S 6 = unary R) (h9 : S 9 = []) (h15 : S 15 = []) :
    ((advance p6)^[2*R+2])
      (⟨some BitMachineCopy.Label.scan, none, S5 S j t⟩ :
        TM2.Cfg (fun _ : Bank => Bool) _ _) =
      ⟨none, none, S6 S j t R⟩ := by
  have h := MatrixStage4ScalarPreparationOps.copy_run copyR (S5 S j t)
    (by simp [S5, S4, S3, S2, S1, copyR, h15])
  simpa [p6, copyR, S6, S5, S4, S3, S2, S1, hR, h9, unary] using h

theorem verdict_le (p R : ℕ) :
    EntryUnaryCompare.verdict true true false p R = decide (p ≤ R) := by
  unfold EntryUnaryCompare.verdict
  by_cases hlt : p < R <;> by_cases heq : p = R <;> simp_all <;> omega

theorem stage7 (S : Bank → List Bool) (j t R : ℕ)
    (h12 : S 12 = []) :
    ∃ u ≤ max (2^j*(t+j-2)) R + 2, ∃ w,
      ((advance p7)^[u])
        (⟨some EntryUnaryCompare.CL.loop, (none, none), S6 S j t R⟩ :
          TM2.Cfg (fun _ : Bank => Bool) _ _) =
        ⟨none, w, S7 S j t R⟩ := by
  have h := EntryUnaryCompare.compare_run (13 : Bank) 9 12
    (by decide) (by decide) (by decide) true true false
    (S6 S j t R) (none, none) (2^j*(t+j-2)) R
    (by simp [S6, S5, unary]) (by simp [S6, unary])
  simpa [p7, S7, S6, S5, S4, S3, S2, S1, h12, verdict_le] using h

theorem stage8 (S : Bank → List Bool) (j t R : ℕ)
    (h7 : S 7 = []) (h8 : S 8 = []) (h9 : S 9 = [])
    (h10 : S 10 = []) (h11 : S 11 = []) (h13 : S 13 = [])
    (h14 : S 14 = []) (h15 : S 15 = []) :
    ((advance p8)^[(j + 2^j + (t+j-2)) + 5])
      (⟨some (0 : Fin 5), ((), none), S7 S j t R⟩ :
        TM2.Cfg (fun _ : Bank => Bool) _ _) =
      ⟨none, ((), none), finalBank S j t R⟩ := by
  have h := WeightedRawWords.clear_run clearCells (by decide) (S7 S j t R)
  have htime : (∑ i : Fin 3, ((S7 S j t R) (clearCells i)).length) + 3 + 2 =
      (j + 2^j + (t+j-2)) + 5 := by
    simp [Fin.sum_univ_succ, S7, S6, S5, S4, S3, S2, S1, clearCells, unary]
    omega
  rw [htime] at h
  have hbank : BitMachineClearBank.cleared clearCells (S7 S j t R) =
      finalBank S j t R := by
    have hx (k : Bank) : (∃ i : Fin 3, clearCells i = k) ↔
        k = 7 ∨ k = 8 ∨ k = 11 := by
      fin_cases k <;> decide
    funext k
    change (if ∃ i : Fin 3, clearCells i = k then [] else S7 S j t R k) =
      finalBank S j t R k
    simp only [hx k]
    fin_cases k <;> simp [finalBank, S7, S6, S5, S4, S3, S2, S1,
      h7, h8, h9, h10, h11, h13, h14, h15]
  simpa [p8, hbank] using h

abbrev v7 : EntryUnaryCompare.CV × (Unit × Option Bool) :=
  ((none, none), ((), none))
abbrev v6 : Option Bool × (EntryUnaryCompare.CV × (Unit × Option Bool)) :=
  (none, v7)
abbrev v5 : Bool × (Option Bool × (EntryUnaryCompare.CV × (Unit × Option Bool))) :=
  (false, v6)
abbrev v4 : MatrixUnaryPower.Control ×
    (Bool × (Option Bool × (EntryUnaryCompare.CV × (Unit × Option Bool)))) :=
  (((false,false),none), v5)
abbrev v3 : Option Bool ×
    (MatrixUnaryPower.Control ×
      (Bool × (Option Bool × (EntryUnaryCompare.CV × (Unit × Option Bool))))) :=
  (none, v4)
abbrev v2 : Unit ×
    (Option Bool ×
      (MatrixUnaryPower.Control ×
        (Bool × (Option Bool × (EntryUnaryCompare.CV × (Unit × Option Bool)))))) :=
  ((), v3)
abbrev v1 : Option Bool ×
    (Unit ×
      (Option Bool ×
        (MatrixUnaryPower.Control ×
          (Bool × (Option Bool × (EntryUnaryCompare.CV × (Unit × Option Bool))))))) :=
  (none, v2)

theorem q7_run (S : Bank → List Bool) (j t R : ℕ)
    (h7 : S 7 = []) (h8 : S 8 = []) (h9 : S 9 = [])
    (h10 : S 10 = []) (h11 : S 11 = []) (h12 : S 12 = [])
    (h13 : S 13 = []) (h14 : S 14 = []) (h15 : S 15 = []) :
    ∃ u ≤ (max (2^j*(t+j-2)) R + 2) +
        (j + 2^j + (t+j-2) + 5) + 1,
      ((advance q7)^[u])
        (⟨some (BitMachineRawSequence.leftLabel EntryUnaryCompare.CL.loop),
          v7, S6 S j t R⟩ : TM2.Cfg (fun _ : Bank => Bool) _ _) =
        ⟨none, v7, finalBank S j t R⟩ := by
  obtain ⟨u, hu, w, hcmp⟩ := stage7 S j t R h12
  have hclr := stage8 S j t R h7 h8 h9 h10 h11 h13 h14 h15
  obtain ⟨steps, hsteps, hrun⟩ := BitMachineRawSequence.runs
    p7 p8 EntryUnaryCompare.CL.loop (0 : Fin 5)
    ((none, none) : EntryUnaryCompare.CV) w ((), none) ((), none)
    (S6 S j t R) (S7 S j t R) (finalBank S j t R)
    u (j + 2^j + (t+j-2) + 5) hcmp hclr
  exact ⟨steps, by omega, by simpa [q7, v7] using hrun⟩

theorem q6_run (S : Bank → List Bool) (j t R : ℕ)
    (hR : S 6 = unary R)
    (h7 : S 7 = []) (h8 : S 8 = []) (h9 : S 9 = [])
    (h10 : S 10 = []) (h11 : S 11 = []) (h12 : S 12 = [])
    (h13 : S 13 = []) (h14 : S 14 = []) (h15 : S 15 = []) :
    ∃ u ≤ (2*R+2) + (max (2^j*(t+j-2)) R + 2) +
        (j + 2^j + (t+j-2) + 5) + 2,
      ((advance q6)^[u])
        (⟨some (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan),
          v6, S5 S j t⟩ : TM2.Cfg (fun _ : Bank => Bool) _ _) =
        ⟨none, v6, finalBank S j t R⟩ := by
  have hc := stage6 S j t R hR h9 h15
  obtain ⟨u, hu, hr⟩ := q7_run S j t R h7 h8 h9 h10 h11 h12 h13 h14 h15
  obtain ⟨steps, hsteps, hrun⟩ := BitMachineRawSequence.runs
    p6 q7 BitMachineCopy.Label.scan
    (BitMachineRawSequence.leftLabel EntryUnaryCompare.CL.loop)
    (none : Option Bool) none v7 v7
    (S5 S j t) (S6 S j t R) (finalBank S j t R)
    (2*R+2) u hc hr
  exact ⟨steps, by omega, by simpa [q6, v6] using hrun⟩

def B7 (j t R : ℕ) := (max (2^j*(t+j-2)) R + 2) +
  (j + 2^j + (t+j-2) + 5) + 1
def B6 (j t R : ℕ) := (2*R+2) + B7 j t R + 1
def B5 (j t R : ℕ) :=
  MatrixAddressMachine.exactTime (2^j) (t+j-2) 0 + B6 j t R + 1
def B4 (j t R : ℕ) := (4*2^j+5*j+7) + B5 j t R + 1
def B3 (j t R : ℕ) := (2*j+2) + B4 j t R + 1
def B2 (j t R : ℕ) := ((t-2)+1) + B3 j t R + 1
def timeBound (j t R : ℕ) := (2*j+2) + B2 j t R + 1

theorem q5_run (S : Bank → List Bool) (j t R : ℕ)
    (hR : S 6 = unary R)
    (h7 : S 7 = []) (h8 : S 8 = []) (h9 : S 9 = [])
    (h10 : S 10 = []) (h11 : S 11 = []) (h12 : S 12 = [])
    (h13 : S 13 = []) (h14 : S 14 = []) (h15 : S 15 = []) :
    ∃ u ≤ B5 j t R,
      ((advance q5)^[u])
        (⟨some (BitMachineRawSequence.leftLabel MatrixAddressMachine.Label.outer),
          v5, S4 S j t⟩ : TM2.Cfg (fun _ : Bank => Bool) _ _) =
        ⟨none, v5, finalBank S j t R⟩ := by
  have hm := stage5 S j t h9 h10 h13 h14
  obtain ⟨u, hu, hr⟩ := q6_run S j t R hR h7 h8 h9 h10 h11 h12 h13 h14 h15
  obtain ⟨steps, hsteps, hrun⟩ := BitMachineRawSequence.runs
    p5 q6 MatrixAddressMachine.Label.outer
    (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)
    false false v6 v6
    (S4 S j t) (S5 S j t) (finalBank S j t R)
    (MatrixAddressMachine.exactTime (2^j) (t+j-2) 0) u hm hr
  exact ⟨steps, by dsimp [B5, B6, B7]; omega,
    by simpa [q5, v5] using hrun⟩

theorem q4_run (S : Bank → List Bool) (j t R : ℕ)
    (hR : S 6 = unary R)
    (h7 : S 7 = []) (h8 : S 8 = []) (h9 : S 9 = [])
    (h10 : S 10 = []) (h11 : S 11 = []) (h12 : S 12 = [])
    (h13 : S 13 = []) (h14 : S 14 = []) (h15 : S 15 = []) :
    ∃ u ≤ B4 j t R,
      ((advance q4)^[u])
        (⟨some (BitMachineRawSequence.leftLabel (.inr false : MatrixUnaryPower.Label)),
          v4, S3 S j t⟩ : TM2.Cfg (fun _ : Bank => Bool) _ _) =
        ⟨none, v4, finalBank S j t R⟩ := by
  obtain ⟨up, hup, hp⟩ := stage4 S j t h8 h9 h10
  obtain ⟨um, hum, hm⟩ := q5_run S j t R hR h7 h8 h9 h10 h11 h12 h13 h14 h15
  obtain ⟨steps, hsteps, hrun⟩ := BitMachineRawSequence.runs
    p4 q5 (.inr false : MatrixUnaryPower.Label)
    (BitMachineRawSequence.leftLabel MatrixAddressMachine.Label.outer)
    (((false,false),none) : MatrixUnaryPower.Control) ((false,false),none) v5 v5
    (S3 S j t) (S4 S j t) (finalBank S j t R) up um hp hm
  exact ⟨steps, by dsimp [B4]; omega, by simpa [q4, v4] using hrun⟩

theorem q3_run (S : Bank → List Bool) (j t R : ℕ) (ht : 4 ≤ t)
    (hj : S 4 = unary j) (hR : S 6 = unary R)
    (h7 : S 7 = []) (h8 : S 8 = []) (h9 : S 9 = [])
    (h10 : S 10 = []) (h11 : S 11 = []) (h12 : S 12 = [])
    (h13 : S 13 = []) (h14 : S 14 = []) (h15 : S 15 = []) :
    ∃ u ≤ B3 j t R,
      ((advance q3)^[u])
        (⟨some (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan),
          v3, S2 S j t⟩ : TM2.Cfg (fun _ : Bank => Bool) _ _) =
        ⟨none, v3, finalBank S j t R⟩ := by
  have hc := stage3 S j t ht hj h15
  obtain ⟨u, hu, hr⟩ := q4_run S j t R hR h7 h8 h9 h10 h11 h12 h13 h14 h15
  obtain ⟨steps, hsteps, hrun⟩ := BitMachineRawSequence.runs
    p3 q4 BitMachineCopy.Label.scan
    (BitMachineRawSequence.leftLabel (.inr false : MatrixUnaryPower.Label))
    (none : Option Bool) none v4 v4
    (S2 S j t) (S3 S j t) (finalBank S j t R)
    (2*j+2) u hc hr
  exact ⟨steps, by dsimp [B3]; omega, by simpa [q3, v3] using hrun⟩

theorem q2_run (S : Bank → List Bool) (j t R : ℕ) (ht : 4 ≤ t)
    (hj : S 4 = unary j) (hR : S 6 = unary R)
    (h7 : S 7 = []) (h8 : S 8 = []) (h9 : S 9 = [])
    (h10 : S 10 = []) (h11 : S 11 = []) (h12 : S 12 = [])
    (h13 : S 13 = []) (h14 : S 14 = []) (h15 : S 15 = []) :
    ∃ u ≤ B2 j t R,
      ((advance (q2 t))^[u])
        (⟨some (BitMachineRawSequence.leftLabel
            (0 : SourceClauseFixedUnary.Label (t-2))),
          v2, S1 S j⟩ : TM2.Cfg (fun _ : Bank => Bool) _ _) =
        ⟨none, v2, finalBank S j t R⟩ := by
  have hf := stage2 S j t h11
  obtain ⟨u, hu, hr⟩ := q3_run S j t R ht hj hR
    h7 h8 h9 h10 h11 h12 h13 h14 h15
  obtain ⟨steps, hsteps, hrun⟩ := BitMachineRawSequence.runs
    (p2 t) q3 (0 : SourceClauseFixedUnary.Label (t-2))
    (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan)
    () () v3 v3 (S1 S j) (S2 S j t) (finalBank S j t R)
    ((t-2)+1) u hf hr
  exact ⟨steps, by dsimp [B2]; omega, by simpa [q2, v2] using hrun⟩

/-- A fixed Fin16 instruction table for each fixed t. Every ambient input
bank survives; the only output is one Boolean verdict on bank 12. -/
theorem run (S : Bank → List Bool) (j t R : ℕ) (ht : 4 ≤ t)
    (hj : S 4 = unary j) (hR : S 6 = unary R)
    (h7 : S 7 = []) (h8 : S 8 = []) (h9 : S 9 = [])
    (h10 : S 10 = []) (h11 : S 11 = []) (h12 : S 12 = [])
    (h13 : S 13 = []) (h14 : S 14 = []) (h15 : S 15 = []) :
    ∃ u ≤ timeBound j t R,
      ((advance (program t))^[u])
        (⟨some (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan),
          v1, S⟩ : TM2.Cfg (fun _ : Bank => Bool) _ _) =
        ⟨none, v1, finalBank S j t R⟩ := by
  have hc := stage1 S j hj h7 h15
  obtain ⟨u, hu, hr⟩ := q2_run S j t R ht hj hR
    h7 h8 h9 h10 h11 h12 h13 h14 h15
  obtain ⟨steps, hsteps, hrun⟩ := BitMachineRawSequence.runs
    p1 (q2 t) BitMachineCopy.Label.scan
    (BitMachineRawSequence.leftLabel (0 : SourceClauseFixedUnary.Label (t-2)))
    (none : Option Bool) none v2 v2
    S (S1 S j) (finalBank S j t R) (2*j+2) u hc hr
  exact ⟨steps, by dsimp [timeBound]; omega,
    by simpa [program, v1] using hrun⟩

theorem verdict_source (b t j : ℕ) (ht : 4 ≤ t) (S : Bank → List Bool)
    (hj : S 4 = unary j) (hR : S 6 = unary (2^(t+b-3)))
    (h7 : S 7 = []) (h8 : S 8 = []) (h9 : S 9 = [])
    (h10 : S 10 = []) (h11 : S 11 = []) (h12 : S 12 = [])
    (h13 : S 13 = []) (h14 : S 14 = []) (h15 : S 15 = []) :
    ∃ u ≤ timeBound j t (2^(t+b-3)),
      ((advance (program t))^[u])
        (⟨some (BitMachineRawSequence.leftLabel BitMachineCopy.Label.scan),
          v1, S⟩ : TM2.Cfg (fun _ : Bank => Bool) _ _) =
        ⟨none, v1, Function.update S 12 [decide (sourceCutFeasible b t j)]⟩ := by
  simpa only [finalBank, sourceCutFeasible] using
    run S j t (2^(t+b-3)) ht hj hR h7 h8 h9 h10 h11 h12 h13 h14 h15

/-- The charged clock is quadratic in the sum of its public unary operand
lengths and the generated power length. -/
theorem timeBound_quadratic (j t R : ℕ) :
    timeBound j t R ≤ 100 * (j+t+R+2^j+1)^2 := by
  let X := j+t+R+2^j+1
  have hpow0 : 0 ≤ (2^j : ℕ) := Nat.zero_le _
  have hwidth0 : 0 ≤ t+j-2 := Nat.zero_le _
  have hj : j ≤ X := by dsimp [X]; omega
  have ht : t ≤ X := by dsimp [X]; omega
  have hR : R ≤ X := by dsimp [X]; omega
  have hp : 2^j ≤ X := by dsimp [X]; omega
  have hw : t+j-2 ≤ X := by dsimp [X]; omega
  have hpos : 1 ≤ X := by dsimp [X]; omega
  have hprod : 2^j*(t+j-2) ≤ X^2 := by
    calc
      2^j*(t+j-2) ≤ X*X := Nat.mul_le_mul hp hw
      _ = X^2 := by ring
  have hlinear : X ≤ X^2 := by nlinarith
  have hmax : max (2^j*(t+j-2)) R ≤ X^2 :=
    max_le hprod (hR.trans hlinear)
  change timeBound j t R ≤ 100*X^2
  dsimp [timeBound, B2, B3, B4, B5, B6, B7,
    MatrixAddressMachine.exactTime]
  simp only [mul_assoc]
  omega

/-- For a candidate in the manuscript's finite scan, the tester's physical
clock is quadratic in H=2^b, with a constant depending only on fixed t. -/
theorem timeBound_public (b t j : ℕ)
    (hj : j ≤ sourcePairDepth b t) :
    timeBound j t (2^(t+b-3)) ≤
      100 * (2^(2*t)+2^t+3*t+3)^2 * (2^b+1)^2 := by
  let H := 2^b
  let C := 2^(2*t)+2^t+3*t+3
  have hb : b ≤ H := Nat.le_of_lt Nat.lt_two_pow_self
  have hj' : j ≤ b+2*t := by dsimp [sourcePairDepth] at hj; omega
  have hp : 2^j ≤ H*2^(2*t) := by
    calc
      2^j ≤ 2^(b+2*t) := pow_le_pow_right₀ (by decide : (1:ℕ) ≤ 2) hj'
      _ = H*2^(2*t) := by simp [H, pow_add]
  have hR : 2^(t+b-3) ≤ H*2^t := by
    calc
      2^(t+b-3) ≤ 2^(b+t) := pow_le_pow_right₀ (by decide : (1:ℕ) ≤ 2) (by omega)
      _ = H*2^t := by simp [H, pow_add]
  have hsum : j+t+2^(t+b-3)+2^j+1 ≤ C*(H+1) := by
    have hpre : j+t+2^(t+b-3)+2^j+1 ≤
        H*(2^(2*t)+2^t+1)+3*t+1 := by
      nlinarith [hj', hb, hp, hR]
    calc
      j+t+2^(t+b-3)+2^j+1 ≤
          H*(2^(2*t)+2^t+1)+3*t+1 := hpre
      _ ≤ C*(H+1) := by
        have heq : C*(H+1) =
            H*(2^(2*t)+2^t+1)+3*t+1 +
              (H*(3*t+2)+2^(2*t)+2^t+2) := by
          dsimp [C]
          ring
        rw [heq]
        exact Nat.le_add_right _ _
  calc
    timeBound j t (2^(t+b-3)) ≤
        100*(j+t+2^(t+b-3)+2^j+1)^2 := timeBound_quadratic ..
    _ ≤ 100*C^2*(H+1)^2 := by
      have hsquare := Nat.pow_le_pow_left hsum 2
      nlinarith [hsquare]
    _ = 100 * (2^(2*t)+2^t+3*t+3)^2 * (2^b+1)^2 := by rfl

#print axioms run
#print axioms verdict_source
#print axioms timeBound_public

end CurrentAdditive.SmallBias.YaoCutTester
