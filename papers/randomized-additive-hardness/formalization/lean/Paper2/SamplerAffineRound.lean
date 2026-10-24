import Paper2.AffineMultiplyAdd
import EthInapproximability.CurrentPaper.BitMachineClearBank
import EthInapproximability.CurrentPaper.BitMachineRawSequence

set_option maxHeartbeats 3000000

namespace Paper2.SamplerAffineRound

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open EthInapproximability.CurrentPaper.BitMachineRawSequence

abbrev Stack := Fin 32

def row (b : Bool) : Stack := if b then 15 else 13
def col (b : Bool) : Stack := if b then 16 else 14

theorem locations_distinct (b : Bool) :
    row b ≠ col b ∧ row b ≠ row (!b) ∧ row b ≠ col (!b) ∧
    col b ≠ row (!b) ∧ col b ≠ col (!b) ∧ row (!b) ≠ col (!b) := by
  cases b <;> decide

abbrev ClearLabel := Fin 3
abbrev ClearControl := Unit × Option Bool

def clearProgram (b : Bool) : ClearLabel →
    TM2.Stmt (fun _ : Stack => Bool) ClearLabel ClearControl
  | 0 => BitMachineClearBank.clearStep (row (!b)) 0 1
  | 1 => BitMachineClearBank.clearStep (col (!b)) 1 2
  | _ => .halt

theorem clear_run (b : Bool) (S : Stack → List Bool) :
    ((advance (clearProgram b))^[(S (row (!b))).length +
      (S (col (!b))).length + 3])
      (⟨some 0, ((),none), S⟩ :
        TM2.Cfg (fun _ : Stack => Bool) ClearLabel ClearControl) =
      ⟨none, ((),none),
        Function.update (Function.update S (row (!b)) []) (col (!b)) []⟩ := by
  have hfirst := BitMachineClearBank.clear_one_run
    (clearProgram b) (row (!b)) (0 : ClearLabel) 1 rfl () S
  let T := Function.update S (row (!b)) []
  have hcol : T (col (!b)) = S (col (!b)) := by
    simp only [T, Function.update_of_ne (locations_distinct b).2.2.2.2.2.symm]
  have hsecond := BitMachineClearBank.clear_one_run
    (clearProgram b) (col (!b)) (1 : ClearLabel) 2 rfl () T
  rw [hcol] at hsecond
  have hfinish : advance (clearProgram b)
      (⟨some 2, ((),none), Function.update T (col (!b)) []⟩ :
      TM2.Cfg (fun _ : Stack => Bool) ClearLabel ClearControl) =
      ⟨none, ((),none), Function.update T (col (!b)) []⟩ := rfl
  have htwo :
      ((advance (clearProgram b))^[((S (row (!b))).length + 1) +
        ((S (col (!b))).length + 1)])
        (⟨some 0, ((),none), S⟩ :
          TM2.Cfg (fun _ : Stack => Bool) ClearLabel ClearControl) =
      ⟨some 2, ((),none), Function.update T (col (!b)) []⟩ := by
    rw [show ((S (row (!b))).length + 1) +
      ((S (col (!b))).length + 1) =
      ((S (col (!b))).length + 1) +
      ((S (row (!b))).length + 1) by omega,
      Function.iterate_add_apply, hfirst]
    exact hsecond
  have hthree :
      ((advance (clearProgram b))^[(((S (row (!b))).length + 1) +
        ((S (col (!b))).length + 1)) + 1])
        (⟨some 0, ((),none), S⟩ :
          TM2.Cfg (fun _ : Stack => Bool) ClearLabel ClearControl) =
      ⟨none, ((),none), Function.update T (col (!b)) []⟩ := by
    rw [Function.iterate_succ_apply', htwo]
    exact hfinish
  have htime : (S (row (!b))).length + (S (col (!b))).length + 3 =
      (((S (row (!b))).length + 1) +
        ((S (col (!b))).length + 1)) + 1 := by omega
  rw [htime]
  simpa only [T] using hthree

def rowIndex (b : Bool) : Fin 6 ↪ Stack where
  toFun := ![col b, 10, 9, 17, 18, row (!b)]
  inj' := by
    intro a c h
    cases b <;> fin_cases a <;> fin_cases c <;>
      simp [row, col] at h ⊢

def colIndex (b : Bool) : Fin 6 ↪ Stack where
  toFun := ![row b, 12, 11, 17, 18, col (!b)]
  inj' := by
    intro a c h
    cases b <;> fin_cases a <;> fin_cases c <;>
      simp [row, col] at h ⊢

abbrev FirstLabel := BitMachineRawSequence.Label ClearLabel MatrixAddressMachine.Label
abbrev FirstControl := ClearControl × Bool
abbrev Label := BitMachineRawSequence.Label FirstLabel MatrixAddressMachine.Label
abbrev Control := FirstControl × Bool

def firstProgram (b : Bool) := BitMachineRawSequence.program
  (clearProgram b)
  (MatrixStage4ScalarPreparationOps.multiplyProgram (rowIndex b))
  MatrixAddressMachine.Label.outer ((),none) false

def program (b : Bool) := BitMachineRawSequence.program
  (firstProgram b)
  (MatrixStage4ScalarPreparationOps.multiplyProgram (colIndex b))
  MatrixAddressMachine.Label.outer (((),none),false) false

def initialLabel : Label := .inl (.inl 0)
def initialControl : Control := ((((),none),false),false)

def afterClear (b : Bool) (S : Stack → List Bool) : Stack → List Bool :=
  Function.update (Function.update S (row (!b)) []) (col (!b)) []

def afterRow (b : Bool) (S : Stack → List Bool) (newRow : Nat) :
    Stack → List Bool :=
  Function.update (afterClear b S) (row (!b)) (List.replicate newRow true)

def afterRound (b : Bool) (S : Stack → List Bool) (newRow newCol : Nat) :
    Stack → List Bool :=
  Function.update (afterRow b S newRow) (col (!b))
    (List.replicate newCol true)

private theorem clear_outside (b : Bool) (S : Stack → List Bool)
    (j : Stack) (hr : j ≠ row (!b)) (hc : j ≠ col (!b)) :
    afterClear b S j = S j := by
  simp only [afterClear, Function.update_of_ne hr,
    Function.update_of_ne hc]

theorem round_run (b : Bool) (S : Stack → List Bool)
    (A B C D r c u v : Nat)
    (hA : S 9 = List.replicate A true)
    (hB : S 10 = List.replicate B true)
    (hC : S 11 = List.replicate C true)
    (hD : S 12 = List.replicate D true)
    (hr : S (row b) = List.replicate r true)
    (hc : S (col b) = List.replicate c true)
    (hu : S (row (!b)) = List.replicate u true)
    (hv : S (col (!b)) = List.replicate v true)
    (h17 : S 17 = []) (h18 : S 18 = []) :
    ∃ t ≤ u + v + 3 +
      MatrixAddressMachine.exactTime c B A +
      MatrixAddressMachine.exactTime r D C + 2,
      ((advance (program b))^[t])
        (⟨some initialLabel, initialControl, S⟩ :
          TM2.Cfg (fun _ : Stack => Bool) Label Control) =
      ⟨none, initialControl,
        afterRound b S (A + B*c) (C + D*r)⟩ := by
  let T := afterClear b S
  let U := afterRow b S (A + B*c)
  let V := afterRound b S (A + B*c) (C + D*r)
  have hclear :
      ((advance (clearProgram b))^[u+v+3])
        (⟨some 0, ((),none), S⟩ :
          TM2.Cfg (fun _ : Stack => Bool) ClearLabel ClearControl) =
        ⟨none, ((),none), T⟩ := by
    simpa only [hu, hv, List.length_replicate, T, afterClear]
      using clear_run b S
  have hkeep (j : Stack) (hjrow : j ≠ row (!b))
      (hjcol : j ≠ col (!b)) : T j = S j :=
    clear_outside b S j hjrow hjcol
  have htargetR : T (row (!b)) = [] := by
    simp [T, afterClear, Function.update_of_ne
      (by cases b <;> decide : row (!b) ≠ col (!b))]
  have htargetC : T (col (!b)) = [] := by
    simp [T, afterClear]
  have hmulR := AffineMultiplyAdd.multiply_add_run (rowIndex b) T c B A
    (by change T (col b) = _
        rw [hkeep _ (by cases b <;> decide) (by cases b <;> decide)]
        exact hc)
    (by change T 10 = _
        rw [hkeep _ (by cases b <;> decide) (by cases b <;> decide)]
        exact hB)
    (by change T 9 = _
        rw [hkeep _ (by cases b <;> decide) (by cases b <;> decide)]
        exact hA)
    (by change T 17 = _
        rw [hkeep _ (by cases b <;> decide) (by cases b <;> decide)]
        exact h17)
    (by change T 18 = _
        rw [hkeep _ (by cases b <;> decide) (by cases b <;> decide)]
        exact h18)
  have hmulR' :
      ((advance (MatrixStage4ScalarPreparationOps.multiplyProgram (rowIndex b)))^[
        MatrixAddressMachine.exactTime c B A])
        (⟨some .outer, false, T⟩ :
          TM2.Cfg (fun _ : Stack => Bool) MatrixAddressMachine.Label Bool) =
        ⟨none, false, U⟩ := by
    have heq : Function.update T (rowIndex b 5)
        (List.replicate (c * B + A) true ++ T (rowIndex b 5)) = U := by
      change Function.update T (row (!b))
        (List.replicate (c * B + A) true ++ T (row (!b))) = U
      rw [htargetR, List.append_nil]
      simp only [U, afterRow]
      have hnum : c * B + A = A + B * c := by ring
      rw [hnum]
    rw [heq] at hmulR
    exact hmulR
  have hUkeep (j : Stack) (hj : j ≠ row (!b)) : U j = T j := by
    simp only [U, afterRow, T, Function.update_of_ne hj]
  have hmulC := AffineMultiplyAdd.multiply_add_run (colIndex b) U r D C
    (by change U (row b) = _
        rw [hUkeep _ (by cases b <;> decide),
          hkeep _ (by cases b <;> decide) (by cases b <;> decide)]
        exact hr)
    (by change U 12 = _
        rw [hUkeep _ (by cases b <;> decide),
          hkeep _ (by cases b <;> decide) (by cases b <;> decide)]
        exact hD)
    (by change U 11 = _
        rw [hUkeep _ (by cases b <;> decide),
          hkeep _ (by cases b <;> decide) (by cases b <;> decide)]
        exact hC)
    (by change U 17 = _
        rw [hUkeep _ (by cases b <;> decide),
          hkeep _ (by cases b <;> decide) (by cases b <;> decide)]
        exact h17)
    (by change U 18 = _
        rw [hUkeep _ (by cases b <;> decide),
          hkeep _ (by cases b <;> decide) (by cases b <;> decide)]
        exact h18)
  have hmulC' :
      ((advance (MatrixStage4ScalarPreparationOps.multiplyProgram (colIndex b)))^[
        MatrixAddressMachine.exactTime r D C])
        (⟨some .outer, false, U⟩ :
          TM2.Cfg (fun _ : Stack => Bool) MatrixAddressMachine.Label Bool) =
        ⟨none, false, V⟩ := by
    have htarget : U (col (!b)) = [] := by
      rw [hUkeep _ (by cases b <;> decide)]
      exact htargetC
    have heq : Function.update U (colIndex b 5)
        (List.replicate (r * D + C) true ++ U (colIndex b 5)) = V := by
      change Function.update U (col (!b))
        (List.replicate (r * D + C) true ++ U (col (!b))) = V
      rw [htarget, List.append_nil]
      simp only [V, afterRound, U]
      have hnum : r * D + C = C + D * r := by ring
      rw [hnum]
    rw [heq] at hmulC
    exact hmulC
  obtain ⟨ta, hta, ha⟩ := BitMachineRawSequence.runs
    (clearProgram b)
    (MatrixStage4ScalarPreparationOps.multiplyProgram (rowIndex b))
    (0 : ClearLabel) MatrixAddressMachine.Label.outer
    ((),none) ((),none) false false
    S T U (u+v+3) (MatrixAddressMachine.exactTime c B A)
    hclear hmulR'
  obtain ⟨t, ht, hrun⟩ := BitMachineRawSequence.runs
    (firstProgram b)
    (MatrixStage4ScalarPreparationOps.multiplyProgram (colIndex b))
    (.inl (0 : ClearLabel)) MatrixAddressMachine.Label.outer
    (((),none),false) (((),none),false) false false
    S U V ta (MatrixAddressMachine.exactTime r D C)
    ha hmulC'
  refine ⟨t, by omega, ?_⟩
  simpa only [program, firstProgram, initialLabel, initialControl,
    V] using hrun

#print axioms round_run

structure Invariant (b : Bool) (S : Stack → List Bool)
    (A B C D r c u v : Nat) : Prop where
  coeffA : S 9 = List.replicate A true
  coeffB : S 10 = List.replicate B true
  coeffC : S 11 = List.replicate C true
  coeffD : S 12 = List.replicate D true
  activeRow : S (row b) = List.replicate r true
  activeCol : S (col b) = List.replicate c true
  inactiveRow : S (row (!b)) = List.replicate u true
  inactiveCol : S (col (!b)) = List.replicate v true
  work17 : S 17 = []
  work18 : S 18 = []

theorem round_invariant (b : Bool) (S : Stack → List Bool)
    (A B C D r c u v : Nat)
    (h : Invariant b S A B C D r c u v) :
    Invariant (!b) (afterRound b S (A+B*c) (C+D*r))
      A B C D (A+B*c) (C+D*r) r c := by
  cases b <;>
    constructor <;>
    simp [afterRound, afterRow, afterClear, row, col,
      h.coeffA, h.coeffB, h.coeffC, h.coeffD,
      h.work17, h.work18] <;>
    first
    | simpa [row, col] using h.activeRow
    | simpa [row, col] using h.activeCol

theorem round_fuel (b : Bool) (S : Stack → List Bool)
    (r c : Nat) :
    (afterRound b S r c) 6 = S 6 := by
  cases b <;> simp [afterRound, afterRow, afterClear, row, col]

theorem round_run_inv (b : Bool) (S : Stack → List Bool)
    (A B C D r c u v : Nat)
    (h : Invariant b S A B C D r c u v) :
    ∃ t ≤ u + v + 3 +
      MatrixAddressMachine.exactTime c B A +
      MatrixAddressMachine.exactTime r D C + 2,
      ((advance (program b))^[t])
        (⟨some initialLabel, initialControl, S⟩ :
          TM2.Cfg (fun _ : Stack => Bool) Label Control) =
      ⟨none, initialControl,
        afterRound b S (A+B*c) (C+D*r)⟩ :=
  round_run b S A B C D r c u v h.coeffA h.coeffB h.coeffC
    h.coeffD h.activeRow h.activeCol h.inactiveRow h.inactiveCol
    h.work17 h.work18

#print axioms round_invariant
#print axioms round_run_inv

end Paper2.SamplerAffineRound
