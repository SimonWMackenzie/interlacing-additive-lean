import Paper2.CodeSampleFrames

/-! One fixed machine assembles the exact current row-first sample code from the actual row/column code words and counts.
This is the final syntax-building suffix, not yet the raw graph reduction. -/

namespace CurrentAdditive.V39DeadSampleAssembly

open Paper2

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open Paper2.GeneratorCode Paper2.GeneratorSerialization
open Paper2.CodeSampleFrames

abbrev Stack := Fin 12

def rowIndex : Fin 5 ↪ Stack where
  toFun i := ⟨i.val, by omega⟩
  inj' := by intro i j h; exact Fin.ext (Fin.mk.inj h)

def colIndex : Fin 5 ↪ Stack where
  toFun i := ⟨i.val + 5, by omega⟩
  inj' := by intro i j h; apply Fin.ext; have := Fin.mk.inj h; omega

def appendIndex : Fin 8 ↪ Stack where
  toFun := ![2, 7, 0, 3, 4, 5, 10, 11]
  inj' := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all

def initial (mX mY : Nat) (row col : Code) : Stack → List Bool :=
  ![unary mX, encodeCode row, [], [], [],
    unary mY, encodeCode col, [], [], [], [], []]

def afterRow (mX mY : Nat) (row col : Code) :=
  Function.update (Function.update (initial mX mY row col) (0 : Stack) [])
    (2 : Stack) (encodeCode (copies mX row))

def afterBoth (mX mY : Nat) (row col : Code) :=
  Function.update (Function.update (afterRow mX mY row col) (5 : Stack) [])
    (7 : Stack) (encodeCode (copies mY col))

def final (mX mY : Nat) (row col : Code) :=
  Function.update (afterBoth mX mY row col) (10 : Stack)
    (encodeCode (.append (copies mX row) (copies mY col)))

def bothProgram := BitMachineRawSequence.program
  (copiesProgram rowIndex) (copiesProgram colIndex)
  CodeCopiesMachine.Label.initialize none none

def program := BitMachineRawSequence.program bothProgram
  (appendProgram appendIndex) CodeConstructorMachine.Label.appendRightCopy
  (none, none) none

def startLabel : BitMachineRawSequence.Label
    (BitMachineRawSequence.Label CodeCopiesMachine.Label CodeCopiesMachine.Label)
    CodeConstructorMachine.Label := BitMachineRawSequence.leftLabel
  (BitMachineRawSequence.leftLabel CodeCopiesMachine.Label.initialize)

def clock (mX mY : Nat) (row col : Code) :=
  CodeCopiesMachine.clock mX row + CodeCopiesMachine.clock mY col +
    CodeConstructorMachine.appendClock
      (encodeCode (copies mX row)) (encodeCode (copies mY col)) + 2

theorem row_run (mX mY : Nat) (row col : Code) :
    ((advance (copiesProgram rowIndex))^[CodeCopiesMachine.clock mX row])
      (⟨some CodeCopiesMachine.Label.initialize, none, initial mX mY row col⟩ :
        TM2.Cfg (fun _ : Stack => Bool) _ _) =
      ⟨none, none, afterRow mX mY row col⟩ := by
  simpa only [rowIndex, afterRow] using copies_run rowIndex
    (initial mX mY row col) mX row rfl rfl rfl rfl rfl

theorem col_run (mX mY : Nat) (row col : Code) :
    ((advance (copiesProgram colIndex))^[CodeCopiesMachine.clock mY col])
      (⟨some CodeCopiesMachine.Label.initialize, none, afterRow mX mY row col⟩ :
        TM2.Cfg (fun _ : Stack => Bool) _ _) =
      ⟨none, none, afterBoth mX mY row col⟩ := by
  apply copies_run colIndex (afterRow mX mY row col) mY col
  all_goals simp [afterRow, initial, colIndex]

theorem append_run (mX mY : Nat) (row col : Code) :
    ((advance (appendProgram appendIndex))^[CodeConstructorMachine.appendClock
      (encodeCode (copies mX row)) (encodeCode (copies mY col))])
      (⟨some CodeConstructorMachine.Label.appendRightCopy, none,
        afterBoth mX mY row col⟩ : TM2.Cfg (fun _ : Stack => Bool) _ _) =
      ⟨none, none, final mX mY row col⟩ := by
  apply CodeSampleFrames.append_run appendIndex (afterBoth mX mY row col)
    (copies mX row) (copies mY col)
  all_goals simp [afterBoth, afterRow, initial, appendIndex]

theorem run (mX mY : Nat) (row col : Code) :
    ∃ t ≤ clock mX mY row col,
      ((advance program)^[t])
        (⟨some startLabel, ((none,none),none), initial mX mY row col⟩ :
          TM2.Cfg (fun _ : Stack => Bool) _ _) =
        ⟨none, ((none,none),none), final mX mY row col⟩ := by
  obtain ⟨ta, hta, ha⟩ := BitMachineRawSequence.runs
    (copiesProgram rowIndex) (copiesProgram colIndex)
    CodeCopiesMachine.Label.initialize CodeCopiesMachine.Label.initialize
    none none none none
    (initial mX mY row col) (afterRow mX mY row col)
    (afterBoth mX mY row col)
    (CodeCopiesMachine.clock mX row) (CodeCopiesMachine.clock mY col)
    (row_run mX mY row col) (col_run mX mY row col)
  obtain ⟨t, ht, h⟩ := BitMachineRawSequence.runs bothProgram
    (appendProgram appendIndex)
    (BitMachineRawSequence.leftLabel CodeCopiesMachine.Label.initialize)
    CodeConstructorMachine.Label.appendRightCopy
    (none,none) (none,none) none none
    (initial mX mY row col) (afterBoth mX mY row col)
    (final mX mY row col) ta
    (CodeConstructorMachine.appendClock
      (encodeCode (copies mX row)) (encodeCode (copies mY col)))
    ha (append_run mX mY row col)
  exact ⟨t, by dsimp [clock]; omega, h⟩

theorem output_exact (mX mY : Nat) (row col : Code) :
    final mX mY row col 10 =
      encodeCode (.append (copies mX row) (copies mY col)) := by
  simp [final]

theorem clock_polynomial (mX mY : Nat) (row col : Code) :
    clock mX mY row col ≤
      64 * (mX + mY + codeSize row + codeSize col + 2) ^ 2 := by
  let M := mX + mY + codeSize row + codeSize col + 2
  have hm : 1 ≤ M := by omega
  have hX : mX + 1 ≤ M := by omega
  have hY : mY + 1 ≤ M := by omega
  have hr : codeSize row + 1 ≤ M := by omega
  have hc : codeSize col + 1 ≤ M := by omega
  have hx := Nat.mul_le_mul hX hr
  have hy := Nat.mul_le_mul hY hc
  have hxclock := CodeCopiesMachine.clock_polynomial mX row
  have hyclock := CodeCopiesMachine.clock_polynomial mY col
  have hxsize := CodeCopiesMachine.output_size_polynomial mX row
  have hysize := CodeCopiesMachine.output_size_polynomial mY col
  have happ := CodeConstructorMachine.appendClock_polynomial
    (copies mX row) (copies mY col)
  change clock mX mY row col ≤ 64 * M ^ 2
  dsimp only [clock]
  nlinarith

#print axioms run
#print axioms clock_polynomial

end CurrentAdditive.V39DeadSampleAssembly
