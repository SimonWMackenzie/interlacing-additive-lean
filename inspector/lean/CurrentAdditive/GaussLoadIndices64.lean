import CurrentAdditive.GaussActiveIndexReset64

/-! Fixed physical loading of a chosen row and column unary index from
immutable backup banks into the active one-cell getter input banks. -/

namespace CurrentAdditive.GaussLoadIndices64

open EthInapproximability.CurrentPaper
open Turing BitMachineEncoding

abbrev Stack := Fin 64

def rowBank : Fin 2 → Stack := ![17, 18]
def columnBank : Fin 2 → Stack := ![19, 20]

def afterRow (choice : Fin 2) (row : Nat)
    (S : Stack → List Bool) : Stack → List Bool :=
  SourceClausePreservingBroadcast.result (rowBank choice) 63 [15]
    (List.replicate row true) (GaussActiveIndexReset64.cleared S)

def afterColumn (rowChoice columnChoice : Fin 2)
    (row column : Nat) (S : Stack → List Bool) :
    Stack → List Bool :=
  SourceClausePreservingBroadcast.result (columnBank columnChoice) 63 [16]
    (List.replicate column true) (afterRow rowChoice row S)

def rowCopyProgram (choice : Fin 2) :=
  GaussGetterCopy64.program (rowBank choice) 15

def columnCopyProgram (choice : Fin 2) :=
  GaussGetterCopy64.program (columnBank choice) 16

def resetRowProgram (choice : Fin 2) :=
  BitMachineRawSequence.program GaussActiveIndexReset64.program
    (rowCopyProgram choice) SourceClausePreservingBroadcast.Label.scan
    ((), none) ((), none)

def program (rowChoice columnChoice : Fin 2) :=
  BitMachineRawSequence.program (resetRowProgram rowChoice)
    (columnCopyProgram columnChoice)
    SourceClausePreservingBroadcast.Label.scan
    (((), none), ((), none)) ((), none)

abbrev Label := BitMachineRawSequence.Label
  (BitMachineRawSequence.Label GaussActiveIndexReset64.Label
    GaussGetterCopy64.Label) GaussGetterCopy64.Label

abbrev Control := BitMachineRawSequence.Control
  (BitMachineRawSequence.Control GaussActiveIndexReset64.Control
    GaussGetterCopy64.Control) GaussGetterCopy64.Control

abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

def initial (S : Stack → List Bool) : Config :=
  ⟨some (BitMachineRawSequence.leftLabel
    (BitMachineRawSequence.leftLabel (.clear 0))),
    ((((), none), ((), none)), ((), none)), S⟩

def run (rowChoice columnChoice : Fin 2)
    (t : Nat) (c : Config) : Config :=
  ((advance (program rowChoice columnChoice))^[t]) c

def resetClock (S : Stack → List Bool) : Nat :=
  (S 15).length + (S 16).length + 4

def copyClock (n : Nat) : Nat := 2*n+3

def clock (S : Stack → List Bool) (row column : Nat) : Nat :=
  resetClock S + copyClock row + 1 + copyClock column + 1

theorem reset_halt (S : Stack → List Bool) :
    ((advance GaussActiveIndexReset64.program)^[resetClock S])
      (⟨some (.clear 0), ((), none), S⟩ :
        GaussActiveIndexReset64.Config) =
      ⟨none, ((), none), GaussActiveIndexReset64.cleared S⟩ := by
  have h := GaussActiveIndexReset64.reset_run S
  change ((advance GaussActiveIndexReset64.program)^[(S 15).length +
    (S 16).length + 3])
    (⟨some (.clear 0), ((), none), S⟩ :
      GaussActiveIndexReset64.Config) =
      ⟨some .done, ((), none), GaussActiveIndexReset64.cleared S⟩ at h
  unfold resetClock
  rw [show (S 15).length + (S 16).length + 4 =
      ((S 15).length + (S 16).length + 3) + 1 by omega,
    Function.iterate_succ_apply', h]
  rfl

theorem load_run (rowChoice columnChoice : Fin 2)
    (S : Stack → List Bool) (row column : Nat)
    (hrow : S (rowBank rowChoice) = List.replicate row true)
    (hcolumn : S (columnBank columnChoice) = List.replicate column true)
    (htemp : S 63 = []) :
    ∃ t ≤ clock S row column,
      run rowChoice columnChoice t (initial S) =
        ⟨none, ((((), none), ((), none)), ((), none)),
          afterColumn rowChoice columnChoice row column S⟩ := by
  have hrow0 : (GaussActiveIndexReset64.cleared S)
      (rowBank rowChoice) = List.replicate row true := by
    rw [GaussActiveIndexReset64.cleared_other S _
      (by fin_cases rowChoice <;> decide)
      (by fin_cases rowChoice <;> decide)]
    exact hrow
  have hcolumn0 : (GaussActiveIndexReset64.cleared S)
      (columnBank columnChoice) = List.replicate column true := by
    rw [GaussActiveIndexReset64.cleared_other S _
      (by fin_cases columnChoice <;> decide)
      (by fin_cases columnChoice <;> decide)]
    exact hcolumn
  have htemp0 : (GaussActiveIndexReset64.cleared S) 63 = [] := by
    rw [GaussActiveIndexReset64.cleared_other S 63
      (by decide) (by decide)]
    exact htemp
  have htarget15 : (GaussActiveIndexReset64.cleared S) 15 = [] := by
    exact GaussActiveIndexReset64.cleared_active S 0
  have htarget16 : (GaussActiveIndexReset64.cleared S) 16 = [] := by
    exact GaussActiveIndexReset64.cleared_active S 1
  obtain ⟨hrowRun, _, _, htemp1⟩ :=
    GaussGetterCopy64.copy_word (rowBank rowChoice) 15
      (by fin_cases rowChoice <;> decide)
      (by fin_cases rowChoice <;> decide)
      (by decide)
      (List.replicate row true) (GaussActiveIndexReset64.cleared S)
      hrow0 htemp0 htarget15
  have hcolumn1 : (afterRow rowChoice row S)
      (columnBank columnChoice) = List.replicate column true := by
    rw [afterRow]
    rw [GaussGetterCopy64.copy_preserves_other
      (rowBank rowChoice) 15 (columnBank columnChoice)
      (List.replicate row true) (GaussActiveIndexReset64.cleared S)
      (by fin_cases rowChoice <;> fin_cases columnChoice <;> decide)
      (by fin_cases columnChoice <;> decide)
      (by fin_cases columnChoice <;> decide)]
    exact hcolumn0
  have htarget16' : (afterRow rowChoice row S) 16 = [] := by
    rw [afterRow]
    rw [GaussGetterCopy64.copy_preserves_other
      (rowBank rowChoice) 15 16
      (List.replicate row true) (GaussActiveIndexReset64.cleared S)
      (by fin_cases rowChoice <;> decide) (by decide) (by decide)]
    exact htarget16
  obtain ⟨hcolumnRun, _, _, _⟩ :=
    GaussGetterCopy64.copy_word (columnBank columnChoice) 16
      (by fin_cases columnChoice <;> decide)
      (by fin_cases columnChoice <;> decide)
      (by decide)
      (List.replicate column true) (afterRow rowChoice row S)
      hcolumn1 htemp1 htarget16'
  have hrowRun' :
      ((advance (rowCopyProgram rowChoice))^[copyClock row])
        (⟨some .scan, ((), none), GaussActiveIndexReset64.cleared S⟩ :
          GaussGetterCopy64.Config) =
        ⟨none, ((), none), afterRow rowChoice row S⟩ := by
    simpa [rowCopyProgram, copyClock, GaussGetterCopy64.run] using hrowRun
  have hcolumnRun' :
      ((advance (columnCopyProgram columnChoice))^[copyClock column])
        (⟨some .scan, ((), none), afterRow rowChoice row S⟩ :
          GaussGetterCopy64.Config) =
        ⟨none, ((), none),
          afterColumn rowChoice columnChoice row column S⟩ := by
    simpa [columnCopyProgram, copyClock, GaussGetterCopy64.run] using hcolumnRun
  obtain ⟨u, hu, hpair⟩ := BitMachineRawSequence.runs
    GaussActiveIndexReset64.program (rowCopyProgram rowChoice)
    (.clear 0) .scan ((), none) ((), none) ((), none) ((), none)
    S (GaussActiveIndexReset64.cleared S)
    (afterRow rowChoice row S)
    (resetClock S) (copyClock row)
    (reset_halt S) hrowRun'
  obtain ⟨v, hv, hfull⟩ := BitMachineRawSequence.runs
    (resetRowProgram rowChoice) (columnCopyProgram columnChoice)
    (BitMachineRawSequence.leftLabel (.clear 0)) .scan
    (((), none), ((), none)) (((), none), ((), none))
    ((), none) ((), none)
    S (afterRow rowChoice row S)
    (afterColumn rowChoice columnChoice row column S)
    u (copyClock column) hpair hcolumnRun'
  refine ⟨v, ?_, ?_⟩
  · unfold clock
    omega
  · simpa [run, initial, program] using hfull

theorem loaded_indices (rowChoice columnChoice : Fin 2)
    (S : Stack → List Bool) (row column : Nat)
    (hrow : S (rowBank rowChoice) = List.replicate row true)
    (hcolumn : S (columnBank columnChoice) = List.replicate column true) :
    let T := afterColumn rowChoice columnChoice row column S
    T 15 = List.replicate row true ∧
    T 16 = List.replicate column true ∧
    (∀ j : Stack, j ≠ 15 → j ≠ 16 → j ≠ 63 → T j = S j) ∧
    T 63 = [] := by
  dsimp only
  have hclear15 : (GaussActiveIndexReset64.cleared S) 15 = [] :=
    GaussActiveIndexReset64.cleared_active S 0
  have hclear16 : (GaussActiveIndexReset64.cleared S) 16 = [] :=
    GaussActiveIndexReset64.cleared_active S 1
  have hrow15 : afterRow rowChoice row S 15 =
      List.replicate row true := by
    unfold afterRow
    rw [SourceClausePreservingBroadcast.target_written
      (rowBank rowChoice) 63 [15]
      (by simp) (by fin_cases rowChoice <;> decide)
      (by fin_cases rowChoice <;> decide)
      (List.replicate row true) (GaussActiveIndexReset64.cleared S)
      15 (by simp), hclear15, List.append_nil]
  have hrow16 : afterRow rowChoice row S 16 = [] := by
    unfold afterRow
    rw [GaussGetterCopy64.copy_preserves_other
      (rowBank rowChoice) 15 16
      (List.replicate row true) (GaussActiveIndexReset64.cleared S)
      (by fin_cases rowChoice <;> decide) (by decide) (by decide)]
    exact hclear16
  have h15 : afterColumn rowChoice columnChoice row column S 15 =
      List.replicate row true := by
    unfold afterColumn
    rw [GaussGetterCopy64.copy_preserves_other
      (columnBank columnChoice) 16 15
      (List.replicate column true) (afterRow rowChoice row S)
      (by fin_cases columnChoice <;> decide) (by decide) (by decide)]
    exact hrow15
  have h16 : afterColumn rowChoice columnChoice row column S 16 =
      List.replicate column true := by
    unfold afterColumn
    rw [SourceClausePreservingBroadcast.target_written
      (columnBank columnChoice) 63 [16]
      (by simp) (by fin_cases columnChoice <;> decide)
      (by fin_cases columnChoice <;> decide)
      (List.replicate column true) (afterRow rowChoice row S)
      16 (by simp), hrow16, List.append_nil]
  refine ⟨h15, h16, ?_, ?_⟩
  · intro j hj15 hj16 hj63
    unfold afterColumn afterRow
    by_cases hjColumn : j = columnBank columnChoice
    · subst j
      rw [SourceClausePreservingBroadcast.source_restored
        (columnBank columnChoice) 63 [16]
        (by fin_cases columnChoice <;> decide)]
      exact hcolumn.symm
    rw [GaussGetterCopy64.copy_preserves_other
      (columnBank columnChoice) 16 j
      (List.replicate column true)
      (SourceClausePreservingBroadcast.result
        (rowBank rowChoice) 63 [15]
        (List.replicate row true) (GaussActiveIndexReset64.cleared S))
      hjColumn hj63 hj16]
    by_cases hjRow : j = rowBank rowChoice
    · subst j
      rw [SourceClausePreservingBroadcast.source_restored
        (rowBank rowChoice) 63 [15]
        (by fin_cases rowChoice <;> decide)]
      exact hrow.symm
    rw [GaussGetterCopy64.copy_preserves_other
      (rowBank rowChoice) 15 j
      (List.replicate row true) (GaussActiveIndexReset64.cleared S)
      hjRow hj63 hj15]
    exact GaussActiveIndexReset64.cleared_other S j hj15 hj16
  · unfold afterColumn
    exact SourceClausePreservingBroadcast.temp_empty
      (columnBank columnChoice) 63 [16]
      (List.replicate column true) (afterRow rowChoice row S)

#print axioms load_run

#print axioms reset_halt

end CurrentAdditive.GaussLoadIndices64
