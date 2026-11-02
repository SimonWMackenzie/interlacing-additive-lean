import CurrentAdditive.GaussLoadIndices64

/-! One charged Gauss cell fetch from immutable caller index banks, saving the
encoded cell to a separate caller bank. -/

namespace CurrentAdditive.GaussFetchFromBackups64

open EthInapproximability.CurrentPaper
open Turing BitMachineEncoding

abbrev Stack := Fin 64

def program (rowChoice columnChoice : Fin 2) (target : Stack) :=
  BitMachineRawSequence.program
    (GaussLoadIndices64.program rowChoice columnChoice)
    (GaussFetchSave64.program target)
    (BitMachineRawSequence.leftLabel GaussFetchSave64.fetchStart)
    ((((), none), ((), none)), ((), none))
    (GaussFetchSave64.fetchControl, ((), none))

abbrev Label := BitMachineRawSequence.Label
  GaussLoadIndices64.Label GaussFetchSave64.Label

abbrev Control := BitMachineRawSequence.Control
  GaussLoadIndices64.Control GaussFetchSave64.Control

abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

def initial (S : Stack → List Bool) : Config :=
  ⟨some (BitMachineRawSequence.leftLabel
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel (.clear 0)))),
    (((((), none), ((), none)), ((), none)),
      (GaussFetchSave64.fetchControl, ((), none))), S⟩

def run (rowChoice columnChoice : Fin 2) (target : Stack)
    (t : Nat) (c : Config) : Config :=
  ((advance (program rowChoice columnChoice target))^[t]) c

def clock (rowChoice columnChoice : Fin 2)
    (S : Stack → List Bool) (row column : Nat)
    (matrix cell : List Bool) : Nat :=
  GaussLoadIndices64.clock S row column +
    GaussOneFetchProgram64.preparationClock
      (GaussLoadIndices64.afterColumn rowChoice columnChoice row column S)
      row column +
    140 * (matrix.length + 1)^3 + 1 +
    (2 * cell.length + 3) + 2

theorem fetch_from_backups
    (rowChoice columnChoice : Fin 2) (target : Stack)
    (htargetLow : target.val < 32) (htargetHigh : 21 ≤ target.val)
    (rowPre rowSuffix cellPre cellSuffix : List (List Bool))
    (cell : List Bool) (S : Stack → List Bool)
    (hmat : S 8 = SourceListEncoding.encode
      (rowPre ++ SourceListEncoding.encode
        (cellPre ++ cell :: cellSuffix) :: rowSuffix))
    (hrow : S (GaussLoadIndices64.rowBank rowChoice) =
      List.replicate rowPre.length true)
    (hcolumn : S (GaussLoadIndices64.columnBank columnChoice) =
      List.replicate cellPre.length true)
    (htemp : S 63 = []) (hblank : S target = []) :
    let matrix := SourceListEncoding.encode
      (rowPre ++ SourceListEncoding.encode
        (cellPre ++ cell :: cellSuffix) :: rowSuffix)
    ∃ t ≤ clock rowChoice columnChoice S rowPre.length cellPre.length
      matrix cell,
      (run rowChoice columnChoice target t (initial S)).l = none ∧
      (run rowChoice columnChoice target t (initial S)).stk target = cell ∧
      (run rowChoice columnChoice target t (initial S)).stk 8 = matrix ∧
      (∀ j : Stack, j.val < 32 → j ≠ target →
        j ≠ 15 → j ≠ 16 →
        (run rowChoice columnChoice target t (initial S)).stk j = S j) ∧
      (run rowChoice columnChoice target t (initial S)).stk 63 = [] := by
  dsimp only
  let T := GaussLoadIndices64.afterColumn rowChoice columnChoice
    rowPre.length cellPre.length S
  obtain ⟨tLoad, htLoad, hLoad⟩ :=
    GaussLoadIndices64.load_run rowChoice columnChoice S
      rowPre.length cellPre.length hrow hcolumn htemp
  obtain ⟨hTrow, hTcolumn, hTforeign, hTtemp⟩ :=
    GaussLoadIndices64.loaded_indices rowChoice columnChoice S
      rowPre.length cellPre.length hrow hcolumn
  have hTmat : T 8 = SourceListEncoding.encode
      (rowPre ++ SourceListEncoding.encode
        (cellPre ++ cell :: cellSuffix) :: rowSuffix) := by
    exact (hTforeign 8 (by decide) (by decide) (by decide)).trans hmat
  have hTblank : T target = [] := by
    exact (hTforeign target
      (by intro he; have hv := congrArg Fin.val he; omega)
      (by intro he; have hv := congrArg Fin.val he; omega)
      (by intro he; have hv := congrArg Fin.val he; omega)).trans hblank
  obtain ⟨tFetch, htFetch, hHalt, hCell, hMatrix,
    hForeign, hTemp⟩ :=
    GaussFetchSave64.fetch_save target htargetLow
      (by intro he; have hv := congrArg Fin.val he; omega)
      rowPre rowSuffix cellPre cellSuffix cell T
      hTmat hTrow hTcolumn hTtemp hTblank
  let fetched := GaussFetchSave64.run target tFetch
    (GaussFetchSave64.initial T)
  have hFetchRun :
      ((advance (GaussFetchSave64.program target))^[tFetch])
        (⟨some (BitMachineRawSequence.leftLabel
          GaussFetchSave64.fetchStart),
          (GaussFetchSave64.fetchControl, ((), none)), T⟩ :
          GaussFetchSave64.Config) =
        ⟨none, fetched.var, fetched.stk⟩ := by
    change fetched = ⟨none, fetched.var, fetched.stk⟩
    cases hf : fetched with
    | mk l v U =>
      cases l with
      | none => rfl
      | some l =>
        have hh : fetched.l = none := hHalt
        rw [hf] at hh
        contradiction
  have hLoadRun :
      ((advance (GaussLoadIndices64.program rowChoice columnChoice))^[tLoad])
        (⟨some (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel (.clear 0))),
          ((((), none), ((), none)), ((), none)), S⟩ :
          GaussLoadIndices64.Config) =
        ⟨none, ((((), none), ((), none)), ((), none)), T⟩ := hLoad
  obtain ⟨t, ht, hfull⟩ := BitMachineRawSequence.runs
    (GaussLoadIndices64.program rowChoice columnChoice)
    (GaussFetchSave64.program target)
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel (.clear 0)))
    (BitMachineRawSequence.leftLabel GaussFetchSave64.fetchStart)
    ((((), none), ((), none)), ((), none))
    ((((), none), ((), none)), ((), none))
    (GaussFetchSave64.fetchControl, ((), none)) fetched.var
    S T fetched.stk tLoad tFetch hLoadRun hFetchRun
  have heq : run rowChoice columnChoice target t (initial S) =
      ⟨none,
        ((( ((), none), ((), none)), ((), none)), fetched.var),
        fetched.stk⟩ := by
    simpa [run, initial, program] using hfull
  refine ⟨t, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold clock
    dsimp only [T] at htFetch
    omega
  · rw [heq]
  · rw [heq]
    exact hCell
  · rw [heq]
    exact hMatrix
  · intro j hj hTarget h15 h16
    rw [heq]
    exact (hForeign j hj hTarget).trans
      (hTforeign j h15 h16
        (by intro he; have hv := congrArg Fin.val he; omega))
  · rw [heq]
    exact hTemp

#print axioms fetch_from_backups

def CellAt (matrix : List Bool) (row column : Nat)
    (cell : List Bool) : Prop :=
  ∃ rowPre rowSuffix cellPre cellSuffix : List (List Bool),
    matrix = SourceListEncoding.encode
      (rowPre ++ SourceListEncoding.encode
        (cellPre ++ cell :: cellSuffix) :: rowSuffix) ∧
    rowPre.length = row ∧ cellPre.length = column

set_option maxHeartbeats 1000000 in
theorem fetch_cell_at
    (rowChoice columnChoice : Fin 2) (target : Stack)
    (htargetLow : target.val < 32) (htargetHigh : 21 ≤ target.val)
    (matrix cell : List Bool) (row column : Nat)
    (S : Stack → List Bool)
    (hmat : S 8 = matrix) (hcell : CellAt matrix row column cell)
    (hrow : S (GaussLoadIndices64.rowBank rowChoice) =
      List.replicate row true)
    (hcolumn : S (GaussLoadIndices64.columnBank columnChoice) =
      List.replicate column true)
    (htemp : S 63 = []) (hblank : S target = []) :
    ∃ t ≤ clock rowChoice columnChoice S row column matrix cell,
      (run rowChoice columnChoice target t (initial S)).l = none ∧
      (run rowChoice columnChoice target t (initial S)).stk target = cell ∧
      (run rowChoice columnChoice target t (initial S)).stk 8 = matrix ∧
      (∀ j : Stack, j.val < 32 → j ≠ target →
        j ≠ 15 → j ≠ 16 →
        (run rowChoice columnChoice target t (initial S)).stk j = S j) ∧
      (run rowChoice columnChoice target t (initial S)).stk 63 = [] := by
  obtain ⟨rowPre, rowSuffix, cellPre, cellSuffix,
    hDecomp, hRowLength, hColumnLength⟩ := hcell
  rw [hDecomp] at hmat
  rw [← hRowLength] at hrow
  rw [← hColumnLength] at hcolumn
  obtain ⟨t, ht, hh, hc, hm, hf, he⟩ :=
    fetch_from_backups rowChoice columnChoice target
      htargetLow htargetHigh rowPre rowSuffix cellPre cellSuffix
      cell S hmat hrow hcolumn htemp hblank
  refine ⟨t, ?_, hh, hc, ?_, hf, he⟩
  · simpa [clock, hRowLength, hColumnLength, hDecomp] using ht
  · exact hm.trans hDecomp.symm

#print axioms fetch_cell_at

end CurrentAdditive.GaussFetchFromBackups64
