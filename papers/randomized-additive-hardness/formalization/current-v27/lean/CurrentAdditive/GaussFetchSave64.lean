import CurrentAdditive.GaussOneFetchForeign64

/-! One physical cell fetch followed by a charged source-preserving save of
the selected encoded cell to a caller-owned low bank. -/

namespace CurrentAdditive.GaussFetchSave64

open EthInapproximability.CurrentPaper
open Turing BitMachineEncoding

abbrev Stack := Fin 64

def fetchStart : GaussOneFetchProgram64.Label :=
  BitMachineRawSequence.leftLabel
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel (.clear 0)))

def fetchControl : GaussOneFetchProgram64.Control :=
  ((((((), none), ((), none)), ((), none)),
    GaussOneFetchProgram64.getterControl))

theorem fetch_initial (S : Stack → List Bool) :
    GaussOneFetchProgram64.initial S =
      ⟨some fetchStart, fetchControl, S⟩ := rfl

def program (target : Stack) :=
  BitMachineRawSequence.program GaussOneFetchProgram64.program
    (GaussGetterCopy64.program 38 target)
    SourceClausePreservingBroadcast.Label.scan
    fetchControl ((), none)

abbrev Label := BitMachineRawSequence.Label
  GaussOneFetchProgram64.Label GaussGetterCopy64.Label

abbrev Control := BitMachineRawSequence.Control
  GaussOneFetchProgram64.Control GaussGetterCopy64.Control

abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

def run (target : Stack) (t : Nat) (c : Config) : Config :=
  ((advance (program target))^[t]) c

def initial (S : Stack → List Bool) : Config :=
  ⟨some (BitMachineRawSequence.leftLabel fetchStart),
    (fetchControl, ((), none)), S⟩

theorem fetch_save (target : Stack) (hLow : target.val < 32)
    (hTarget8 : target ≠ 8)
    (rowPre rowSuffix cellPre cellSuffix : List (List Bool))
    (cell : List Bool) (S : Stack → List Bool)
    (hmat : S 8 = SourceListEncoding.encode
      (rowPre ++ SourceListEncoding.encode
        (cellPre ++ cell :: cellSuffix) :: rowSuffix))
    (hrow : S 15 = List.replicate rowPre.length true)
    (hcolumn : S 16 = List.replicate cellPre.length true)
    (htemp : S 63 = []) (hTargetBlank : S target = []) :
    let row := SourceListEncoding.encode (cellPre ++ cell :: cellSuffix)
    let matrix := SourceListEncoding.encode (rowPre ++ row :: rowSuffix)
    ∃ t ≤ GaussOneFetchProgram64.preparationClock S
        rowPre.length cellPre.length +
        140 * (matrix.length + 1)^3 + 1 +
        (2 * cell.length + 3) + 1,
      (run target t (initial S)).l = none ∧
      (run target t (initial S)).stk target = cell ∧
      (run target t (initial S)).stk 8 = matrix ∧
      (∀ j : Stack, j.val < 32 → j ≠ target →
        (run target t (initial S)).stk j = S j) ∧
      (run target t (initial S)).stk 63 = [] := by
  dsimp only
  obtain ⟨tFetch, htFetch, hHalt, hCell, hMatrix,
    hForeign, hTemp⟩ :=
    GaussOneFetchForeign64.canonical_one_fetch_foreign
      rowPre rowSuffix cellPre cellSuffix cell S
      hmat hrow hcolumn htemp
  let fetched := GaussOneFetchProgram64.run tFetch
    (GaussOneFetchProgram64.initial S)
  have hFetchRun :
      ((advance GaussOneFetchProgram64.program)^[tFetch])
        (⟨some fetchStart, fetchControl, S⟩ :
          GaussOneFetchProgram64.Config) =
        ⟨none, fetched.var, fetched.stk⟩ := by
    rw [← fetch_initial S]
    change fetched = ⟨none, fetched.var, fetched.stk⟩
    cases hf : fetched with
    | mk l v T =>
        cases l with
        | none => rfl
        | some l =>
            have hh : fetched.l = none := hHalt
            rw [hf] at hh
            contradiction
  have hTargetBlank' : fetched.stk target = [] :=
    (hForeign target hLow).trans hTargetBlank
  have h38 : (38 : Stack) ≠ 63 := by decide
  have hTarget38 : target ≠ (38 : Stack) := by
    intro h
    have hv := congrArg Fin.val h
    omega
  have hTarget63 : target ≠ (63 : Stack) := by
    intro h
    have hv := congrArg Fin.val h
    omega
  obtain ⟨hCopyRun, hSaved, _, hTemp2⟩ :=
    GaussGetterCopy64.copy_word 38 target h38 hTarget38
      hTarget63 cell fetched.stk hCell hTemp hTargetBlank'
  let saved := SourceClausePreservingBroadcast.result 38 63
    [target] cell fetched.stk
  have hCopyRun' :
      ((advance (GaussGetterCopy64.program 38 target))^[2 * cell.length + 3])
        (⟨some SourceClausePreservingBroadcast.Label.scan,
          ((), none), fetched.stk⟩ : GaussGetterCopy64.Config) =
        ⟨none, ((), none), saved⟩ := hCopyRun
  obtain ⟨t, ht, hfull⟩ := BitMachineRawSequence.runs
    GaussOneFetchProgram64.program
    (GaussGetterCopy64.program 38 target)
    fetchStart SourceClausePreservingBroadcast.Label.scan
    fetchControl fetched.var ((), none) ((), none)
    S fetched.stk saved tFetch (2 * cell.length + 3)
    hFetchRun hCopyRun'
  have heq : run target t (initial S) =
      ⟨none, (fetchControl, ((), none)), saved⟩ := by
    simpa [run, initial, program] using hfull
  refine ⟨t, by omega, ?_, ?_, ?_, ?_, ?_⟩
  · rw [heq]
  · rw [heq]
    exact hSaved
  · rw [heq]
    have h8 : saved 8 = fetched.stk 8 :=
      GaussGetterCopy64.copy_preserves_other 38 target 8
        cell fetched.stk (by decide) (by decide) hTarget8.symm
    exact h8.trans hMatrix
  · intro j hj hne
    rw [heq]
    have hother : saved j = fetched.stk j :=
      GaussGetterCopy64.copy_preserves_other 38 target j
        cell fetched.stk
        (by intro he; have hv := congrArg Fin.val he; omega)
        (by intro he; have hv := congrArg Fin.val he; omega)
        hne
    exact hother.trans (hForeign j hj)
  · rw [heq]
    exact hTemp2

#print axioms fetch_save

end CurrentAdditive.GaussFetchSave64
