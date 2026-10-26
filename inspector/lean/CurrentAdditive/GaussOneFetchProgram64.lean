import CurrentAdditive.GaussGetterPrep64
import EthInapproximability.CurrentPaper.BitMachineRawSequence

/-! One fixed Fin64 controller for resetting scratch, loading two unary
indices, and fetching one cell from a canonical nested V2 matrix. -/

namespace CurrentAdditive.GaussOneFetchProgram64

open EthInapproximability.CurrentPaper
open Turing BitMachineEncoding

abbrev Stack := Fin 64
abbrev CopyLabel := GaussGetterCopy64.Label
abbrev CopyControl := GaussGetterCopy64.Control
abbrev ResetLabel := GaussGetterReset64.Label
abbrev ResetControl := GaussGetterReset64.Control
abbrev GetterLabel := GaussGetterSafe64.Label
abbrev GetterControl := GaussGetterSafe64.Control

def rowProgram := GaussGetterCopy64.program (15 : Stack) 41
def columnProgram := GaussGetterCopy64.program (16 : Stack) 42

def resetRowProgram :=
  BitMachineRawSequence.program GaussGetterReset64.program
    rowProgram SourceClausePreservingBroadcast.Label.scan
      ((), none) ((), none)

def preparationProgram :=
  BitMachineRawSequence.program resetRowProgram
    columnProgram SourceClausePreservingBroadcast.Label.scan
      (((), none), ((), none)) ((), none)

def getterStart : GetterLabel := .inl (.inl (.inl .scan))

def getterControl : GetterControl :=
  (GaussNestedGetter.firstControl
    (CylinderContextScanStep.copyControl ((), none)), ((), none))

def program :=
  BitMachineRawSequence.program preparationProgram
    GaussGetterSafe64.program getterStart
    ((((), none), ((), none)), ((), none)) getterControl

abbrev Label := BitMachineRawSequence.Label
  (BitMachineRawSequence.Label
    (BitMachineRawSequence.Label ResetLabel CopyLabel) CopyLabel)
  GetterLabel

abbrev Control := BitMachineRawSequence.Control
  (BitMachineRawSequence.Control
    (BitMachineRawSequence.Control ResetControl CopyControl) CopyControl)
  GetterControl

abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

def run (t : Nat) (c : Config) : Config := ((advance program)^[t]) c

def initial (S : Stack → List Bool) : Config :=
  ⟨some (BitMachineRawSequence.leftLabel
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel (.clear 0)))),
    ((((((), none), ((), none)), ((), none)), getterControl)), S⟩

def resetClock (S : Stack → List Bool) : Nat :=
  (∑ i : Fin 21, (S (GaussGetterReset64.resetBank i)).length) + 23

def copyClock (n : Nat) : Nat := 2 * n + 3

def preparationClock (S : Stack → List Bool) (row column : Nat) : Nat :=
  resetClock S + copyClock row + 1 + copyClock column + 1

theorem reset_halt (S : Stack → List Bool) :
    ((advance GaussGetterReset64.program)^[resetClock S])
      (⟨some (.clear 0), ((), none), S⟩ : GaussGetterReset64.Config) =
        ⟨none, ((), none), GaussGetterPrep64.resetState S⟩ := by
  have h := GaussGetterReset64.reset_run S
  change ((advance GaussGetterReset64.program)^[(∑ i : Fin 21,
      (S (GaussGetterReset64.resetBank i)).length) + 22])
    (⟨some (.clear 0), ((), none), S⟩ : GaussGetterReset64.Config) =
      ⟨some .done, ((), none), GaussGetterPrep64.resetState S⟩ at h
  unfold resetClock
  rw [show (∑ i : Fin 21,
      (S (GaussGetterReset64.resetBank i)).length) + 23 =
      ((∑ i : Fin 21,
        (S (GaussGetterReset64.resetBank i)).length) + 22) + 1 by omega,
    Function.iterate_succ_apply', h]
  rfl

theorem preparation_run (S : Stack → List Bool)
    (matrix : List Bool) (row column : Nat)
    (hmat : S 8 = matrix)
    (hrow : S 15 = List.replicate row true)
    (hcolumn : S 16 = List.replicate column true)
    (htemp : S 63 = []) :
    ∃ t ≤ preparationClock S row column,
      ((advance preparationProgram)^[t])
        (⟨some (BitMachineRawSequence.leftLabel
          (BitMachineRawSequence.leftLabel (.clear 0))),
          ((((), none), ((), none)), ((), none)), S⟩ :
          TM2.Cfg (fun _ : Stack => Bool) _ _) =
        ⟨none, ((((), none), ((), none)), ((), none)),
          GaussGetterPrep64.finalState row column S⟩ := by
  obtain ⟨_, hrowRun, hcolumnRun, _⟩ :=
    GaussGetterPrep64.physical_preparation S matrix row column
      hmat hrow hcolumn htemp
  have hrowRun' :
      ((advance rowProgram)^[copyClock row])
        (⟨some SourceClausePreservingBroadcast.Label.scan,
          ((), none), GaussGetterPrep64.resetState S⟩ :
          GaussGetterCopy64.Config) =
        ⟨none, ((), none), GaussGetterPrep64.rowState row S⟩ := by
    simpa only [rowProgram, copyClock, GaussGetterCopy64.run] using hrowRun
  have hcolumnRun' :
      ((advance columnProgram)^[copyClock column])
        (⟨some SourceClausePreservingBroadcast.Label.scan,
          ((), none), GaussGetterPrep64.rowState row S⟩ :
          GaussGetterCopy64.Config) =
        ⟨none, ((), none), GaussGetterPrep64.finalState row column S⟩ := by
    simpa only [columnProgram, copyClock, GaussGetterCopy64.run] using hcolumnRun
  obtain ⟨u, hu, hpair⟩ := BitMachineRawSequence.runs
    GaussGetterReset64.program rowProgram
    (.clear 0) SourceClausePreservingBroadcast.Label.scan
    ((), none) ((), none) ((), none) ((), none)
    S (GaussGetterPrep64.resetState S)
    (GaussGetterPrep64.rowState row S)
    (resetClock S) (copyClock row)
    (reset_halt S) hrowRun'
  obtain ⟨v, hv, hprep⟩ := BitMachineRawSequence.runs
    resetRowProgram columnProgram
    (BitMachineRawSequence.leftLabel (.clear 0))
    SourceClausePreservingBroadcast.Label.scan
    (((), none), ((), none)) (((), none), ((), none))
    ((), none) ((), none)
    S (GaussGetterPrep64.rowState row S)
    (GaussGetterPrep64.finalState row column S)
    u (copyClock column) hpair hcolumnRun'
  refine ⟨v, ?_, ?_⟩
  · unfold preparationClock
    omega
  · simpa only [preparationProgram] using hprep

theorem getter_initial_fixed (matrix : List Bool) (row column : Nat) :
    let c := GaussGetterIntegrated.firstFrame
      (GaussNestedGetter.firstFrame
        (GaussNestedGetter.inputForeign column)
        (CylinderContextScanStep.initial matrix row))
    c.l = some getterStart ∧ c.var = getterControl := by
  constructor <;> rfl

theorem canonical_one_fetch
    (rowPre rowSuffix cellPre cellSuffix : List (List Bool))
    (cell : List Bool) (S : Stack → List Bool)
    (hmat : S 8 = SourceListEncoding.encode
      (rowPre ++ SourceListEncoding.encode
        (cellPre ++ cell :: cellSuffix) :: rowSuffix))
    (hrow : S 15 = List.replicate rowPre.length true)
    (hcolumn : S 16 = List.replicate cellPre.length true)
    (htemp : S 63 = []) :
    let row := SourceListEncoding.encode (cellPre ++ cell :: cellSuffix)
    let matrix := SourceListEncoding.encode (rowPre ++ row :: rowSuffix)
    ∃ t ≤ preparationClock S rowPre.length cellPre.length +
        140 * (matrix.length + 1)^3 + 1,
      (run t (initial S)).l = none ∧
      (run t (initial S)).stk 38 = cell ∧
      (run t (initial S)).stk 8 = matrix := by
  dsimp only
  let matrix := SourceListEncoding.encode
    (rowPre ++ SourceListEncoding.encode
      (cellPre ++ cell :: cellSuffix) :: rowSuffix)
  let getInit := GaussGetterIntegrated.firstFrame
    (GaussNestedGetter.firstFrame
      (GaussNestedGetter.inputForeign cellPre.length)
      (CylinderContextScanStep.initial matrix rowPre.length))
  obtain ⟨tPrep, htPrep, hPrep⟩ :=
    preparation_run S matrix rowPre.length cellPre.length
      hmat hrow hcolumn htemp
  obtain ⟨tGet, htGet, hGetHalt, hCell, hMatrix⟩ :=
    GaussGetterPrep64.fetch_after_preparation
      rowPre rowSuffix cellPre cellSuffix cell S hmat
  let getCfg : GaussGetterSafe64.Config :=
    ⟨getInit.l, getInit.var,
      GaussGetterPrep64.finalState rowPre.length cellPre.length S⟩
  let getFinal := GaussGetterSafe64.run tGet getCfg
  have hFixed := getter_initial_fixed matrix rowPre.length cellPre.length
  have hGetRun :
      ((advance GaussGetterSafe64.program)^[tGet])
        (⟨some getterStart, getterControl,
          GaussGetterPrep64.finalState rowPre.length cellPre.length S⟩ :
          GaussGetterSafe64.Config) =
        ⟨none, getFinal.var, getFinal.stk⟩ := by
    rw [← hFixed.1, ← hFixed.2]
    change getFinal = ⟨none, getFinal.var, getFinal.stk⟩
    cases hfinal : getFinal with
    | mk l v T =>
        cases l with
        | none => rfl
        | some l =>
            have : getFinal.l = none := hGetHalt
            rw [hfinal] at this
            contradiction
  obtain ⟨t, ht, hfull⟩ := BitMachineRawSequence.runs
    preparationProgram GaussGetterSafe64.program
    (BitMachineRawSequence.leftLabel
      (BitMachineRawSequence.leftLabel (.clear 0)))
    getterStart
    ((((), none), ((), none)), ((), none))
    ((((), none), ((), none)), ((), none))
    getterControl getFinal.var
    S (GaussGetterPrep64.finalState rowPre.length cellPre.length S)
    getFinal.stk tPrep tGet hPrep hGetRun
  have heq : run t (initial S) =
      ⟨none,
        (((((), none), ((), none)), ((), none)), getFinal.var),
        getFinal.stk⟩ := by
    simpa [run, initial, program] using hfull
  refine ⟨t, by omega, ?_, ?_, ?_⟩
  · rw [heq]
  · rw [heq]
    exact hCell
  · rw [heq]
    exact hMatrix

#print axioms getter_initial_fixed
#print axioms reset_halt
#print axioms preparation_run
#print axioms canonical_one_fetch

end CurrentAdditive.GaussOneFetchProgram64
