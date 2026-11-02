import CurrentAdditive.GaussStepFields32

/-! Exact inlining lemmas for each fixed Fin32 Gauss field-preparation phase. -/

namespace CurrentAdditive.GaussStepPhaseLift32

noncomputable section

open EthInapproximability.CurrentPaper
open Turing BitMachineEncoding
open CurrentAdditive.GaussStepFields32

theorem parse_lift (terminal : Bool) (c : GaussParsedState32.Config)
    (t : Nat) (hh : (GaussParsedState32.run t c).l = none) :
    ∃ u ≤ t,
      run u (BitMachineInline.cfg (Label.parse terminal) eParse
        (some (.afterParse terminal)) c) =
      BitMachineInline.cfg (Label.parse terminal) eParse
        (some (.afterParse terminal)) (GaussParsedState32.run t c) := by
  exact BitMachineInline.outputs (Label.parse terminal) eParse
    Control.parse (by intro v; rfl) (some (.afterParse terminal))
    GaussParsedState32.program program (by intro l; rfl) c t hh

theorem tag_lift
    (c : TM2.Cfg (fun _ : Stack => Bool)
      SourceClausePreservingBroadcast.Label GaussBranchFields32.Control)
    (t : Nat)
    (hh : (((advance (SourceClausePreservingBroadcast.program
      (20 : Stack) 31 [25]))^[t]) c).l = none) :
    ∃ u ≤ t,
      run u (BitMachineInline.cfg Label.saveTag eBranch
        (some .afterSaveTag) c) =
      BitMachineInline.cfg Label.saveTag eBranch
        (some .afterSaveTag)
        (((advance (SourceClausePreservingBroadcast.program
          (20 : Stack) 31 [25]))^[t]) c) := by
  exact BitMachineInline.outputs Label.saveTag eBranch
    Control.branch (by intro v; rfl) (some .afterSaveTag)
    (SourceClausePreservingBroadcast.program (20 : Stack) 31 [25])
    program (by intro l; rfl) c t hh

theorem branch_lift (c : GaussBranchFields32.Config)
    (t : Nat) (hh : (GaussBranchFields32.run t c).l = none) :
    ∃ u ≤ t,
      run u (BitMachineInline.cfg Label.branch eBranch
        (some .afterBranch) c) =
      BitMachineInline.cfg Label.branch eBranch
        (some .afterBranch) (GaussBranchFields32.run t c) := by
  exact BitMachineInline.outputs Label.branch eBranch
    Control.branch (by intro v; rfl) (some .afterBranch)
    GaussBranchFields32.program program (by intro l; rfl) c t hh

theorem split_lift (c : GaussPivotBodySplit32.Config)
    (t : Nat) (hh : (GaussPivotBodySplit32.run t c).l = none) :
    ∃ u ≤ t,
      run u (BitMachineInline.cfg Label.split eSplit
        (some .afterSplit) c) =
      BitMachineInline.cfg Label.split eSplit
        (some .afterSplit) (GaussPivotBodySplit32.run t c) := by
  exact BitMachineInline.outputs Label.split eSplit
    Control.split (by intro v; rfl) (some .afterSplit)
    GaussPivotBodySplit32.program program (by intro l; rfl) c t hh

theorem pair_lift (c : GaussPivotPairEmit32.Config)
    (t : Nat) (hh : (GaussPivotPairEmit32.run t c).l = none) :
    ∃ u ≤ t,
      run u (BitMachineInline.cfg Label.pair ePair
        (some .afterPair) c) =
      BitMachineInline.cfg Label.pair ePair
        (some .afterPair) (GaussPivotPairEmit32.run t c) := by
  exact BitMachineInline.outputs Label.pair ePair
    Control.pair (by intro v; rfl) (some .afterPair)
    GaussPivotPairEmit32.program program (by intro l; rfl) c t hh

theorem payload_lift (c : GaussPivotPayload32.Config)
    (t : Nat) (hh : (GaussPivotPayload32.run t c).l = none) :
    ∃ u ≤ t,
      run u (BitMachineInline.cfg Label.payload ePayload
        (some .afterPayload) c) =
      BitMachineInline.cfg Label.payload ePayload
        (some .afterPayload) (GaussPivotPayload32.run t c) := by
  exact BitMachineInline.outputs Label.payload ePayload
    Control.payload (by intro v; rfl) (some .afterPayload)
    GaussPivotPayload32.program program (by intro l; rfl) c t hh

theorem append_lift (c : GaussPivotAppend32.Config)
    (t : Nat) (hh : (GaussPivotAppend32.run t c).l = none) :
    ∃ u ≤ t,
      run u (BitMachineInline.cfg Label.append eAppend
        (some .afterAppend) c) =
      BitMachineInline.cfg Label.append eAppend
        (some .afterAppend) (GaussPivotAppend32.run t c) := by
  exact BitMachineInline.outputs Label.append eAppend
    Control.append (by intro v; rfl) (some .afterAppend)
    GaussPivotAppend32.program program (by intro l; rfl) c t hh

theorem reset_writer_lift (c : GaussWorkerReset32.Config)
    (t : Nat) (hh : (GaussWorkerReset32.run t c).l = none) :
    ∃ u ≤ t,
      run u (BitMachineInline.cfg Label.resetWriter eResetWriter
        (some .afterResetWriter) c) =
      BitMachineInline.cfg Label.resetWriter eResetWriter
        (some .afterResetWriter) (GaussWorkerReset32.run t c) := by
  exact BitMachineInline.outputs Label.resetWriter eResetWriter
    Control.resetWriter (by intro v; rfl) (some .afterResetWriter)
    GaussWorkerReset32.program program (by intro l; rfl) c t hh

theorem header_lift (c : GaussPivotHeader32.Config)
    (t : Nat) (hh : (GaussPivotHeader32.run t c).l = none) :
    ∃ u ≤ t,
      run u (BitMachineInline.cfg Label.header eHeader
        (some .afterHeader) c) =
      BitMachineInline.cfg Label.header eHeader
        (some .afterHeader) (GaussPivotHeader32.run t c) := by
  exact BitMachineInline.outputs Label.header eHeader
    Control.header (by intro v; rfl) (some .afterHeader)
    GaussPivotHeader32.program program (by intro l; rfl) c t hh

theorem join_lift (c : GaussPivotJoin32.Config)
    (t : Nat) (hh : (GaussPivotJoin32.run t c).l = none) :
    ∃ u ≤ t,
      run u (BitMachineInline.cfg Label.join eJoin
        (some .afterJoin) c) =
      BitMachineInline.cfg Label.join eJoin
        (some .afterJoin) (GaussPivotJoin32.run t c) := by
  exact BitMachineInline.outputs Label.join eJoin
    Control.join (by intro v; rfl) (some .afterJoin)
    GaussPivotJoin32.program program (by intro l; rfl) c t hh

theorem reset_assembler_lift (c : GaussAssemblerReset32.Config)
    (t : Nat) (hh : (GaussAssemblerReset32.run t c).l = none) :
    ∃ u ≤ t,
      run u (BitMachineInline.cfg Label.resetAssembler eResetAssembler
        (some .afterResetAssembler) c) =
      BitMachineInline.cfg Label.resetAssembler eResetAssembler
        (some .afterResetAssembler) (GaussAssemblerReset32.run t c) := by
  exact BitMachineInline.outputs Label.resetAssembler eResetAssembler
    Control.resetAssembler (by intro v; rfl) (some .afterResetAssembler)
    GaussAssemblerReset32.program program (by intro l; rfl) c t hh

#print axioms parse_lift
#print axioms tag_lift
#print axioms branch_lift
#print axioms split_lift
#print axioms pair_lift
#print axioms payload_lift
#print axioms append_lift
#print axioms reset_writer_lift
#print axioms header_lift
#print axioms join_lift
#print axioms reset_assembler_lift

end
end CurrentAdditive.GaussStepPhaseLift32
