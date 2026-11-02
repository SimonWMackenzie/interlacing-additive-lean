import CurrentAdditive.GaussPivotReverse32
import CurrentAdditive.GaussFlagSearch
import EthInapproximability.CurrentPaper.BitMachineInline
import EthInapproximability.CurrentPaper.BitMachineStackRun

/-! One fixed physical Fin32 controller: scan typed rows, reverse the
produced flags, and select the first nonzero row at or after the saved
threshold. The run theorem is in a separate module. -/

namespace CurrentAdditive.GaussPivotSearchController

noncomputable section

open Turing Turing.TM2.Stmt
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding

abbrev Stack := Fin 32
abbrev ScanLabel := CurrentAdditive.LargeContextListScheduler.Label
  GaussRowZeroCallback.Label
abbrev ScanControl := CurrentAdditive.LargeContextListScheduler.Control
  GaussRowZeroCallback.Control

noncomputable instance : DecidableEq ScanLabel := Classical.decEq _
noncomputable instance : DecidableEq ScanControl := Classical.decEq _

def selectSlot : Fin 5 ↪ Stack where
  toFun j := ![15, 30, 19, 20, 31] j
  inj' := by intro a b h; fin_cases a <;> fin_cases b <;> simp_all

inductive Label where
  | scan (l : ScanLabel)
  | reverse (l : GaussPivotReverse32.Label)
  | choose (l : GaussFlagSearch.Label)
  | toReverse | toChoose | done
  deriving Fintype

inductive Control where
  | scan (v : ScanControl)
  | reverse (v : GaussPivotReverse32.Control)
  | choose (v : GaussFlagSearch.Control)
  deriving Fintype

noncomputable instance : DecidableEq Label := Classical.decEq _
noncomputable instance : DecidableEq Control := Classical.decEq _

abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

def readScan : Control → ScanControl
  | .scan v => v
  | _ => CurrentAdditive.LargeContextListScheduler.getterControl
      (GaussRowZeroCallback.bControl ((), none))
        (CylinderContextScanStep.copyControl ((), none))

def readReverse : Control → GaussPivotReverse32.Control
  | .reverse v => v
  | _ => none

def readChoose : Control → GaussFlagSearch.Control
  | .choose v => v
  | _ => (none, none)

def scanProgram : ScanLabel →
    TM2.Stmt (fun _ : Stack => Bool) ScanLabel ScanControl :=
  CurrentAdditive.LargeContextListScheduler.program
    GaussRowZeroCallback.program (GaussRowZeroCallback.bLabel .scan)
      (GaussRowZeroCallback.bControl ((), none))

def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .scan l => BitMachineInline.stmt Label.scan Control.scan readScan
      (some .toReverse) (scanProgram l)
  | .reverse l => BitMachineInline.stmt Label.reverse Control.reverse
      readReverse (some .toChoose) (GaussPivotReverse32.program l)
  | .choose l => BitMachineInline.stmt Label.choose Control.choose
      readChoose (some .done)
      (BitMachineStackEmbedding.stackStmt selectSlot
        (GaussFlagSearch.program l))
  | .toReverse => .load (fun _ => .reverse none)
      (.goto (fun _ => .reverse .scan))
  | .toChoose => .load (fun _ => .choose (none, none))
      (.goto (fun _ => .choose .skip))
  | .done => .halt

def run (t : Nat) (c : Config) : Config := ((advance program)^[t]) c

def initial (S : Stack → List Bool) : Config :=
  ⟨some (.scan (.inr (.inr .check))),
   .scan (CurrentAdditive.LargeContextListScheduler.getterControl
     (GaussRowZeroCallback.bControl ((), none))
       (CylinderContextScanStep.copyControl ((), none))), S⟩

theorem finite_program : Finite Stack ∧ Finite Label ∧ Finite Control :=
  ⟨inferInstance, inferInstance, inferInstance⟩

end
end CurrentAdditive.GaussPivotSearchController
