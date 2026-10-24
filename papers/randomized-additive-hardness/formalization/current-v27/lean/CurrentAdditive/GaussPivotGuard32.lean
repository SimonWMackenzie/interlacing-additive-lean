import CurrentAdditive.GaussPivotPrepClock
import EthInapproximability.CurrentPaper.EntryUnaryCompare
import EthInapproximability.CurrentPaper.SourceClausePreservingBroadcast

/-! A fixed unary terminal guard for a prepared Gauss state. It copies r and m
to scratch, compares r < m, and consumes the verdict into the next label. -/

namespace CurrentAdditive.GaussPivotGuard32

open EthInapproximability.CurrentPaper
open Turing Turing.TM2.Stmt BitMachineEncoding

abbrev Stack := Fin 32

inductive Control where
  | copy (v : Unit × Option Bool)
  | compare (v : EntryUnaryCompare.CV)
  | choose (v : Option Bool)
  deriving DecidableEq, Fintype

inductive Label where
  | rowCopy (l : SourceClausePreservingBroadcast.Label)
  | toCountCopy
  | countCopy (l : SourceClausePreservingBroadcast.Label)
  | toCompare
  | compare (l : EntryUnaryCompare.CL)
  | choose | active | terminal
  deriving DecidableEq, Fintype

abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

def readCopy : Control → Unit × Option Bool
  | .copy v => v
  | _ => ((), none)
def readCompare : Control → EntryUnaryCompare.CV
  | .compare v => v
  | _ => (none, none)

def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .rowCopy l => BitMachineInline.stmt Label.rowCopy Control.copy readCopy
      (some .toCountCopy)
      (SourceClausePreservingBroadcast.program (30 : Stack) 29 [20] l)
  | .toCountCopy => .load (fun _ => .copy ((), none))
      (.goto (fun _ => .countCopy .scan))
  | .countCopy l => BitMachineInline.stmt Label.countCopy Control.copy readCopy
      (some .toCompare)
      (SourceClausePreservingBroadcast.program (13 : Stack) 29 [21] l)
  | .toCompare => .load (fun _ => .compare (none, none))
      (.goto (fun _ => .compare .loop))
  | .compare l => BitMachineInline.stmt Label.compare Control.compare readCompare
      (some .choose)
      (EntryUnaryCompare.program (20 : Stack) 21 22 true false false l)
  | .choose => .pop 22 (fun _ bit => .choose bit)
      (.branch (fun v => match v with
        | .choose (some true) => true
        | _ => false)
        (.goto (fun _ => .active))
        (.goto (fun _ => .terminal)))
  | .active => .halt
  | .terminal => .halt

def run (t : Nat) (c : Config) : Config := ((advance program)^[t]) c

def initial (S : Stack → List Bool) : Config :=
  ⟨some (.rowCopy .scan), .copy ((), none), S⟩

theorem finite_program : Finite Stack ∧ Finite Label ∧ Finite Control :=
  ⟨inferInstance, inferInstance, inferInstance⟩

theorem run_add {c c' : Config} {t : Nat} (h : run t c = c') (u : Nat) :
    run (t + u) c = run u c' := by
  rw [Nat.add_comm, run, Function.iterate_add_apply]
  exact congrArg (run u) h

def afterRow (S : Stack → List Bool) : Stack → List Bool :=
  SourceClausePreservingBroadcast.result 30 29 [20] (S 30) S

def afterCount (S : Stack → List Bool) : Stack → List Bool :=
  SourceClausePreservingBroadcast.result 13 29 [21] ((afterRow S) 13)
    (afterRow S)

def afterCompare (S : Stack → List Bool) (r m : Nat) : Stack → List Bool :=
  Function.update (Function.update (Function.update (afterCount S) 20 []) 21 [])
    22 [decide (r < m)]

def afterChoose (S : Stack → List Bool) (r m : Nat) : Stack → List Bool :=
  Function.update (afterCompare S r m) 22 []

theorem to_count_step (S : Stack → List Bool) (v : Control) :
    run 1 ⟨some .toCountCopy, v, S⟩ =
      ⟨some (.countCopy .scan), .copy ((), none), S⟩ := rfl

theorem to_compare_step (S : Stack → List Bool) (v : Control) :
    run 1 ⟨some .toCompare, v, S⟩ =
      ⟨some (.compare .loop), .compare (none, none), S⟩ := rfl

theorem choose_step (S : Stack → List Bool) (b : Bool) (v : Control)
    (h : S 22 = [b]) :
    run 1 ⟨some .choose, v, S⟩ =
      ⟨some (if b then .active else .terminal), .choose (some b),
        Function.update S 22 []⟩ := by
  cases b <;> simp [run, program, advance, TM2.step, TM2.stepAux, h]

end CurrentAdditive.GaussPivotGuard32
