import EthInapproximability.CurrentPaper.SourceCSPInputGuardedPoly

/-!
# Physical collection of the two raw-input guard statuses

The fixed-header checker and bounded-constraint checker produce separate
literal Boolean bits. This constant-size finite program consumes those bits
and pushes their conjunction into a disjoint status cell, preserving the
constraint checker's unary count tail for later row iteration.
-/

namespace EthInapproximability.CurrentPaper.SourceCSPGuardStatus

open Turing BitMachineEncoding

abbrev Stack := SourceCSPInputFrame.Stack
abbrev Control := Option Bool × Option Bool

def headerSlot : Stack := SourceCSPInputGuarded.FlagSlot
def guardSlot : Stack := .inr 6
def statusSlot : Stack := .inr 1

def program (_ : Unit) : TM2.Stmt (fun _ : Stack => Bool) Unit Control :=
  .pop headerSlot (fun _ b => (b, none))
    (.pop guardSlot (fun v b => (v.1, b))
      (.push statusSlot (fun v =>
        v.1 == some true && v.2 == some true) .halt))

theorem collect_step (before : Stack → List Bool) (h g : Bool)
    (unary : List Bool)
    (hh : before headerSlot = [h])
    (hg : before guardSlot = g :: unary) :
    let c := advance program
      (⟨some (), (none, none), before⟩ :
        TM2.Cfg (fun _ : Stack => Bool) Unit Control)
    c.l = none ∧ c.stk statusSlot = (h && g) :: before statusSlot ∧
      c.stk guardSlot = unary ∧ c.stk headerSlot = [] := by
  change before SourceCSPInputGuarded.FlagSlot = [h] at hh
  change before (.inr 6) = g :: unary at hg
  simp [advance, TM2.step, TM2.stepAux, program,
    headerSlot, guardSlot, statusSlot, hh, hg]

end EthInapproximability.CurrentPaper.SourceCSPGuardStatus
