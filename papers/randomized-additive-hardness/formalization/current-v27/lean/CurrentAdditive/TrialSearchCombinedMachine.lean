import CurrentAdditive.TrialSearchControllerMachine
import CurrentAdditive.TrialInputPrepMachine
import CurrentAdditive.TrialDividerMachine
import CurrentAdditive.ZeroWordTest

/-!
A single finite-control TM2 program wiring physical input preparation,
physical long division, physical zero testing, and the physical nested-search
controller. Each embedded statement is recursively mapped instruction by
instruction onto the shared twelve Boolean stacks. In particular, no local
`halt` is treated as a magic computation: it jumps to the next phase.

This file defines the composed program and its stack/register wiring. The
correspondence of entire runs to `TrialSearch.firstPassing`, and its clock,
are separate proof obligations.
-/

namespace CurrentAdditive.FieldMachineHelper.TrialSearchCombinedMachine

open Turing Turing.TM2.Stmt
open EthInapproximability.CurrentPaper.BitMachineEncoding

namespace Prep
open CurrentAdditive.FieldMachineHelper.TrialInputPrepMachine
end Prep
namespace Divide
open CurrentAdditive.FieldMachineHelper.TrialDividerMachine
end Divide
namespace Zero
open CurrentAdditive.FieldMachineHelper.ZeroWordTest
end Zero
namespace Outer
open CurrentAdditive.FieldMachineHelper.TrialSearchControllerMachine
end Outer

inductive Label where
  | prep (l : CurrentAdditive.FieldMachineHelper.TrialInputPrepMachine.Label)
  | divide (l : CurrentAdditive.FieldMachineHelper.TrialDividerMachine.Label)
  | zero (l : CurrentAdditive.FieldMachineHelper.ZeroWordTest.Label)
  | outer (l : CurrentAdditive.FieldMachineHelper.TrialSearchControllerMachine.Label)
  | clearDivisor
  deriving DecidableEq, Fintype

structure Registers where
  prep : CurrentAdditive.FieldMachineHelper.TrialInputPrepMachine.Control
  divide : CurrentAdditive.FieldMachineHelper.TrialDividerMachine.Control
  zero : CurrentAdditive.FieldMachineHelper.ZeroWordTest.Control
  outer : CurrentAdditive.FieldMachineHelper.TrialSearchControllerMachine.Control
  deriving DecidableEq, Fintype

abbrev Config := TM2.Cfg (fun _ : Fin 12 => Bool) Label Registers

def prepStack (k : Fin 7) : Fin 12 := ⟨k.val, by omega⟩

def divideStack (k : Fin 5) : Fin 12 :=
  match k.val with
  | 0 => 3
  | 1 => 4
  | 2 => 6
  | 3 => 7
  | _ => 5

def zeroStack (_ : Fin 1) : Fin 12 := 3

/-- Copy a local finite-control instruction tree into the shared machine.
Every primitive push, peek, pop, load, and branch remains one TM2 step. -/
def embedStmt {K L V : Type*} (stack : K → Fin 12)
    (label : L → Label) (next : Label)
    (get : Registers → V) (put : Registers → V → Registers)
    (finish : Registers → Registers) :
    TM2.Stmt (fun _ : K => Bool) L V →
      TM2.Stmt (fun _ : Fin 12 => Bool) Label Registers
  | .push k f q => .push (stack k) (fun r => f (get r))
      (embedStmt stack label next get put finish q)
  | .peek k f q => .peek (stack k) (fun r b => put r (f (get r) b))
      (embedStmt stack label next get put finish q)
  | .pop k f q => .pop (stack k) (fun r b => put r (f (get r) b))
      (embedStmt stack label next get put finish q)
  | .load f q => .load (fun r => put r (f (get r)))
      (embedStmt stack label next get put finish q)
  | .branch f q s => .branch (fun r => f (get r))
      (embedStmt stack label next get put finish q)
      (embedStmt stack label next get put finish s)
  | .goto f => .goto (fun r => label (f (get r)))
  | .halt => .load finish (.goto (fun _ => next))

def program : Label → TM2.Stmt (fun _ : Fin 12 => Bool) Label Registers
  | .prep l => embedStmt prepStack Label.prep (.divide .next)
      (fun r => r.prep) (fun r v => {r with prep := v})
      (fun r => {r with divide := (false, none, none)})
      (CurrentAdditive.FieldMachineHelper.TrialInputPrepMachine.program l)
  | .divide l => embedStmt divideStack Label.divide (.zero .scan)
      (fun r => r.divide) (fun r v => {r with divide := v})
      (fun r => {r with zero := (false, none)})
      (CurrentAdditive.FieldMachineHelper.TrialDividerMachine.program l)
  | .zero l => embedStmt zeroStack Label.zero .clearDivisor
      (fun r => r.zero) (fun r v => {r with zero := v})
      id (CurrentAdditive.FieldMachineHelper.ZeroWordTest.program l)
  | .outer .success => .halt
  | .outer .exhausted => .halt
  | .outer l => embedStmt id Label.outer (.prep .shiftScan)
      (fun r => r.outer) (fun r v => {r with outer := v})
      (fun r => {r with prep := none})
      (CurrentAdditive.FieldMachineHelper.TrialSearchControllerMachine.program l)
  | .clearDivisor => .pop 4 (fun r b => {r with outer := (r.zero.1, r.outer.2.1, b)})
      (.branch (fun r => r.outer.2.2.isSome)
        (.goto (fun _ => .clearDivisor))
        (.goto (fun _ => .outer .afterTest)))

def run (t : Nat) (q : Config) : Config := ((advance program)^[t]) q

theorem run_add (t u : Nat) (q : Config) :
    run (t + u) q = run u (run t q) := by
  rw [Nat.add_comm t u]
  simp only [run, Function.iterate_add_apply]

#print axioms run_add

end CurrentAdditive.FieldMachineHelper.TrialSearchCombinedMachine
