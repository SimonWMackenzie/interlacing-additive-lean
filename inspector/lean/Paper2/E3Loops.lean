import Paper2.A4KofLoops

/-!
# Paper A (lock v12), lane `owner:a-eth-3`, segment 1 (obstacle B2): two tape-independent field machines

Two FIXED finite machines built only from the admitted fixed statements of `Paper2/A4Loops.lean`
(`moveStmt`, `parseStmt`, `emitStmt`, `pushFalseStmt`, `.halt`) and the admitted `dupStmt` of
`Paper2/A4KofLoops.lean`, with exact iterated-step runs (admitted `move_loop`, `parse_loop`,
`emit_loop`, `dup_loop`, `pushFalse_step`, `halt_step`, `outputsWithin_of_raw_run`):

* `RawDup.machine`: raw `x ↦ pair x (pair x [])` (= `field x ++ field x`), in `5|x| + 8` steps;
* `Fst.machine`: `pair a r ↦ a`, in `2|a| + 3` steps; the raw rest `r` is never read
  (it stays on the input stack; the output stack is a separate stack).

Both clocks are independent of any unread suffix. Every step is one `TM2.step` of a literal
statement; nothing is inserted; the machines start from `Machine.init`. No ledger row is closed.
-/

namespace Paper2.AEth3

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open Paper2.Unit4Shell.Loops
open Paper2.Unit4Shell.KofLoops

abbrev Control := Option Bool × Unit

namespace RawDup

inductive RL
  | r1 | r2 | r3 | r4 | r5 | r6 | r7 | done
  deriving DecidableEq, Fintype

abbrev Stack := Fin 4

def program : RL → TM2.Stmt (fun _ : Stack => Bool) RL Control
  | .r1 => moveStmt 0 1 .r1 .r2
  | .r2 => moveStmt 1 2 .r2 .r3
  | .r3 => dupStmt 2 1 3 .r3 .r4
  | .r4 => pushFalseStmt 0 .r5
  | .r5 => emitStmt 1 0 .r5 .r6
  | .r6 => pushFalseStmt 0 .r7
  | .r7 => emitStmt 3 0 .r7 .done
  | .done => .halt

noncomputable def machine : BitMachine.Machine :=
  ofFinite (0 : Stack) (0 : Stack) RL.r1 ((none, ()) : Control) program

/-- **Raw duplication.** On the raw word `x` the fixed machine prints `pair x (pair x [])`
within `5|x| + 8` steps. -/
theorem machine_outputs (x : List Bool) :
    machine.OutputsWithin x
      (EncodedComplexity.pair x (EncodedComplexity.pair x [])) (5 * x.length + 8) := by
  let S0 : Stack → List Bool := fun j => if j = 0 then x else []
  have e1 := move_loop program (0 : Stack) 1 RL.r1 RL.r2 (by decide) rfl x S0 none ()
    (by simp [S0])
  set S1 := Function.update (Function.update S0 1 (x.reverse ++ S0 1)) 0 [] with hS1
  have h1 : S1 1 = x.reverse := by simp [hS1, S0]
  have e2 := move_loop program (1 : Stack) 2 RL.r2 RL.r3 (by decide) rfl x.reverse S1
    none () h1
  rw [List.length_reverse] at e2
  set S2 := Function.update (Function.update S1 2 (x.reverse.reverse ++ S1 2)) 1 [] with hS2
  have h2 : S2 2 = x := by simp [hS2, hS1, S0]
  have e3 := dup_loop program (2 : Stack) 1 3 RL.r3 RL.r4 (by decide) (by decide) (by decide)
    rfl x S2 none () h2
  set S3 := Function.update (Function.update (Function.update S2 1 (x.reverse ++ S2 1)) 3
    (x.reverse ++ S2 3)) 2 [] with hS3
  have e4 := pushFalse_step program (0 : Stack) RL.r4 RL.r5 rfl (none, ()) S3
  set S4 := Function.update S3 0 (false :: S3 0) with hS4
  have h4 : S4 1 = x.reverse := by simp [hS4, hS3, hS2, hS1, S0]
  have e5 := emit_loop program (1 : Stack) 0 RL.r5 RL.r6 (by decide) rfl x.reverse S4
    none () h4
  rw [List.length_reverse] at e5
  set S5 := Function.update (Function.update S4 0 (x.reverse.foldl emitFold (S4 0))) 1 []
    with hS5
  have h50 : S5 0 = EncodedCommunication.field x ++ [] := by
    have : S4 0 = false :: [] := by simp [hS4, hS3, hS2, hS1]
    simp only [hS5, Function.update_of_ne (by decide : (0 : Stack) ≠ 1), Function.update_self,
      this]
    exact emit_reverse_field x []
  have e6 := pushFalse_step program (0 : Stack) RL.r6 RL.r7 rfl (none, ()) S5
  set S6 := Function.update S5 0 (false :: S5 0) with hS6
  have h6 : S6 3 = x.reverse := by simp [hS6, hS5, hS4, hS3, hS2, hS1, S0]
  have e7 := emit_loop program (3 : Stack) 0 RL.r7 RL.done (by decide) rfl x.reverse S6
    none () h6
  rw [List.length_reverse] at e7
  set S7 := Function.update (Function.update S6 0 (x.reverse.foldl emitFold (S6 0))) 3 []
    with hS7
  have h70 : S7 0 = EncodedCommunication.field x ++ (EncodedCommunication.field x ++ []) := by
    have : S6 0 = false :: (EncodedCommunication.field x ++ []) := by
      simp only [hS6, Function.update_self, h50]
    simp only [hS7, Function.update_of_ne (by decide : (0 : Stack) ≠ 3), Function.update_self,
      this]
    exact emit_reverse_field x _
  have e8 := halt_step program RL.done rfl (none, ()) S7
  have r := iter_chain (iter_chain (iter_chain (iter_chain (iter_chain (iter_chain
    (iter_chain e1 e2) e3) (show (advance program)^[1] _ = _ from e4)) e5)
    (show (advance program)^[1] _ = _ from e6)) e7)
    (show (advance program)^[1] _ = _ from e8)
  have hraw : rawInit (0 : Stack) RL.r1 ((none, ()) : Control) x =
      ⟨some RL.r1, (none, ()), S0⟩ := rfl
  refine outputsWithin_of_raw_run (0 : Stack) (0 : Stack) RL.r1 ((none, ()) : Control)
    program x (EncodedComplexity.pair x (EncodedComplexity.pair x []))
    (x.length + 1 + (x.length + 1) + (x.length + 1) + 1 + (x.length + 1) + 1 +
      (x.length + 1) + 1) _ ?_ ?_ ?_
  · omega
  · rw [hraw, r]
  · rw [hraw, r]
    simp only [EncodedComplexity.pair]
    exact h70

end RawDup

namespace Fst

inductive FL
  | f1 | f2 | done
  deriving DecidableEq, Fintype

abbrev Stack := Fin 3

def program : FL → TM2.Stmt (fun _ : Stack => Bool) FL Control
  | .f1 => parseStmt 0 1 .f1 .f2
  | .f2 => moveStmt 1 2 .f2 .done
  | .done => .halt

/-- Input stack `0`, output stack `2`. -/
noncomputable def machine : BitMachine.Machine :=
  ofFinite (0 : Stack) (2 : Stack) FL.f1 ((none, ()) : Control) program

/-- **First projection.** On `pair a r` the fixed machine prints `a` within `2|a| + 3` steps;
the rest `r` is never read. -/
theorem machine_outputs (a r : List Bool) :
    machine.OutputsWithin (EncodedComplexity.pair a r) a (2 * a.length + 3) := by
  let S0 : Stack → List Bool := fun j => if j = 0 then EncodedComplexity.pair a r else []
  have e1 := parse_loop program (0 : Stack) 1 FL.f1 FL.f2 (by decide) rfl a r S0 none ()
    (by simp [S0, EncodedComplexity.pair])
  set S1 := Function.update (Function.update S0 1 (a.reverse ++ S0 1)) 0 r with hS1
  have h1 : S1 1 = a.reverse := by simp [hS1, S0]
  have e2 := move_loop program (1 : Stack) 2 FL.f2 FL.done (by decide) rfl a.reverse S1
    (some false) () h1
  rw [List.length_reverse] at e2
  set S2 := Function.update (Function.update S1 2 (a.reverse.reverse ++ S1 2)) 1 [] with hS2
  have h2 : S2 2 = a := by simp [hS2, hS1, S0]
  have e3 := halt_step program FL.done rfl (none, ()) S2
  have hrun := iter_chain (iter_chain e1 e2) (show (advance program)^[1] _ = _ from e3)
  have hraw : rawInit (0 : Stack) FL.f1 ((none, ()) : Control) (EncodedComplexity.pair a r) =
      ⟨some FL.f1, (none, ()), S0⟩ := rfl
  refine outputsWithin_of_raw_run (0 : Stack) (2 : Stack) FL.f1 ((none, ()) : Control)
    program (EncodedComplexity.pair a r) a (a.length + 1 + (a.length + 1) + 1) _ ?_ ?_ ?_
  · omega
  · rw [hraw, hrun]
  · rw [hraw, hrun]
    exact h2

end Fst

end Paper2.AEth3

#print axioms Paper2.AEth3.RawDup.machine_outputs
#print axioms Paper2.AEth3.Fst.machine_outputs
