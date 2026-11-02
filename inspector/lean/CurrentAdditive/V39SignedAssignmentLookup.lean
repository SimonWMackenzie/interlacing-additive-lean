import EthInapproximability.CurrentPaper.ProtocolBitLookup
import EthInapproximability.CurrentPaper.BitMachineSubroutine
import EthInapproximability.CurrentPaper.EncodedCNF

/-! A physical literal-evaluation primitive: remember the sign in finite
control, run the admitted unary-index lookup, and negate its answer when
the sign is negative. This does not yet assemble the full CNF evaluator. -/

namespace CurrentAdditive.V39SignedAssignmentLookup

open EthInapproximability.CurrentPaper
open Turing TM2.Stmt BitMachineEncoding BitMachineComposition

abbrev Local := ProtocolBitLookup.bitMachine
inductive Outer where | start | finish
  deriving DecidableEq, Fintype

abbrev Stack := Fin Local.stackCount ⊕ Unit
abbrev Label := Fin Local.labelCount ⊕ Outer
abbrev Control := Fin Local.controlCount × Bool

def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .inl l => liftStmt (some Outer.finish) (Local.program l)
  | .inr .start =>
      pop (.inl Local.input) (fun _ b => (Local.initial, b.getD false))
        (goto (fun _ => .inl Local.start))
  | .inr .finish =>
      pop (.inl Local.output) (fun v b =>
        (ProtocolBitLookup.controlCode (b.getD false, false), v.2))
        (push (.inr ()) (fun v =>
          if v.2 then (ProtocolBitLookup.controlCode.symm v.1).1
          else !(ProtocolBitLookup.controlCode.symm v.1).1) halt)

noncomputable def machine : BitMachine.Machine :=
  ofFinite (.inl Local.input : Stack) (.inr ()) (.inr Outer.start)
    ((Local.initial, false) : Control) program

def embedded (sign : Bool) (c : Local.Config) :
    TM2.Cfg (fun _ : Stack => Bool) Label Control :=
  liftCfg (some Outer.finish) sign (fun _ : Unit => []) c

theorem start_step (sign : Bool) (word : List Bool) :
    advance program (rawInit (.inl Local.input : Stack) (.inr Outer.start)
      ((Local.initial, false) : Control) (sign :: word)) =
      embedded sign (Local.init word) := by
  simp only [advance, rawInit, TM2.step, Option.getD_some,
    program, TM2.stepAux, List.head?_cons, List.tail_cons, Option.getD_some,
    embedded, liftCfg, BitMachine.Machine.init]
  congr 1
  funext k
  cases k with
  | inl k => fin_cases k <;> rfl
  | inr k => cases k; rfl

theorem finish_step (sign bit : Bool) (c : Local.Config)
    (hhalt : c.l = none) (houtput : c.stk Local.output = [bit]) :
    (advance program (embedded sign c)).l = none ∧
    (advance program (embedded sign c)).stk (.inr ()) =
      [if sign then bit else !bit] := by
  simp only [advance, embedded, liftCfg, hhalt, Option.map_none,
    Option.map_some, Option.getD_some, TM2.step, program, TM2.stepAux,
    Sum.elim_inl, Sum.elim_inr, houtput, List.head?_cons, List.tail_cons,
    Option.getD_some, Equiv.symm_apply_apply]
  constructor
  · trivial
  · rfl

/-- Sign, unary index, delimiter, literal assignment. The same machine
works at every index and assignment length, with all literal stack
transfers charged. Out-of-range queries use the admitted false default. -/
theorem outputs (sign : Bool) (i : ℕ) (assignment : List Bool) :
    machine.OutputsWithin (sign :: ProtocolBitLookup.encodeInput i assignment)
      [if sign then assignment[i]?.getD false else !(assignment[i]?.getD false)]
      (2 * (sign :: ProtocolBitLookup.encodeInput i assignment).length + 3) := by
  let word := ProtocolBitLookup.encodeInput i assignment
  let bound := 2 * word.length + 3
  have hr := ProtocolBitLookup.bitMachine_outputs i assignment
  have hfinal := BitMachine.outputsWithin_at_bound Local hr
  obtain ⟨t, ht, he⟩ := BitMachineSubroutine.lift_outputs
    Local.program program (some Outer.finish) (fun _ => rfl)
    sign (fun _ : Unit => []) (Local.init word) bound hfinal.1
  have hfinish := finish_step sign (assignment[i]?.getD false)
    (Local.run bound (Local.init word)) hfinal.1 hfinal.2
  have hstart := start_step sign word
  have hrun : ((advance program)^[t + 2])
      (rawInit (.inl Local.input : Stack) (.inr Outer.start)
        ((Local.initial, false) : Control) (sign :: word)) =
      advance program (embedded sign (Local.run bound (Local.init word))) := by
    rw [show t + 2 = 1 + t + 1 by omega, Function.iterate_add_apply,
      Function.iterate_add_apply]
    simp only [Function.iterate_one, hstart]
    change advance program (((advance program)^[t])
      (liftCfg (some Outer.finish) sign (fun _ : Unit => []) (Local.init word))) = _
    rw [he]
    rfl
  apply outputsWithin_of_raw_run (.inl Local.input : Stack) (.inr ())
    (.inr Outer.start) ((Local.initial, false) : Control) program
    (sign :: word) _ (t + 2) _ (by
      dsimp [bound, word] at ht ⊢
      omega)
  · rw [hrun]
    exact hfinish.1
  · rw [hrun]
    exact hfinish.2

/-- The returned bit is exactly the manuscript's literal semantics. -/
theorem outputs_literal (literal : EncodedCNF.Literal) (assignment : List Bool) :
    machine.OutputsWithin
      (literal.positive :: ProtocolBitLookup.encodeInput literal.variable assignment)
      [literal.eval assignment]
      (2 * (literal.positive :: ProtocolBitLookup.encodeInput literal.variable assignment).length + 3) := by
  simpa only [EncodedCNF.Literal.eval, List.getD_eq_getElem?_getD] using
    outputs literal.positive literal.variable assignment

#print axioms outputs
#print axioms outputs_literal

end CurrentAdditive.V39SignedAssignmentLookup
