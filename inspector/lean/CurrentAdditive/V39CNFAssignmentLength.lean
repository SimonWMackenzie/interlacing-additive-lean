import EthInapproximability.CurrentPaper.ProtocolWordField
import EthInapproximability.CurrentPaper.BitMachineSubroutine
import CurrentAdditive.V39CNFWitnessBoundary

/-! Physical all-input assignment-length checking. Parse the unrestricted
outer pair, then compare its witness length with the unary variable-count
prefix. No unbounded natural is stored in finite control. -/

namespace CurrentAdditive.V39CNFAssignmentLength

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000

open EthInapproximability.CurrentPaper
open Turing TM2.Stmt BitMachineEncoding BitMachineComposition
open EncodedCommunication

inductive Outer where | ready | count
  deriving DecidableEq, Fintype
abbrev Stack := Fin 3 ⊕ Unit
abbrev Label := ProtocolWordField.Label ⊕ Outer
abbrev Control := ProtocolWordField.Control × Unit

def last (v : Control) : Option Bool := v.1.2
def setLast (v : Control) (b : Option Bool) : Control := ((v.1.1, b), ())
def output (b : Control → Bool) : TM2.Stmt (fun _ : Stack => Bool) Label Control :=
  push (.inr ()) b halt
def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .inl l => liftStmt (some Outer.ready) (ProtocolWordField.program l)
  | .inr .ready => pop (.inl 2) setLast
      (branch (fun v => (last v).getD false)
        (goto (fun _ => .inr .count)) (output (fun _ => false)))
  | .inr .count => pop (.inl 2) setLast
      (branch (fun v => (last v).isSome)
        (branch (fun v => (last v).getD false)
          (pop (.inl 0) setLast (branch (fun v => (last v).isSome)
            (goto (fun _ => .inr .count)) (output (fun _ => false))))
          (pop (.inl 0) setLast (output (fun v => !(last v).isSome))))
        (output (fun _ => false)))

noncomputable def machine : BitMachine.Machine :=
  ofFinite (.inl 0 : Stack) (.inr ()) (.inl ProtocolWordField.Label.scan)
    (((none, none), ()) : Control) program

def prefixMatch : List Bool → List Bool → Bool
  | [], _ => false
  | false :: _, assignment => assignment.isEmpty
  | true :: _, [] => false
  | true :: word, _ :: assignment => prefixMatch word assignment

def result (code : List Bool) : Bool :=
  match readField code with
  | none => false
  | some (word, assignment) => prefixMatch word assignment

def cfg (l : Option Label) (v : Control) (word assignment : List Bool) :
    TM2.Cfg (fun _ : Stack => Bool) Label Control :=
  ⟨l, v, Sum.elim (ProtocolWordField.stackContents assignment [] word) (fun _ => [])⟩

def run (t : ℕ) (c : TM2.Cfg (fun _ : Stack => Bool) Label Control) :=
  ((advance program)^[t]) c

theorem count_cons (word assignment : List Bool) (b : Bool) (v : Control) :
    advance program (cfg (some (.inr .count)) v (true :: word) (b :: assignment)) =
      cfg (some (.inr .count)) (setLast (setLast v (some true)) (some b)) word assignment := by
  simp only [advance, cfg, program, TM2.step, TM2.stepAux, output,
    ProtocolWordField.stackContents, last, setLast, Option.getD_some,
    List.head?_cons, List.tail_cons, Sum.elim_inl, Bool.cond_true,
    Option.isSome_some, show (2 : Fin 3) ≠ 0 by decide,
    show (2 : Fin 3) ≠ 1 by decide, if_neg, if_pos rfl, ite_true, ite_false,
    Function.update_of_ne (by decide : (Sum.inl (0 : Fin 3) : Stack) ≠ .inl 2)]
  apply congrArg (fun S : Stack → List Bool =>
    (⟨some (.inr Outer.count), ((v.1.1, some b), ()), S⟩ :
      TM2.Cfg (fun _ : Stack => Bool) Label Control))
  funext k
  cases k with
  | inl k => fin_cases k <;> rfl
  | inr k => cases k; rfl

theorem count_run (word assignment : List Bool) (v : Control) :
    ∃ t ≤ word.length + 1,
      (run t (cfg (some (.inr .count)) v word assignment)).l = none ∧
      (run t (cfg (some (.inr .count)) v word assignment)).stk (.inr ()) =
        [prefixMatch word assignment] := by
  induction word generalizing assignment v with
  | nil =>
    refine ⟨1, by simp, ?_, ?_⟩ <;> rfl
  | cons bit word ih =>
    cases bit with
    | false =>
      cases assignment <;>
        refine ⟨1, by simp, ?_, ?_⟩ <;> rfl
    | true =>
      cases assignment with
      | nil =>
        refine ⟨1, by simp, ?_, ?_⟩ <;> rfl
      | cons b assignment =>
        obtain ⟨t, ht, hh, ho⟩ := ih assignment (setLast (setLast v (some true)) (some b))
        refine ⟨t + 1, by simp only [List.length_cons]; omega, ?_, ?_⟩
        all_goals
          rw [run, Function.iterate_succ_apply, count_cons]
        · exact hh
        · exact ho

theorem prefixMatch_unary (n : ℕ) (tail assignment : List Bool) :
    prefixMatch (EncodedGraph.unary n ++ tail) assignment = decide (assignment.length = n) := by
  induction n generalizing assignment with
  | zero => cases assignment <;> simp [EncodedGraph.unary, prefixMatch]
  | succ n ih =>
    cases assignment with
    | nil => simp [EncodedGraph.unary, List.replicate_succ, prefixMatch]
    | cons b assignment =>
      simpa [EncodedGraph.unary, List.replicate_succ, prefixMatch] using ih assignment

theorem result_pair_formula (f : EncodedCNF.Formula) (assignment : List Bool) :
    result (EncodedComplexity.pair (EncodedCNF.encode f) assignment) =
      decide (assignment.length = f.variables) := by
  simp only [result, EncodedComplexity.pair, readField_append, EncodedCNF.encode]
  rw [List.append_assoc, prefixMatch_unary]

def ready (c : TM2.Cfg (fun _ : Fin 3 => Bool)
    ProtocolWordField.Label ProtocolWordField.Control) :
    TM2.Cfg (fun _ : Stack => Bool) Label Control :=
  liftCfg (some Outer.ready) () (fun _ : Unit => []) c

theorem ready_failed (c : TM2.Cfg (fun _ : Fin 3 => Bool)
    ProtocolWordField.Label ProtocolWordField.Control)
    (hh : c.l = none) (ho : c.stk 2 = [false]) :
    (advance program (ready c)).l = none ∧
      (advance program (ready c)).stk (.inr ()) = [false] := by
  simp only [advance, ready, liftCfg, hh, program, TM2.step, TM2.stepAux,
    ho, last, setLast, output, Option.map_some, Option.getD_some,
    Sum.elim_inl, List.head?_cons, List.tail_cons, Bool.cond_false]
  constructor
  · trivial
  · rfl

theorem ready_success (c : TM2.Cfg (fun _ : Fin 3 => Bool)
    ProtocolWordField.Label ProtocolWordField.Control) (word assignment : List Bool)
    (hh : c.l = none) (h0 : c.stk 0 = assignment) (h1 : c.stk 1 = [])
    (h2 : c.stk 2 = true :: word) :
    advance program (ready c) = cfg (some (.inr .count))
      (setLast (c.var, ()) (some true)) word assignment := by
  simp only [advance, ready, liftCfg, hh, Option.map_some, Option.getD_some,
    TM2.step, program, TM2.stepAux, Sum.elim_inl, h2,
    List.head?_cons, List.tail_cons, setLast, last, Option.getD_some,
    cfg, Bool.cond_true]
  apply congrArg (fun S : Stack → List Bool =>
    (⟨some (.inr Outer.count), setLast (c.var, ()) (some true), S⟩ :
      TM2.Cfg (fun _ : Stack => Bool) Label Control))
  funext k
  cases k with
  | inl k => fin_cases k <;> simp [ProtocolWordField.stackContents, h0, h1, h2]
  | inr k => cases k; rfl

/-- The pair parser and the unary/witness scan are both actual finite
programs. Every malformed outer word and every malformed unary header
terminates within this linear all-input clock. -/
theorem outputs (code : List Bool) :
    machine.OutputsWithin code [result code] (4 * (code.length + 1)) := by
  obtain ⟨t, ht, hp⟩ := ProtocolWordField.scan_correct code none none [] []
  let start := ProtocolWordField.cfg (some .scan) (none, none) code [] []
  let c := ProtocolWordField.run t start
  have hh : c.l = none := hp.1
  obtain ⟨u, hu, he⟩ := BitMachineSubroutine.lift_outputs
    ProtocolWordField.program program (some Outer.ready) (fun _ => rfl)
    () (fun _ : Unit => []) start t hh
  have hentry : rawInit (.inl 0 : Stack) (.inl ProtocolWordField.Label.scan)
      (((none, none), ()) : Control) code = ready start := by
    unfold rawInit ready start liftCfg ProtocolWordField.cfg
    congr 1
    funext k
    cases k with
    | inl k => fin_cases k <;> rfl
    | inr k => cases k; rfl
  have hrun : run u (rawInit (.inl 0 : Stack) (.inl ProtocolWordField.Label.scan)
      (((none, none), ()) : Control) code) = ready c := by
    rw [hentry]
    exact he
  cases hd : readField code with
  | none =>
    have hout : c.stk 2 = [false] := by simpa only [ProtocolWordField.Post, hd] using hp.2
    have hfin := ready_failed c hh hout
    have heq : run (u + 1) (rawInit (.inl 0 : Stack) (.inl ProtocolWordField.Label.scan)
        (((none, none), ()) : Control) code) = advance program (ready c) := by
      rw [run, Function.iterate_succ_apply']
      exact congrArg (advance program) hrun
    apply outputsWithin_of_raw_run (.inl 0 : Stack) (.inr ())
      (.inl ProtocolWordField.Label.scan) (((none, none), ()) : Control)
      program code [result code] (u + 1) _ (by simp at ht; omega)
    · exact (congrArg (fun q => q.l) heq).trans hfin.1
    · simpa only [run, result, hd] using
        (congrArg (fun q => q.stk (.inr ())) heq).trans hfin.2
  | some p =>
    obtain ⟨word, assignment⟩ := p
    have hout : c.stk 0 = assignment ∧ c.stk 1 = [] ∧ c.stk 2 = true :: word := by
      simpa only [ProtocolWordField.Post, hd, List.reverse_nil, List.nil_append,
        List.append_nil] using hp.2
    have hready := ready_success c word assignment hh hout.1 hout.2.1 hout.2.2
    obtain ⟨v, hv, hhalt, houtput⟩ := count_run word assignment (setLast (c.var, ()) (some true))
    have hlen : word.length ≤ code.length := by
      have hs := congrArg List.length (readField_sound hd)
      simp only [List.length_append, field_length] at hs
      omega
    have heq : run (u + 1 + v) (rawInit (.inl 0 : Stack) (.inl ProtocolWordField.Label.scan)
        (((none, none), ()) : Control) code) =
        run v (cfg (some (.inr .count)) (setLast (c.var, ()) (some true)) word assignment) := by
      rw [run, show u + 1 + v = v + (u + 1) by omega,
        Function.iterate_add_apply, Function.iterate_succ_apply']
      change ((advance program)^[v]) (advance program (run u _)) = _
      rw [hrun, hready]
      rfl
    apply outputsWithin_of_raw_run (.inl 0 : Stack) (.inr ())
      (.inl ProtocolWordField.Label.scan) (((none, none), ()) : Control)
      program code [result code] (u + 1 + v) _ (by simp at ht; omega)
    · exact (congrArg (fun q => q.l) heq).trans hhalt
    · simpa only [run, result, hd] using
        (congrArg (fun q => q.stk (.inr ())) heq).trans houtput

theorem polytime : BitMachine.Polytime (fun code => [result code]) :=
  ⟨machine, 4, 1, by simpa only [pow_one] using outputs⟩

#print axioms count_run
#print axioms result_pair_formula
#print axioms outputs
#print axioms polytime

end CurrentAdditive.V39CNFAssignmentLength
