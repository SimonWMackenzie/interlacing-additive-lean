import EthInapproximability.CurrentPaper.SourceNormalizationMachineField
import EthInapproximability.CurrentPaper.BitMachineSubroutine
import EthInapproximability.CurrentPaper.EncodedGraph
import EthInapproximability.CurrentPaper.SourceNormalizationMachineMark
import EthInapproximability.CurrentPaper.UnaryBinaryEncoding

/-! # Physical parser for a graph's unary endpoint stream

The program first copies the entire input to make a physical field budget,
then consumes the unary vertex count, the canonical edge-count field, and two
canonical endpoint fields per edge. The count and endpoint values are expanded
by the bounded field subroutine. All phases are finite control, and every
loop consumes a stack symbol. The valid-code theorem below composes the full
physical run. Malformed-code rejection is a separate obligation.
-/

namespace EthInapproximability.CurrentPaper.SourceNormalizationMachineDecode

set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

open Turing TM2.Stmt BitMachineEncoding BitMachineComposition

inductive Phase where
  | count | left | right
  deriving DecidableEq, Fintype

inductive Admin where
  | gate | capScan | capRestore | vertices | afterField
  | splitCountScan | splitCountRestore | edges
  | emitLeft | emitLeftUnary | emitRight | emitRightUnary
  | finishReverse | clearCap | reject
  deriving DecidableEq, Fintype

abbrev Stack := SourceNormalizationMachineField.Stack ⊕ Fin 6
abbrev Label := SourceNormalizationMachineField.Label ⊕ Admin
abbrev Control := SourceNormalizationMachineField.Control × (Phase × Option Bool)
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control
abbrev Statement := TM2.Stmt (fun _ : Stack => Bool) Label Control

def go (l : Admin) : Statement := goto (fun _ => .inr l)
def setPop (v : Control) (b : Option Bool) : Control := (v.1, v.2.1, b)
def setPhase (p : Phase) (_v : Control) : Control :=
  (SourceNormalizationMachineField.initialControl, p, none)
def doneControl (b : Bool) : Control :=
  (SourceNormalizationMachineField.doneControl b, .count, none)

/-- The left summand is precisely the eight-stack bounded-field bank. The
right summand holds vertices, edge count, remaining edges, reversed stream,
ordered stream, and graph-copy scratch in that order. -/
def program : Label → Statement
  | .inl l => liftStmt (some Admin.afterField) (SourceNormalizationMachineField.program l)
  | .inr .gate => pop (.inl 0) setPop
      (branch (fun v => v.2.2 == some true)
        (load (fun _ => (SourceNormalizationMachineField.initialControl, .count, none))
          (go .capScan))
        (go .reject))
  | .inr .capScan => pop (.inl 0) setPop
      (branch (fun v => v.2.2.isSome)
        (push (.inl 6) (fun _ => true)
          (push (.inr 5) (fun v => v.2.2.getD false) (go .capScan)))
        (go .capRestore))
  | .inr .capRestore => pop (.inr 5) setPop
      (branch (fun v => v.2.2.isSome)
        (push (.inl 0) (fun v => v.2.2.getD false) (go .capRestore))
        (go .vertices))
  | .inr .vertices => pop (.inl 0) setPop
      (branch (fun v => v.2.2.isSome)
        (branch (fun v => v.2.2.getD false)
          (push (.inr 0) (fun _ => true) (go .vertices))
          (load (setPhase .count) (goto (fun _ => .inl (.inl .scan)))))
        (go .reject))
  | .inr .afterField =>
      branch (fun v => v.1.2 == some true)
        (branch (fun v => decide (v.2.1 = .count)) (go .splitCountScan)
          (branch (fun v => decide (v.2.1 = .left)) (go .emitLeft) (go .emitRight)))
        (go .reject)
  | .inr .splitCountScan => pop (.inl 5) setPop
      (branch (fun v => v.2.2.isSome)
        (push (.inl 7) (fun _ => true) (go .splitCountScan))
        (go .splitCountRestore))
  | .inr .splitCountRestore => pop (.inl 7) setPop
      (branch (fun v => v.2.2.isSome)
        (push (.inr 1) (fun _ => true)
          (push (.inr 2) (fun _ => true) (go .splitCountRestore)))
        (go .edges))
  | .inr .edges => pop (.inr 2) setPop
      (branch (fun v => v.2.2.isSome)
        (load (setPhase .left) (goto (fun _ => .inl (.inl .scan))))
        (go .finishReverse))
  | .inr .emitLeft => go .emitLeftUnary
  | .inr .emitLeftUnary => pop (.inl 5) setPop
      (branch (fun v => v.2.2.isSome)
        (push (.inr 3) (fun _ => true) (go .emitLeftUnary))
        (push (.inr 3) (fun _ => false)
          (load (setPhase .right) (goto (fun _ => .inl (.inl .scan))))))
  | .inr .emitRight => go .emitRightUnary
  | .inr .emitRightUnary => pop (.inl 5) setPop
      (branch (fun v => v.2.2.isSome)
        (push (.inr 3) (fun _ => true) (go .emitRightUnary))
        (push (.inr 3) (fun _ => false) (go .edges)))
  | .inr .finishReverse => pop (.inr 3) setPop
      (branch (fun v => v.2.2.isSome)
        (push (.inr 4) (fun v => v.2.2.getD false) (go .finishReverse))
        (go .clearCap))
  | .inr .clearCap => pop (.inl 6) setPop
      (branch (fun v => v.2.2.isSome) (go .clearCap)
        (load (fun _ => doneControl true) halt))
  | .inr .reject => load (fun _ => doneControl false) halt

def run (t : ℕ) (c : Config) : Config := ((advance program)^[t]) c

def cfg (l : Option Label) (v : Control) (d : SourceNormalizationMachineField.Data)
    (vertices edgeCount remaining reverseStream stream scratch : List Bool) : Config :=
  ⟨l, v, Sum.elim d.stacks
    ![vertices, edgeCount, remaining, reverseStream, stream, scratch]⟩

private theorem update_left (a : SourceNormalizationMachineField.Stack → List Bool)
    (b : Fin 6 → List Bool) (i : SourceNormalizationMachineField.Stack)
    (x : List Bool) :
    Function.update (Sum.elim a b) (.inl i) x =
      Sum.elim (Function.update a i x) b := by
  funext k
  cases k with
  | inl j => by_cases h : j = i <;> simp [Function.update_apply, h]
  | inr j => simp [Function.update_apply]

private theorem update_right (a : SourceNormalizationMachineField.Stack → List Bool)
    (b : Fin 6 → List Bool) (i : Fin 6) (x : List Bool) :
    Function.update (Sum.elim a b) (.inr i) x =
      Sum.elim a (Function.update b i x) := by
  funext k
  cases k with
  | inl j => simp [Function.update_apply]
  | inr j => by_cases h : j = i <;> simp [Function.update_apply, h]

private theorem update_field_input (d : SourceNormalizationMachineField.Data)
    (xs : List Bool) :
    Function.update d.stacks 0 xs = ({d with input := xs} : SourceNormalizationMachineField.Data).stacks := by
  funext k
  fin_cases k <;> rfl

private theorem update_field_cap (d : SourceNormalizationMachineField.Data)
    (xs : List Bool) :
    Function.update d.stacks 6 xs = ({d with cap := xs} : SourceNormalizationMachineField.Data).stacks := by
  funext k
  fin_cases k <;> rfl

theorem run_succ {c c' : Config} (h : advance program c = c') (n : ℕ) :
    run (n + 1) c = run n c' := by
  exact (Function.iterate_succ_apply _ _ _).trans (congrArg (run n) h)

theorem run_add {c c' : Config} {n : ℕ} (h : run n c = c') (m : ℕ) :
    run (n + m) c = run m c' := by
  rw [Nat.add_comm, run, Function.iterate_add_apply]
  exact congrArg (run m) h

theorem capScan_cons (b : Bool) (xs cap scratch : List Bool) (v : Control)
    (d : SourceNormalizationMachineField.Data)
    (vertices edgeCount remaining reverseStream stream : List Bool) :
    advance program
      (cfg (some (.inr .capScan)) v {d with input := b :: xs, cap := cap}
        vertices edgeCount remaining reverseStream stream scratch) =
    cfg (some (.inr .capScan)) (setPop v (some b))
      {d with input := xs, cap := true :: cap}
        vertices edgeCount remaining reverseStream stream (b :: scratch) := by
  simp only [advance, TM2.step, program, TM2.stepAux, cfg,
    SourceNormalizationMachineField.Data.stacks, Sum.elim_inl,
    Matrix.cons_val_zero, List.head?_cons, List.tail_cons,
    setPop, Option.isSome_some, Option.getD_some, Bool.cond_true,
    go, TM2.stepAux]
  simp only [update_left, update_right, update_field_input, update_field_cap]
  congr 1
  funext k
  fin_cases k <;> rfl

theorem capScan_nil (cap scratch : List Bool) (v : Control)
    (d : SourceNormalizationMachineField.Data)
    (vertices edgeCount remaining reverseStream stream : List Bool) :
    advance program
      (cfg (some (.inr .capScan)) v {d with input := [], cap := cap}
        vertices edgeCount remaining reverseStream stream scratch) =
    cfg (some (.inr .capRestore)) (setPop v none)
      {d with input := [], cap := cap}
        vertices edgeCount remaining reverseStream stream scratch := by
  simp only [advance, TM2.step, program, TM2.stepAux, cfg,
    SourceNormalizationMachineField.Data.stacks, Sum.elim_inl,
    Matrix.cons_val_zero, List.head?_nil, List.tail_nil,
    setPop, Option.isSome_none, Bool.cond_false,
    go, TM2.stepAux]
  simp only [update_left, update_field_input]
  simp only [Option.getD_some]
  congr 1
  funext k
  cases k with
  | inl k => fin_cases k <;> rfl
  | inr k => fin_cases k <;> rfl

theorem capRestore_cons (b : Bool) (xs cap scratch : List Bool) (v : Control)
    (d : SourceNormalizationMachineField.Data)
    (vertices edgeCount remaining reverseStream stream : List Bool) :
    advance program
      (cfg (some (.inr .capRestore)) v {d with input := xs, cap := cap}
        vertices edgeCount remaining reverseStream stream (b :: scratch)) =
    cfg (some (.inr .capRestore)) (setPop v (some b))
      {d with input := b :: xs, cap := cap}
        vertices edgeCount remaining reverseStream stream scratch := by
  simp only [advance, TM2.step, program, TM2.stepAux, cfg,
    SourceNormalizationMachineField.Data.stacks, Sum.elim_inr,
    Matrix.cons_val_succ, Matrix.cons_val_zero,
    List.head?_cons, List.tail_cons, setPop,
    Option.isSome_some, Option.getD_some, Bool.cond_true,
    go, TM2.stepAux]
  simp only [show (![vertices, edgeCount, remaining, reverseStream, stream,
      b :: scratch] : Fin 6 → List Bool) 5 = b :: scratch by rfl,
    List.head?_cons, List.tail_cons, Option.isSome_some,
    Option.getD_some, Bool.cond_true]
  simp only [update_left, update_right]
  congr 1
  funext k
  cases k with
  | inl k => fin_cases k <;> rfl
  | inr k => fin_cases k <;> rfl

theorem capRestore_nil (xs cap : List Bool) (v : Control)
    (d : SourceNormalizationMachineField.Data)
    (vertices edgeCount remaining reverseStream stream : List Bool) :
    advance program
      (cfg (some (.inr .capRestore)) v {d with input := xs, cap := cap}
        vertices edgeCount remaining reverseStream stream []) =
    cfg (some (.inr .vertices)) (setPop v none)
      {d with input := xs, cap := cap}
        vertices edgeCount remaining reverseStream stream [] := by
  simp only [advance, TM2.step, program, TM2.stepAux, cfg,
    SourceNormalizationMachineField.Data.stacks, Sum.elim_inr,
    Matrix.cons_val_succ, Matrix.cons_val_zero,
    List.head?_nil, List.tail_nil, setPop,
    Option.isSome_none, Bool.cond_false,
    go, TM2.stepAux]
  simp only [show (![vertices, edgeCount, remaining, reverseStream, stream,
      []] : Fin 6 → List Bool) 5 = [] by rfl,
    List.head?_nil, List.tail_nil, Option.isSome_none, Bool.cond_false]
  simp only [update_right]
  simp only [Option.getD_some]
  congr 1
  funext k
  cases k with
  | inl k => fin_cases k <;> rfl
  | inr k => fin_cases k <;> rfl

private theorem replicate_push (n : ℕ) (cap : List Bool) :
    List.replicate n true ++ true :: cap =
      true :: (List.replicate n true ++ cap) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simpa [List.replicate_succ, List.cons_append] using
        (congrArg (List.cons true) ih)

theorem capScan_run (xs cap scratch : List Bool) (v : Control)
    (d : SourceNormalizationMachineField.Data)
    (vertices edgeCount remaining reverseStream stream : List Bool) :
    run (xs.length + 1)
      (cfg (some (.inr .capScan)) v {d with input := xs, cap := cap}
        vertices edgeCount remaining reverseStream stream scratch) =
    cfg (some (.inr .capRestore)) (setPop v none)
      {d with input := [], cap := List.replicate xs.length true ++ cap}
        vertices edgeCount remaining reverseStream stream (xs.reverse ++ scratch) := by
  induction xs generalizing v cap scratch with
  | nil =>
      simpa using run_succ
        (capScan_nil cap scratch v d vertices edgeCount remaining reverseStream stream) 0
  | cons b xs ih =>
      rw [List.length_cons, run_succ
        (capScan_cons b xs cap scratch v d vertices edgeCount remaining reverseStream stream)]
      simpa only [List.replicate_succ, List.reverse_cons, List.append_assoc,
        replicate_push, setPop] using
        ih (true :: cap) (b :: scratch) (setPop v (some b))

theorem capRestore_run (ys xs cap : List Bool) (v : Control)
    (d : SourceNormalizationMachineField.Data)
    (vertices edgeCount remaining reverseStream stream : List Bool) :
    run (ys.length + 1)
      (cfg (some (.inr .capRestore)) v {d with input := xs, cap := cap}
        vertices edgeCount remaining reverseStream stream ys) =
    cfg (some (.inr .vertices)) (setPop v none)
      {d with input := ys.reverse ++ xs, cap := cap}
        vertices edgeCount remaining reverseStream stream [] := by
  induction ys generalizing xs v with
  | nil =>
      simpa using capRestore_nil xs cap v d vertices edgeCount remaining reverseStream stream
  | cons b ys ih =>
      rw [List.length_cons, run_succ
        (capRestore_cons b xs cap ys v d vertices edgeCount remaining reverseStream stream)]
      simpa [List.reverse_cons, List.append_assoc] using
        ih (b :: xs) (setPop v (some b))

def start (input : List Bool) : Config :=
  ⟨some (.inr .capScan), (SourceNormalizationMachineField.initialControl, .count, none),
    Sum.elim ![input, [], [], [], [], [], [], []] ![[], [], [], [], [], []]⟩

def guardedStart (input : List Bool) : Config :=
  cfg (some (.inr .gate))
    (SourceNormalizationMachineField.initialControl, .count, none)
    {input := input} [] [] [] [] [] []

theorem gate_true (input : List Bool) :
    advance program (guardedStart (true :: input)) = start input := by
  simp only [guardedStart, advance, TM2.step, program, TM2.stepAux,
    cfg, SourceNormalizationMachineField.Data.stacks, Sum.elim_inl,
    Matrix.cons_val_zero, List.head?_cons, List.tail_cons,
    setPop, Option.isSome_some, Option.getD_some, go, start]
  simp only [update_left, update_field_input]
  simp only [show ((some true : Option Bool) == some true) = true by decide,
    Bool.cond_true]
  congr 1
  funext k
  cases k with
  | inl k => fin_cases k <;> rfl
  | inr k => fin_cases k <;> rfl

theorem gate_false :
    advance program (guardedStart [false]) =
      cfg (some (.inr .reject))
        (setPop (SourceNormalizationMachineField.initialControl, .count, none)
          (some false)) {} [] [] [] [] [] [] := by
  simp only [guardedStart, advance, TM2.step, program, TM2.stepAux,
    cfg, SourceNormalizationMachineField.Data.stacks, Sum.elim_inl,
    Matrix.cons_val_zero, List.head?_cons, List.tail_cons,
    setPop, Option.isSome_some, Option.getD_some, go]
  simp only [update_left, update_field_input]
  simp only [show ((some false : Option Bool) == some true) = false by decide,
    Bool.cond_false]
  congr 1
  funext k
  cases k with
  | inl k => fin_cases k <;> rfl
  | inr k => fin_cases k <;> rfl

theorem cap_run (input : List Bool) :
    run (2 * input.length + 2) (start input) =
    cfg (some (.inr .vertices))
      (setPop (SourceNormalizationMachineField.initialControl, .count, none) none)
      {input := input, cap := List.replicate input.length true}
      [] [] [] [] [] [] := by
  have hs := capScan_run input [] []
    (SourceNormalizationMachineField.initialControl, .count, none)
    ({} : SourceNormalizationMachineField.Data) [] [] [] [] []
  have hr := capRestore_run input.reverse [] (List.replicate input.length true)
    (setPop (SourceNormalizationMachineField.initialControl, .count, none) none)
    ({} : SourceNormalizationMachineField.Data) [] [] [] [] []
  simp only [List.append_nil] at hs
  simp only [List.length_reverse, List.reverse_reverse, List.append_nil] at hr
  rw [show 2 * input.length + 2 = (input.length + 1) + (input.length + 1) by omega]
  exact (run_add hs _).trans hr

theorem vertices_cons (xs : List Bool) (v : Control)
    (d : SourceNormalizationMachineField.Data)
    (vertices edgeCount remaining reverseStream stream scratch : List Bool) :
    advance program
      (cfg (some (.inr .vertices)) v {d with input := true :: xs}
        vertices edgeCount remaining reverseStream stream scratch) =
    cfg (some (.inr .vertices)) (setPop v (some true))
      {d with input := xs}
        (true :: vertices) edgeCount remaining reverseStream stream scratch := by
  simp only [advance, TM2.step, program, TM2.stepAux, cfg,
    SourceNormalizationMachineField.Data.stacks, Sum.elim_inl,
    Matrix.cons_val_zero, List.head?_cons, List.tail_cons,
    setPop, Option.isSome_some, Option.getD_some, Bool.cond_true,
    go, TM2.stepAux]
  simp only [update_left, update_right]
  congr 1
  funext k
  cases k with
  | inl k => fin_cases k <;> rfl
  | inr k => fin_cases k <;> rfl

theorem vertices_end (xs : List Bool) (v : Control)
    (d : SourceNormalizationMachineField.Data)
    (vertices edgeCount remaining reverseStream stream scratch : List Bool) :
    advance program
      (cfg (some (.inr .vertices)) v {d with input := false :: xs}
        vertices edgeCount remaining reverseStream stream scratch) =
    cfg (some (.inl (.inl .scan))) (setPhase .count (setPop v (some false)))
      {d with input := xs}
        vertices edgeCount remaining reverseStream stream scratch := by
  simp only [advance, TM2.step, program, TM2.stepAux, cfg,
    SourceNormalizationMachineField.Data.stacks, Sum.elim_inl,
    Matrix.cons_val_zero, List.head?_cons, List.tail_cons,
    setPop, Option.isSome_some, Option.getD_some, Bool.cond_false,
    go, TM2.stepAux, setPhase]
  simp only [update_left]
  simp only [Bool.cond_true]
  congr 1
  funext k
  cases k with
  | inl k => fin_cases k <;> rfl
  | inr k => fin_cases k <;> rfl

theorem vertices_run (n : ℕ) (suffix : List Bool) (v : Control)
    (d : SourceNormalizationMachineField.Data)
    (vertices edgeCount remaining reverseStream stream scratch : List Bool) :
    run (n + 1)
      (cfg (some (.inr .vertices)) v
        {d with input := EncodedGraph.unary n ++ suffix}
        vertices edgeCount remaining reverseStream stream scratch) =
    cfg (some (.inl (.inl .scan)))
      (setPhase .count (setPop v (some false)))
      {d with input := suffix}
        (List.replicate n true ++ vertices)
        edgeCount remaining reverseStream stream scratch := by
  induction n generalizing v vertices with
  | zero =>
      simpa [EncodedGraph.unary] using
        run_succ (vertices_end suffix v d vertices edgeCount remaining reverseStream stream scratch) 0
  | succ n ih =>
      rw [show EncodedGraph.unary (n + 1) =
        true :: EncodedGraph.unary n by simp [EncodedGraph.unary, List.replicate_succ]]
      simp only [List.cons_append]
      rw [run_succ (vertices_cons _ v d vertices edgeCount remaining reverseStream stream scratch)]
      simpa only [List.replicate_succ, replicate_push, setPop] using
        ih (setPop v (some true))
        (true :: vertices)

theorem field_run (phase : Phase) (n : ℕ) (cap suffix : List Bool)
    (hn : n ≤ cap.length)
    (vertices edgeCount remaining reverseStream stream scratch : List Bool) :
    ∃ t ≤ 20 * (cap.length + 1) * (n.bits.length + 1),
      run t (cfg (some (.inl (.inl .scan)))
        (SourceNormalizationMachineField.initialControl, phase, none)
        {input := EncodedCommunication.natField n ++ suffix, cap := cap}
        vertices edgeCount remaining reverseStream stream scratch) =
      cfg (some (.inr .afterField))
        (SourceNormalizationMachineField.doneControl true, phase, none)
        {input := suffix, unary := List.replicate n true, cap := cap}
        vertices edgeCount remaining reverseStream stream scratch := by
  let c := SourceNormalizationMachineField.cfg (some (.inl .scan))
    SourceNormalizationMachineField.initialControl
      {input := EncodedCommunication.natField n ++ suffix, cap := cap}
  let T : Fin 6 → List Bool :=
    ![vertices, edgeCount, remaining, reverseStream, stream, scratch]
  obtain ⟨t, ht, he⟩ := SourceNormalizationMachineField.field_encoded_cap n cap hn suffix
  have hhalt : ((advance SourceNormalizationMachineField.program)^[t] c).l = none := by
    simpa only [SourceNormalizationMachineField.run, c] using congrArg TM2.Cfg.l he
  obtain ⟨u, hu, hr⟩ := BitMachineSubroutine.lift_outputs
    SourceNormalizationMachineField.program program (some Admin.afterField)
    (fun _ => rfl) (phase, none) T c t hhalt
  have hrun : ((advance SourceNormalizationMachineField.program)^[t] c) =
      SourceNormalizationMachineField.cfg none
        (SourceNormalizationMachineField.doneControl true)
        {input := suffix, unary := List.replicate n true, cap := cap} := by
    simpa only [SourceNormalizationMachineField.run, c] using he
  rw [hrun] at hr
  refine ⟨u, hu.trans ht, ?_⟩
  exact hr

theorem afterField_count (d : SourceNormalizationMachineField.Data)
    (vertices edgeCount remaining reverseStream stream scratch : List Bool) :
    advance program
      (cfg (some (.inr .afterField))
        (SourceNormalizationMachineField.doneControl true, .count, none) d
        vertices edgeCount remaining reverseStream stream scratch) =
    cfg (some (.inr .splitCountScan))
      (SourceNormalizationMachineField.doneControl true, .count, none) d
        vertices edgeCount remaining reverseStream stream scratch := by
  rfl

theorem afterField_left (d : SourceNormalizationMachineField.Data)
    (vertices edgeCount remaining reverseStream stream scratch : List Bool) :
    advance program
      (cfg (some (.inr .afterField))
        (SourceNormalizationMachineField.doneControl true, .left, none) d
        vertices edgeCount remaining reverseStream stream scratch) =
    cfg (some (.inr .emitLeft))
      (SourceNormalizationMachineField.doneControl true, .left, none) d
        vertices edgeCount remaining reverseStream stream scratch := by
  rfl

theorem afterField_right (d : SourceNormalizationMachineField.Data)
    (vertices edgeCount remaining reverseStream stream scratch : List Bool) :
    advance program
      (cfg (some (.inr .afterField))
        (SourceNormalizationMachineField.doneControl true, .right, none) d
        vertices edgeCount remaining reverseStream stream scratch) =
    cfg (some (.inr .emitRight))
      (SourceNormalizationMachineField.doneControl true, .right, none) d
        vertices edgeCount remaining reverseStream stream scratch := by
  rfl

theorem splitScan_cons (xs temp : List Bool) (v : Control)
    (d : SourceNormalizationMachineField.Data)
    (vertices edgeCount remaining reverseStream stream scratch : List Bool) :
    advance program
      (cfg (some (.inr .splitCountScan)) v {d with unary := true :: xs, temp := temp}
        vertices edgeCount remaining reverseStream stream scratch) =
    cfg (some (.inr .splitCountScan)) (setPop v (some true))
      {d with unary := xs, temp := true :: temp}
        vertices edgeCount remaining reverseStream stream scratch := by
  simp only [advance, TM2.step, program, TM2.stepAux, cfg,
    SourceNormalizationMachineField.Data.stacks, Sum.elim_inl,
    List.head?_cons, List.tail_cons, setPop,
    Option.isSome_some, Bool.cond_true, go]
  simp only [show (![d.input, d.saved, d.value, d.budget, d.work,
      true :: xs, d.cap, temp] : SourceNormalizationMachineField.Stack → List Bool) 5 =
      true :: xs by rfl, List.head?_cons, List.tail_cons,
      Option.isSome_some, Bool.cond_true, Option.getD_some]
  simp only [update_left]
  congr 1
  funext k
  cases k with
  | inl k => fin_cases k <;> rfl
  | inr k => fin_cases k <;> rfl

theorem splitScan_nil (temp : List Bool) (v : Control)
    (d : SourceNormalizationMachineField.Data)
    (vertices edgeCount remaining reverseStream stream scratch : List Bool) :
    advance program
      (cfg (some (.inr .splitCountScan)) v {d with unary := [], temp := temp}
        vertices edgeCount remaining reverseStream stream scratch) =
    cfg (some (.inr .splitCountRestore)) (setPop v none)
      {d with unary := [], temp := temp}
        vertices edgeCount remaining reverseStream stream scratch := by
  simp only [advance, TM2.step, program, TM2.stepAux, cfg,
    SourceNormalizationMachineField.Data.stacks, Sum.elim_inl,
    List.head?_nil, List.tail_nil, setPop,
    Option.isSome_none, Bool.cond_false, go]
  simp only [show (![d.input, d.saved, d.value, d.budget, d.work,
      [], d.cap, temp] : SourceNormalizationMachineField.Stack → List Bool) 5 =
      [] by rfl, List.head?_nil, List.tail_nil,
      Option.isSome_none, Bool.cond_false]
  simp only [update_left]
  simp only [Option.getD_some]
  congr 1
  funext k
  cases k with
  | inl k => fin_cases k <;> rfl
  | inr k => fin_cases k <;> rfl

theorem splitRestore_cons (xs : List Bool) (v : Control)
    (d : SourceNormalizationMachineField.Data)
    (vertices edgeCount remaining reverseStream stream scratch : List Bool) :
    advance program
      (cfg (some (.inr .splitCountRestore)) v {d with temp := true :: xs}
        vertices edgeCount remaining reverseStream stream scratch) =
    cfg (some (.inr .splitCountRestore)) (setPop v (some true))
      {d with temp := xs}
        vertices (true :: edgeCount) (true :: remaining) reverseStream stream scratch := by
  simp only [advance, TM2.step, program, TM2.stepAux, cfg,
    SourceNormalizationMachineField.Data.stacks, Sum.elim_inl,
    List.head?_cons, List.tail_cons, setPop,
    Option.isSome_some, Bool.cond_true, go]
  simp only [show (![d.input, d.saved, d.value, d.budget, d.work,
      d.unary, d.cap, true :: xs] : SourceNormalizationMachineField.Stack → List Bool) 7 =
      true :: xs by rfl, List.head?_cons, List.tail_cons,
      Option.isSome_some, Bool.cond_true, Option.getD_some]
  simp only [update_left, update_right]
  congr 1
  funext k
  cases k with
  | inl k => fin_cases k <;> rfl
  | inr k => fin_cases k <;> rfl

theorem splitRestore_nil (v : Control)
    (d : SourceNormalizationMachineField.Data)
    (vertices edgeCount remaining reverseStream stream scratch : List Bool) :
    advance program
      (cfg (some (.inr .splitCountRestore)) v {d with temp := []}
        vertices edgeCount remaining reverseStream stream scratch) =
    cfg (some (.inr .edges)) (setPop v none)
      {d with temp := []}
        vertices edgeCount remaining reverseStream stream scratch := by
  simp only [advance, TM2.step, program, TM2.stepAux, cfg,
    SourceNormalizationMachineField.Data.stacks, Sum.elim_inl,
    List.head?_nil, List.tail_nil, setPop,
    Option.isSome_none, Bool.cond_false, go]
  simp only [show (![d.input, d.saved, d.value, d.budget, d.work,
      d.unary, d.cap, []] : SourceNormalizationMachineField.Stack → List Bool) 7 =
      [] by rfl, List.head?_nil, List.tail_nil,
      Option.isSome_none, Bool.cond_false]
  simp only [update_left]
  simp only [Option.getD_some]
  congr 1
  funext k
  cases k with
  | inl k => fin_cases k <;> rfl
  | inr k => fin_cases k <;> rfl

theorem splitScan_run (m : ℕ) (temp : List Bool) (v : Control)
    (d : SourceNormalizationMachineField.Data)
    (vertices edgeCount remaining reverseStream stream scratch : List Bool) :
    run (m + 1)
      (cfg (some (.inr .splitCountScan)) v
        {d with unary := List.replicate m true, temp := temp}
        vertices edgeCount remaining reverseStream stream scratch) =
    cfg (some (.inr .splitCountRestore)) (setPop v none)
      {d with unary := [], temp := List.replicate m true ++ temp}
        vertices edgeCount remaining reverseStream stream scratch := by
  induction m generalizing temp v with
  | zero =>
      simpa using run_succ
        (splitScan_nil temp v d vertices edgeCount remaining reverseStream stream scratch) 0
  | succ m ih =>
      rw [List.replicate_succ, run_succ
        (splitScan_cons (List.replicate m true) temp v d
          vertices edgeCount remaining reverseStream stream scratch)]
      simpa only [List.replicate_succ, replicate_push, setPop] using
        ih (true :: temp) (setPop v (some true))

theorem splitRestore_run (m : ℕ) (v : Control)
    (d : SourceNormalizationMachineField.Data)
    (vertices edgeCount remaining reverseStream stream scratch : List Bool) :
    run (m + 1)
      (cfg (some (.inr .splitCountRestore)) v
        {d with temp := List.replicate m true}
        vertices edgeCount remaining reverseStream stream scratch) =
    cfg (some (.inr .edges)) (setPop v none)
      {d with temp := []}
        vertices (List.replicate m true ++ edgeCount)
          (List.replicate m true ++ remaining) reverseStream stream scratch := by
  induction m generalizing v edgeCount remaining with
  | zero =>
      simpa using run_succ
        (splitRestore_nil v d vertices edgeCount remaining reverseStream stream scratch) 0
  | succ m ih =>
      rw [List.replicate_succ, run_succ
        (splitRestore_cons (List.replicate m true) v d
          vertices edgeCount remaining reverseStream stream scratch)]
      simpa only [List.replicate_succ, replicate_push, setPop] using
        ih (setPop v (some true)) (true :: edgeCount) (true :: remaining)

theorem count_run (m : ℕ) (cap suffix : List Bool) (hm : m ≤ cap.length)
    (vertices reverseStream stream scratch : List Bool) :
    ∃ t ≤ 20 * (cap.length + 1) * (m.bits.length + 1) + 2 * m + 3,
      run t (cfg (some (.inl (.inl .scan)))
        (SourceNormalizationMachineField.initialControl, .count, none)
        {input := EncodedCommunication.natField m ++ suffix, cap := cap}
        vertices [] [] reverseStream stream scratch) =
      cfg (some (.inr .edges))
        (setPop (SourceNormalizationMachineField.doneControl true, .count, none) none)
        {input := suffix, cap := cap}
        vertices (List.replicate m true) (List.replicate m true)
          reverseStream stream scratch := by
  obtain ⟨a, ha, hfield⟩ := field_run .count m cap suffix hm
    vertices [] [] reverseStream stream scratch
  have hafter := run_succ
    (afterField_count
      {input := suffix, unary := List.replicate m true, cap := cap}
      vertices [] [] reverseStream stream scratch) 0
  have hscan := splitScan_run m []
    (SourceNormalizationMachineField.doneControl true, .count, none)
    {input := suffix, cap := cap}
      vertices [] [] reverseStream stream scratch
  simp only [List.append_nil] at hscan
  have hrestore := splitRestore_run m
    (setPop (SourceNormalizationMachineField.doneControl true, .count, none) none)
    {input := suffix, cap := cap}
      vertices [] [] reverseStream stream scratch
  simp only [List.append_nil, setPop] at hrestore
  refine ⟨a + 1 + (m + 1) + (m + 1), by omega, ?_⟩
  exact (run_add ((run_add ((run_add hfield 1).trans hafter) (m + 1)).trans hscan)
    (m + 1)).trans hrestore

theorem edges_cons (rest : List Bool) (v : Control)
    (d : SourceNormalizationMachineField.Data)
    (vertices edgeCount reverseStream stream scratch : List Bool) :
    advance program
      (cfg (some (.inr .edges)) v d
        vertices edgeCount (true :: rest) reverseStream stream scratch) =
    cfg (some (.inl (.inl .scan))) (setPhase .left (setPop v (some true))) d
      vertices edgeCount rest reverseStream stream scratch := by
  simp only [advance, TM2.step, program, TM2.stepAux, cfg, setPop,
    Sum.elim_inr]
  simp only [show (![vertices, edgeCount, true :: rest, reverseStream, stream,
      scratch] : Fin 6 → List Bool) 2 = true :: rest by rfl,
    List.head?_cons, List.tail_cons, Option.isSome_some,
    Bool.cond_true, setPhase]
  simp only [update_right, Option.getD_some]
  congr 1
  funext k
  cases k with
  | inl k => fin_cases k <;> rfl
  | inr k => fin_cases k <;> rfl

theorem edges_nil (v : Control) (d : SourceNormalizationMachineField.Data)
    (vertices edgeCount reverseStream stream scratch : List Bool) :
    advance program
      (cfg (some (.inr .edges)) v d
        vertices edgeCount [] reverseStream stream scratch) =
    cfg (some (.inr .finishReverse)) (setPop v none) d
      vertices edgeCount [] reverseStream stream scratch := by
  simp only [advance, TM2.step, program, TM2.stepAux, cfg, setPop,
    Sum.elim_inr]
  simp only [show (![vertices, edgeCount, [], reverseStream, stream,
      scratch] : Fin 6 → List Bool) 2 = [] by rfl,
    List.head?_nil, List.tail_nil, Option.isSome_none,
    Bool.cond_false]
  simp only [update_right, Option.getD_some]
  simp only [go, TM2.stepAux]
  congr 1
  funext k
  cases k with
  | inl k => fin_cases k <;> rfl
  | inr k => fin_cases k <;> rfl

theorem emitLeft_step (v : Control) (d : SourceNormalizationMachineField.Data)
    (vertices edgeCount remaining reverseStream stream scratch : List Bool) :
    advance program (cfg (some (.inr .emitLeft)) v d
      vertices edgeCount remaining reverseStream stream scratch) =
    cfg (some (.inr .emitLeftUnary)) v d
      vertices edgeCount remaining reverseStream stream scratch := by
  rfl

theorem emitRight_step (v : Control) (d : SourceNormalizationMachineField.Data)
    (vertices edgeCount remaining reverseStream stream scratch : List Bool) :
    advance program (cfg (some (.inr .emitRight)) v d
      vertices edgeCount remaining reverseStream stream scratch) =
    cfg (some (.inr .emitRightUnary)) v d
      vertices edgeCount remaining reverseStream stream scratch := by
  rfl

theorem emitLeft_cons (xs : List Bool) (v : Control)
    (d : SourceNormalizationMachineField.Data)
    (vertices edgeCount remaining reverseStream stream scratch : List Bool) :
    advance program
      (cfg (some (.inr .emitLeftUnary)) v {d with unary := true :: xs}
        vertices edgeCount remaining reverseStream stream scratch) =
    cfg (some (.inr .emitLeftUnary)) (setPop v (some true))
      {d with unary := xs}
        vertices edgeCount remaining (true :: reverseStream) stream scratch := by
  simp only [advance, TM2.step, program, TM2.stepAux, cfg,
    SourceNormalizationMachineField.Data.stacks, Sum.elim_inl]
  simp only [show (![d.input,d.saved,d.value,d.budget,d.work,true :: xs,d.cap,d.temp] :
      SourceNormalizationMachineField.Stack → List Bool) 5 = true :: xs by rfl,
    List.head?_cons, List.tail_cons, Option.isSome_some,
    Bool.cond_true, Option.getD_some]
  simp only [setPop, Option.isSome_some, Bool.cond_true, go, TM2.stepAux]
  simp only [update_left, update_right]
  congr 1
  funext k
  cases k with
  | inl k => fin_cases k <;> rfl
  | inr k => fin_cases k <;> rfl

theorem emitRight_cons (xs : List Bool) (v : Control)
    (d : SourceNormalizationMachineField.Data)
    (vertices edgeCount remaining reverseStream stream scratch : List Bool) :
    advance program
      (cfg (some (.inr .emitRightUnary)) v {d with unary := true :: xs}
        vertices edgeCount remaining reverseStream stream scratch) =
    cfg (some (.inr .emitRightUnary)) (setPop v (some true))
      {d with unary := xs}
        vertices edgeCount remaining (true :: reverseStream) stream scratch := by
  simp only [advance, TM2.step, program, TM2.stepAux, cfg,
    SourceNormalizationMachineField.Data.stacks, Sum.elim_inl]
  simp only [show (![d.input,d.saved,d.value,d.budget,d.work,true :: xs,d.cap,d.temp] :
      SourceNormalizationMachineField.Stack → List Bool) 5 = true :: xs by rfl,
    List.head?_cons, List.tail_cons, Option.isSome_some,
    Bool.cond_true, Option.getD_some]
  simp only [setPop, Option.isSome_some, Bool.cond_true, go, TM2.stepAux]
  simp only [update_left, update_right]
  congr 1
  funext k
  cases k with
  | inl k => fin_cases k <;> rfl
  | inr k => fin_cases k <;> rfl

theorem emitLeft_nil (v : Control) (d : SourceNormalizationMachineField.Data)
    (vertices edgeCount remaining reverseStream stream scratch : List Bool) :
    advance program
      (cfg (some (.inr .emitLeftUnary)) v {d with unary := []}
        vertices edgeCount remaining reverseStream stream scratch) =
    cfg (some (.inl (.inl .scan))) (setPhase .right (setPop v none))
      {d with unary := []}
        vertices edgeCount remaining (false :: reverseStream) stream scratch := by
  simp only [advance, TM2.step, program, TM2.stepAux, cfg,
    SourceNormalizationMachineField.Data.stacks, Sum.elim_inl]
  simp only [show (![d.input,d.saved,d.value,d.budget,d.work,[],d.cap,d.temp] :
      SourceNormalizationMachineField.Stack → List Bool) 5 = [] by rfl,
    List.head?_nil, List.tail_nil, Option.isSome_none,
    Bool.cond_false, setPop, setPhase]
  simp only [update_left, update_right, Option.getD_some]
  congr 1
  funext k
  cases k with
  | inl k => fin_cases k <;> rfl
  | inr k => fin_cases k <;> rfl

theorem emitRight_nil (v : Control) (d : SourceNormalizationMachineField.Data)
    (vertices edgeCount remaining reverseStream stream scratch : List Bool) :
    advance program
      (cfg (some (.inr .emitRightUnary)) v {d with unary := []}
        vertices edgeCount remaining reverseStream stream scratch) =
    cfg (some (.inr .edges)) (setPop v none)
      {d with unary := []}
        vertices edgeCount remaining (false :: reverseStream) stream scratch := by
  simp only [advance, TM2.step, program, TM2.stepAux, cfg,
    SourceNormalizationMachineField.Data.stacks, Sum.elim_inl]
  simp only [show (![d.input,d.saved,d.value,d.budget,d.work,[],d.cap,d.temp] :
      SourceNormalizationMachineField.Stack → List Bool) 5 = [] by rfl,
    List.head?_nil, List.tail_nil, Option.isSome_none,
    Bool.cond_false, setPop]
  simp only [go, TM2.stepAux]
  simp only [update_left, update_right, Option.getD_some]
  congr 1
  funext k
  cases k with
  | inl k => fin_cases k <;> rfl
  | inr k => fin_cases k <;> rfl

theorem emitLeft_run (u : ℕ) (v : Control)
    (d : SourceNormalizationMachineField.Data)
    (vertices edgeCount remaining reverseStream stream scratch : List Bool) :
    run (u + 2)
      (cfg (some (.inr .emitLeft)) v
        {d with unary := List.replicate u true}
        vertices edgeCount remaining reverseStream stream scratch) =
    cfg (some (.inl (.inl .scan))) (setPhase .right (setPop v none))
      {d with unary := []}
        vertices edgeCount remaining
          (false :: List.replicate u true ++ reverseStream) stream scratch := by
  have hloop : ∀ w (acc : List Bool),
      run (u + 1)
        (cfg (some (.inr .emitLeftUnary)) w
          {d with unary := List.replicate u true}
          vertices edgeCount remaining acc stream scratch) =
      cfg (some (.inl (.inl .scan))) (setPhase .right (setPop w none))
        {d with unary := []}
          vertices edgeCount remaining
            (false :: List.replicate u true ++ acc) stream scratch := by
    induction u with
    | zero =>
        intro w acc
        simpa using run_succ
          (emitLeft_nil w d vertices edgeCount remaining acc stream scratch) 0
    | succ u ih =>
        intro w acc
        rw [List.replicate_succ, run_succ
          (emitLeft_cons (List.replicate u true) w d
            vertices edgeCount remaining acc stream scratch)]
        have h := ih (setPop w (some true)) (true :: acc)
        have hs : false :: List.replicate u true ++ true :: acc =
            false :: List.replicate (u + 1) true ++ acc := by
          simp [List.replicate_succ, List.append_assoc, replicate_push]
        rw [hs] at h
        simpa only [List.replicate_succ, setPop] using h
  have hstart := emitLeft_step v {d with unary := List.replicate u true}
    vertices edgeCount remaining reverseStream stream scratch
  exact (run_succ hstart (u + 1)).trans (hloop v reverseStream)

theorem emitRight_run (u : ℕ) (v : Control)
    (d : SourceNormalizationMachineField.Data)
    (vertices edgeCount remaining reverseStream stream scratch : List Bool) :
    run (u + 2)
      (cfg (some (.inr .emitRight)) v
        {d with unary := List.replicate u true}
        vertices edgeCount remaining reverseStream stream scratch) =
    cfg (some (.inr .edges)) (setPop v none)
      {d with unary := []}
        vertices edgeCount remaining
          (false :: List.replicate u true ++ reverseStream) stream scratch := by
  have hloop : ∀ w (acc : List Bool),
      run (u + 1)
        (cfg (some (.inr .emitRightUnary)) w
          {d with unary := List.replicate u true}
          vertices edgeCount remaining acc stream scratch) =
      cfg (some (.inr .edges)) (setPop w none)
        {d with unary := []}
          vertices edgeCount remaining
            (false :: List.replicate u true ++ acc) stream scratch := by
    induction u with
    | zero =>
        intro w acc
        simpa using run_succ
          (emitRight_nil w d vertices edgeCount remaining acc stream scratch) 0
    | succ u ih =>
        intro w acc
        rw [List.replicate_succ, run_succ
          (emitRight_cons (List.replicate u true) w d
            vertices edgeCount remaining acc stream scratch)]
        have h := ih (setPop w (some true)) (true :: acc)
        have hs : false :: List.replicate u true ++ true :: acc =
            false :: List.replicate (u + 1) true ++ acc := by
          simp [List.replicate_succ, List.append_assoc, replicate_push]
        rw [hs] at h
        simpa only [List.replicate_succ, setPop] using h
  have hstart := emitRight_step v {d with unary := List.replicate u true}
    vertices edgeCount remaining reverseStream stream scratch
  exact (run_succ hstart (u + 1)).trans (hloop v reverseStream)

theorem oneEdge_run (u w : ℕ) (cap suffix : List Bool)
    (hu : u ≤ cap.length) (hw : w ≤ cap.length)
    (remaining reverseStream : List Bool) (v : Control)
    (vertices edgeCount stream scratch : List Bool) :
    ∃ t ≤ 20 * (cap.length + 1) * (u.bits.length + 1) +
        20 * (cap.length + 1) * (w.bits.length + 1) + u + w + 7,
      run t
        (cfg (some (.inr .edges)) v
          {input := EncodedCommunication.natField u ++
            EncodedCommunication.natField w ++ suffix, cap := cap}
          vertices edgeCount (true :: remaining) reverseStream stream scratch) =
      cfg (some (.inr .edges))
        (setPop (SourceNormalizationMachineField.doneControl true, .right, none) none)
        {input := suffix, cap := cap}
          vertices edgeCount remaining
            ((EncodedGraph.unary w).reverse ++
              (EncodedGraph.unary u).reverse ++ reverseStream) stream scratch := by
  let tail := EncodedCommunication.natField w ++ suffix
  have hstep := edges_cons remaining v
    {input := EncodedCommunication.natField u ++ tail, cap := cap}
    vertices edgeCount reverseStream stream scratch
  obtain ⟨a, ha, hleft⟩ := field_run .left u cap tail hu
    vertices edgeCount remaining reverseStream stream scratch
  have hafterL := run_succ
    (afterField_left {input := tail, unary := List.replicate u true, cap := cap}
      vertices edgeCount remaining reverseStream stream scratch) 0
  have hemitL := emitLeft_run u
    (SourceNormalizationMachineField.doneControl true, .left, none)
    {input := tail, cap := cap}
      vertices edgeCount remaining reverseStream stream scratch
  obtain ⟨b, hb, hright⟩ := field_run .right w cap suffix hw
    vertices edgeCount remaining
      (false :: List.replicate u true ++ reverseStream) stream scratch
  have hafterR := run_succ
    (afterField_right {input := suffix, unary := List.replicate w true, cap := cap}
      vertices edgeCount remaining
        (false :: List.replicate u true ++ reverseStream) stream scratch) 0
  have hemitR := emitRight_run w
    (SourceNormalizationMachineField.doneControl true, .right, none)
    {input := suffix, cap := cap}
      vertices edgeCount remaining
        (false :: List.replicate u true ++ reverseStream) stream scratch
  refine ⟨1 + a + 1 + (u + 2) + b + 1 + (w + 2), by omega, ?_⟩
  have h₁ := (run_add (run_succ hstep 0) a).trans hleft
  have h₂ := (run_add h₁ 1).trans hafterL
  have h₃ := (run_add h₂ (u + 2)).trans hemitL
  have h₄ := (run_add h₃ b).trans hright
  have h₅ := (run_add h₄ 1).trans hafterR
  have h₆ := (run_add h₅ (w + 2)).trans hemitR
  simpa [tail, EncodedGraph.unary, List.reverse_append, List.append_assoc,
    List.reverse_replicate] using h₆

def edgeStream (ps : List (ℕ × ℕ)) : List Bool :=
  (ps.flatMap (fun p => [p.1, p.2])).flatMap EncodedGraph.unary

def edgeCost (capLength : ℕ) (p : ℕ × ℕ) : ℕ :=
  20 * (capLength + 1) * (p.1.bits.length + 1) +
  20 * (capLength + 1) * (p.2.bits.length + 1) + p.1 + p.2 + 7

theorem edgeCost_bound (N : ℕ) (p : ℕ × ℕ)
    (hp : p.1 ≤ N ∧ p.2 ≤ N) :
    edgeCost N p ≤ 50 * (N + 1)^2 := by
  have hu := UnaryBinaryEncoding.bits_length_le p.1
  have hv := UnaryBinaryEncoding.bits_length_le p.2
  dsimp [edgeCost]
  nlinarith [Nat.zero_le N]

theorem edgeCosts_bound (N : ℕ) (ps : List (ℕ × ℕ))
    (hp : ∀ p ∈ ps, p.1 ≤ N ∧ p.2 ≤ N) :
    (ps.map (edgeCost N)).sum ≤ ps.length * (50 * (N + 1)^2) := by
  induction ps with
  | nil => simp
  | cons p ps ih =>
      have hthis := edgeCost_bound N p (hp p (by simp))
      have htail := ih (fun q hq => hp q (by simp [hq]))
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      nlinarith

theorem edgeStream_length_bound (N : ℕ) (ps : List (ℕ × ℕ))
    (hp : ∀ p ∈ ps, p.1 ≤ N ∧ p.2 ≤ N) :
    (edgeStream ps).length ≤ ps.length * (2 * N + 2) := by
  induction ps with
  | nil => simp [edgeStream]
  | cons p ps ih =>
      have hthis := hp p (by simp)
      have htail := ih (fun q hq => hp q (by simp [hq]))
      simp only [edgeStream, List.flatMap_cons, List.flatMap_append,
        List.length_append, List.length_cons, List.length_nil,
        EncodedGraph.unary, List.flatMap_nil, List.length_replicate] at *
      nlinarith

theorem edgeLoop_run (ps : List (ℕ × ℕ)) (cap suffix : List Bool)
    (hbound : ∀ p ∈ ps, p.1 ≤ cap.length ∧ p.2 ≤ cap.length)
    (reverseStream : List Bool) (v : Control)
    (vertices edgeCount stream scratch : List Bool) :
    ∃ t ≤ (ps.map (edgeCost cap.length)).sum + 1,
      ∃ w : Control,
      run t
        (cfg (some (.inr .edges)) v
          {input := EncodedGraph.edgeFields ps ++ suffix, cap := cap}
          vertices edgeCount (List.replicate ps.length true)
            reverseStream stream scratch) =
      cfg (some (.inr .finishReverse)) w
        {input := suffix, cap := cap}
          vertices edgeCount []
            ((edgeStream ps).reverse ++ reverseStream) stream scratch := by
  induction ps generalizing v reverseStream with
  | nil =>
      refine ⟨1, by simp, setPop v none, ?_⟩
      simpa [EncodedGraph.edgeFields, edgeStream] using
        run_succ (edges_nil v {input := suffix, cap := cap}
          vertices edgeCount reverseStream stream scratch) 0
  | cons p ps ih =>
      have hp := hbound p (by simp)
      have hps : ∀ q ∈ ps, q.1 ≤ cap.length ∧ q.2 ≤ cap.length :=
        fun q hq => hbound q (by simp [hq])
      obtain ⟨a, ha, hone⟩ := oneEdge_run p.1 p.2 cap
        (EncodedGraph.edgeFields ps ++ suffix) hp.1 hp.2
        (List.replicate ps.length true) reverseStream v
        vertices edgeCount stream scratch
      obtain ⟨b, hb, w, htail⟩ := ih hps
        ((EncodedGraph.unary p.2).reverse ++
          (EncodedGraph.unary p.1).reverse ++ reverseStream)
        (setPop (SourceNormalizationMachineField.doneControl true, .right, none) none)
      refine ⟨a + b, ?_, w, ?_⟩
      · simp only [List.map_cons, List.sum_cons, edgeCost] at *
        omega
      · have h := (run_add hone b).trans htail
        simpa [EncodedGraph.edgeFields, edgeStream, List.reverse_append,
          List.append_assoc, setPop] using h

theorem reverse_cons (b : Bool) (xs : List Bool) (v : Control)
    (d : SourceNormalizationMachineField.Data)
    (vertices edgeCount remaining stream scratch : List Bool) :
    advance program
      (cfg (some (.inr .finishReverse)) v d
        vertices edgeCount remaining (b :: xs) stream scratch) =
    cfg (some (.inr .finishReverse)) (setPop v (some b)) d
      vertices edgeCount remaining xs (b :: stream) scratch := by
  simp only [advance, TM2.step, program, TM2.stepAux, cfg, Sum.elim_inr]
  simp only [show (![vertices, edgeCount, remaining, b :: xs, stream,
      scratch] : Fin 6 → List Bool) 3 = b :: xs by rfl,
    List.head?_cons, List.tail_cons, Option.isSome_some,
    Bool.cond_true, Option.getD_some, setPop, go, TM2.stepAux]
  simp only [update_right]
  congr 1
  funext k
  cases k with
  | inl k => fin_cases k <;> rfl
  | inr k => fin_cases k <;> rfl

theorem reverse_nil (v : Control) (d : SourceNormalizationMachineField.Data)
    (vertices edgeCount remaining stream scratch : List Bool) :
    advance program
      (cfg (some (.inr .finishReverse)) v d
        vertices edgeCount remaining [] stream scratch) =
    cfg (some (.inr .clearCap)) (setPop v none) d
      vertices edgeCount remaining [] stream scratch := by
  simp only [advance, TM2.step, program, TM2.stepAux, cfg, Sum.elim_inr]
  simp only [show (![vertices, edgeCount, remaining, [], stream,
      scratch] : Fin 6 → List Bool) 3 = [] by rfl,
    List.head?_nil, List.tail_nil, Option.isSome_none,
    Bool.cond_false, setPop, go, TM2.stepAux]
  simp only [update_right, Option.getD_some]
  congr 1
  funext k
  cases k with
  | inl k => fin_cases k <;> rfl
  | inr k => fin_cases k <;> rfl

theorem reverse_run (xs : List Bool) (v : Control)
    (d : SourceNormalizationMachineField.Data)
    (vertices edgeCount remaining stream scratch : List Bool) :
    run (xs.length + 1)
      (cfg (some (.inr .finishReverse)) v d
        vertices edgeCount remaining xs stream scratch) =
    cfg (some (.inr .clearCap)) (setPop v none) d
      vertices edgeCount remaining [] (xs.reverse ++ stream) scratch := by
  induction xs generalizing v stream with
  | nil =>
      simpa using run_succ
        (reverse_nil v d vertices edgeCount remaining stream scratch) 0
  | cons b xs ih =>
      rw [List.length_cons, run_succ
        (reverse_cons b xs v d vertices edgeCount remaining stream scratch)]
      simpa [List.reverse_cons, List.append_assoc, setPop] using
        ih (setPop v (some b)) (b :: stream)

theorem clearCap_cons (b : Bool) (xs : List Bool) (v : Control)
    (d : SourceNormalizationMachineField.Data)
    (vertices edgeCount remaining reverseStream stream scratch : List Bool) :
    advance program
      (cfg (some (.inr .clearCap)) v {d with cap := b :: xs}
        vertices edgeCount remaining reverseStream stream scratch) =
    cfg (some (.inr .clearCap)) (setPop v (some b)) {d with cap := xs}
      vertices edgeCount remaining reverseStream stream scratch := by
  simp only [advance, TM2.step, program, TM2.stepAux, cfg,
    SourceNormalizationMachineField.Data.stacks, Sum.elim_inl]
  simp only [show (![d.input,d.saved,d.value,d.budget,d.work,d.unary,b :: xs,d.temp] :
      SourceNormalizationMachineField.Stack → List Bool) 6 = b :: xs by rfl,
    List.head?_cons, List.tail_cons, Option.isSome_some,
    Bool.cond_true, setPop, go, TM2.stepAux]
  simp only [update_left]
  simp only [Option.getD_some]
  congr 1
  funext k
  cases k with
  | inl k => fin_cases k <;> rfl
  | inr k => fin_cases k <;> rfl

theorem clearCap_nil (v : Control) (d : SourceNormalizationMachineField.Data)
    (vertices edgeCount remaining reverseStream stream scratch : List Bool) :
    advance program
      (cfg (some (.inr .clearCap)) v {d with cap := []}
        vertices edgeCount remaining reverseStream stream scratch) =
    cfg none (doneControl true) {d with cap := []}
      vertices edgeCount remaining reverseStream stream scratch := by
  simp only [advance, TM2.step, program, TM2.stepAux, cfg,
    SourceNormalizationMachineField.Data.stacks, Sum.elim_inl]
  simp only [show (![d.input,d.saved,d.value,d.budget,d.work,d.unary,[],d.temp] :
      SourceNormalizationMachineField.Stack → List Bool) 6 = [] by rfl,
    List.head?_nil, List.tail_nil, Option.isSome_none,
    Bool.cond_false, doneControl]
  simp only [update_left, setPop, Option.isSome_none, Bool.cond_false,
    Option.getD_some]
  congr 1
  funext k
  cases k with
  | inl k => fin_cases k <;> rfl
  | inr k => fin_cases k <;> rfl

theorem clearCap_run (cap : List Bool) (v : Control)
    (d : SourceNormalizationMachineField.Data)
    (vertices edgeCount remaining reverseStream stream scratch : List Bool) :
    run (cap.length + 1)
      (cfg (some (.inr .clearCap)) v {d with cap := cap}
        vertices edgeCount remaining reverseStream stream scratch) =
    cfg none (doneControl true) {d with cap := []}
      vertices edgeCount remaining reverseStream stream scratch := by
  induction cap generalizing v with
  | nil =>
      simpa using run_succ
        (clearCap_nil v d vertices edgeCount remaining reverseStream stream scratch) 0
  | cons b cap ih =>
      rw [List.length_cons, run_succ
        (clearCap_cons b cap v d vertices edgeCount remaining reverseStream stream scratch)]
      exact ih (setPop v (some b))

/-- Semantic specification for a successfully decoded graph. -/
def endpointStream (g : EncodedGraph.Graph) : List Bool :=
  (g.edges.flatMap (fun p => [p.1, p.2])).flatMap EncodedGraph.unary

theorem endpointStream_eq_mark (g : EncodedGraph.Graph) :
    endpointStream g =
      SourceNormalizationMachineMark.endpointStream
        (g.edges.flatMap (fun p => [p.1, p.2])) := by
  let endpoints := g.edges.flatMap (fun p => [p.1, p.2])
  change endpoints.flatMap EncodedGraph.unary =
    SourceNormalizationMachineMark.endpointStream endpoints
  induction endpoints with
  | nil => rfl
  | cons u us ih => simp [SourceNormalizationMachineMark.endpointStream, ih]

def graphCost (g : EncodedGraph.Graph) : ℕ :=
  let N := (EncodedGraph.encode g).length
  let m := g.edges.length
  (2 * N + 2) + (g.vertices + 1) +
    (20 * (N + 1) * (m.bits.length + 1) + 2 * m + 3) +
    ((g.edges.map (edgeCost N)).sum + 1) +
    (edgeStream g.edges).length + 1 + N + 1

/-- Exact valid-code execution of the physical graph parser. The untouched
ambient original graph and original variable word are framed by callers. -/
theorem decode_valid_run (g : EncodedGraph.Graph) (hg : g.Valid) :
    ∃ t ≤ graphCost g,
      run t (start (EncodedGraph.encode g)) =
        cfg none (doneControl true) {}
          (List.replicate g.vertices true)
          (List.replicate g.edges.length true) [] []
          (endpointStream g) [] := by
  let N := (EncodedGraph.encode g).length
  let m := g.edges.length
  have hn : g.vertices ≤ N := by
    have h := EncodedGraph.encode_length_lower g
    dsimp [N]
    omega
  have hm : m ≤ N := by
    have h := EncodedGraph.encode_length_lower g
    dsimp [N, m]
    omega
  have hp : ∀ p ∈ g.edges, p.1 ≤ N ∧ p.2 ≤ N := by
    intro p hmem
    have h := hg p hmem
    exact ⟨h.1.le.trans hn, h.2.1.le.trans hn⟩
  have hcap := cap_run (EncodedGraph.encode g)
  have hvertices := vertices_run g.vertices
    (EncodedCommunication.natField m ++ EncodedGraph.edgeFields g.edges)
    (setPop (SourceNormalizationMachineField.initialControl, .count, none) none)
    {cap := List.replicate N true} [] [] [] [] [] []
  have hcount := count_run m (List.replicate N true)
    (EncodedGraph.edgeFields g.edges) (by simpa [N] using hm)
    (List.replicate g.vertices true) [] [] []
  obtain ⟨a, ha, w, hloop⟩ := edgeLoop_run g.edges
    (List.replicate N true) [] (by simpa only [List.length_replicate] using hp)
    [] (setPop (SourceNormalizationMachineField.doneControl true, .count, none) none)
    (List.replicate g.vertices true) (List.replicate m true) [] []
  have hreverse := reverse_run (edgeStream g.edges).reverse w
    ({cap := List.replicate N true} : SourceNormalizationMachineField.Data)
    (List.replicate g.vertices true) (List.replicate m true) [] [] []
  have hclear := clearCap_run (List.replicate N true) (setPop w none)
    ({} : SourceNormalizationMachineField.Data)
    (List.replicate g.vertices true) (List.replicate m true) [] []
    (edgeStream g.edges) []
  have h₁ : run (2 * N + 2 + (g.vertices + 1))
      (start (EncodedGraph.encode g)) =
      cfg (some (.inl (.inl .scan)))
        (SourceNormalizationMachineField.initialControl, .count, none)
        {input := EncodedCommunication.natField m ++ EncodedGraph.edgeFields g.edges,
          cap := List.replicate N true}
        (List.replicate g.vertices true) [] [] [] [] [] := by
    have hv : run (g.vertices + 1)
        (cfg (some (.inr .vertices))
          (setPop (SourceNormalizationMachineField.initialControl, .count, none) none)
          {input := EncodedGraph.encode g,
            cap := List.replicate (EncodedGraph.encode g).length true}
          [] [] [] [] [] []) =
        cfg (some (.inl (.inl .scan)))
          (SourceNormalizationMachineField.initialControl, .count, none)
          {input := EncodedCommunication.natField m ++ EncodedGraph.edgeFields g.edges,
            cap := List.replicate N true}
          (List.replicate g.vertices true) [] [] [] [] [] := by
      simpa [N, m, EncodedGraph.encode, List.append_assoc,
        setPhase, setPop] using hvertices
    exact (run_add hcap (g.vertices + 1)).trans hv
  obtain ⟨b, hb, hc⟩ := hcount
  have h₂ := (run_add h₁ b).trans hc
  have hl : run a
      (cfg (some (.inr .edges))
        (setPop (SourceNormalizationMachineField.doneControl true, .count, none) none)
        {input := EncodedGraph.edgeFields g.edges, cap := List.replicate N true}
        (List.replicate g.vertices true) (List.replicate m true)
        (List.replicate m true) [] [] []) =
      cfg (some (.inr .finishReverse)) w
        {cap := List.replicate N true}
        (List.replicate g.vertices true) (List.replicate m true) []
        (edgeStream g.edges).reverse [] [] := by
    simpa [m] using hloop
  have h₃ := (run_add h₂ a).trans hl
  have hr : run ((edgeStream g.edges).reverse.length + 1)
      (cfg (some (.inr .finishReverse)) w
        {cap := List.replicate N true}
        (List.replicate g.vertices true) (List.replicate m true) []
        (edgeStream g.edges).reverse [] []) =
      cfg (some (.inr .clearCap)) (setPop w none)
        {cap := List.replicate N true}
        (List.replicate g.vertices true) (List.replicate m true) [] []
        (edgeStream g.edges) [] := by
    simpa using hreverse
  have h₄ := (run_add h₃ ((edgeStream g.edges).reverse.length + 1)).trans hr
  have h₅ := (run_add h₄ (N + 1)).trans
    (by simpa only [List.length_replicate] using hclear)
  refine ⟨2 * N + 2 + (g.vertices + 1) + b + a +
    ((edgeStream g.edges).reverse.length + 1) + (N + 1), ?_, ?_⟩
  · simp only [graphCost, N, m, List.length_reverse] at *
    simp only [List.length_replicate] at ha
    simp only [List.length_replicate] at hb
    omega
  · simpa [endpointStream, edgeStream, N, m, List.reverse_reverse,
      List.append_nil, setPop, doneControl] using h₅

theorem graphCost_polynomial (g : EncodedGraph.Graph) (hg : g.Valid) :
    graphCost g ≤ 100 * ((EncodedGraph.encode g).length + 1)^3 := by
  let N := (EncodedGraph.encode g).length
  let m := g.edges.length
  have hlower := EncodedGraph.encode_length_lower g
  have hn : g.vertices ≤ N := by dsimp [N]; omega
  have hm : m ≤ N := by dsimp [N, m]; omega
  have hp : ∀ p ∈ g.edges, p.1 ≤ N ∧ p.2 ≤ N := by
    intro p hmem
    have h := hg p hmem
    exact ⟨h.1.le.trans hn, h.2.1.le.trans hn⟩
  have hc := edgeCosts_bound N g.edges hp
  have hs := edgeStream_length_bound N g.edges hp
  have hb := UnaryBinaryEncoding.bits_length_le m
  have hc' : (g.edges.map (edgeCost N)).sum ≤ 50 * (N + 1)^3 := by
    calc
      _ ≤ m * (50 * (N + 1)^2) := by simpa [m] using hc
      _ ≤ (N + 1) * (50 * (N + 1)^2) := Nat.mul_le_mul_right _ (by omega)
      _ = 50 * (N + 1)^3 := by ring
  have hs' : (edgeStream g.edges).length ≤ (N + 1) * (2 * N + 2) := by
    calc
      _ ≤ m * (2 * N + 2) := by simpa [m] using hs
      _ ≤ (N + 1) * (2 * N + 2) := Nat.mul_le_mul_right _ (by omega)
  have hcount :
      20 * (N + 1) * (m.bits.length + 1) + 2 * m + 3 ≤
        20 * (N + 1)^2 + 2 * N + 3 := by
    have hprod := Nat.mul_le_mul_left (20 * (N + 1))
      (show m.bits.length + 1 ≤ N + 1 by omega)
    nlinarith
  dsimp [graphCost, N, m]
  nlinarith [sq_nonneg (N : ℤ)]

theorem reject_run (v : Control) (d : SourceNormalizationMachineField.Data)
    (vertices edgeCount remaining reverseStream stream scratch : List Bool) :
    run 1 (cfg (some (.inr .reject)) v d
      vertices edgeCount remaining reverseStream stream scratch) =
      cfg none (doneControl false) d
        vertices edgeCount remaining reverseStream stream scratch := by
  simp [run, advance, TM2.step, program, TM2.stepAux, cfg, doneControl]

theorem guarded_reject_run :
    run 2 (guardedStart [false]) =
      cfg none (doneControl false) {} [] [] [] [] [] [] := by
  exact (run_succ gate_false 1).trans
    (reject_run _ ({} : SourceNormalizationMachineField.Data) [] [] [] [] [] [])

theorem guarded_valid_run (g : EncodedGraph.Graph) (hg : g.Valid) :
    ∃ t ≤ 101 * ((EncodedGraph.encode g).length + 1)^3,
      run t (guardedStart (true :: EncodedGraph.encode g)) =
        cfg none (doneControl true) {}
          (List.replicate g.vertices true)
          (List.replicate g.edges.length true) [] []
          (endpointStream g) [] := by
  obtain ⟨t, ht, he⟩ := decode_valid_run g hg
  have hc := graphCost_polynomial g hg
  refine ⟨t + 1, ?_, ?_⟩
  · have hpos : 0 < ((EncodedGraph.encode g).length + 1)^3 := by positivity
    omega
  · exact (run_succ (gate_true (EncodedGraph.encode g)) t).trans he

end EthInapproximability.CurrentPaper.SourceNormalizationMachineDecode
