import EthInapproximability.CurrentPaper.EncodedCNF
import EthInapproximability.CurrentPaper.ProtocolBinaryHeader
import EthInapproximability.CurrentPaper.ProtocolBoundedUnary
import EthInapproximability.CurrentPaper.BitMachineSubroutine
import EthInapproximability.CurrentPaper.BitMachineSubroutineRenaming

/-!
# A finite-stack validator for the ordered three-CNF encoding (unit 4, B4-S1)

Source: frozen v8 `06-eth.tex:238-242` ("Malformed strings reject by the fixed
convention"), the ordered three-CNF convention of `EncodedCNF`, and the
bit-machine convention of `06-eth.tex`. The machine is the admitted
`EncodedGraphMachine` controller with its per-edge block replaced by a
per-clause block of three literals: a sign bit, a canonical binary index
field, and a strict bound `index < n` checked by the admitted bounded unary
converter against a charged copy of the unary variable count. The input is
retained on a separate stack. A successful output is `true :: input`; a
rejected output is `[false]`. The definitions contain no unbounded register.

Imports: admitted production modules only (shared with Paper A).
-/

namespace EthInapproximability.CurrentPaper.CNFValidator

open Turing TM2.Stmt BitMachineEncoding BitMachineComposition

inductive Field where
  | count | lit0 | lit1 | lit2
  deriving DecidableEq, Fintype

inductive OuterLabel where
  | save | restore | vertices | afterHeader | copyVertices | restoreVertices
  | endpointCap | afterBound | clearValue | clearCap | clearWork | store
  | clauses | sign | finalCheck | accept | reject
  deriving DecidableEq, Fintype

abbrev Stack := Fin 15
abbrev Label := ProtocolBinaryHeader.Label ⊕
  (ProtocolBoundedUnary.Label ⊕ OuterLabel)
abbrev OuterControl := Field × Option Bool × Option Bool
abbrev Control := ProtocolBinaryHeader.Control ×
  (ProtocolBoundedUnary.Control × OuterControl)
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control
abbrev Statement := TM2.Stmt (fun _ : Stack => Bool) Label Control

def outer (l : OuterLabel) : Label := .inr (.inr l)

def popped (v : Control) : Option Bool := v.2.2.2.1
def popped₂ (v : Control) : Option Bool := v.2.2.2.2
def field (v : Control) : Field := v.2.2.1
def setPop (v : Control) (b : Option Bool) : Control :=
  (v.1, v.2.1, v.2.2.1, b, v.2.2.2.2)
def setPop₂ (v : Control) (b : Option Bool) : Control :=
  (v.1, v.2.1, v.2.2.1, v.2.2.2.1, b)
def setField (v : Control) (f : Field) : Control :=
  (v.1, v.2.1, f, v.2.2.2)

def go (l : OuterLabel) : Statement := goto (fun _ => outer l)
def fail : Statement := go .reject
def readHeader : Statement :=
  load (fun v => ((none, none), v.2)) (goto (fun _ => .inl .scan))
def readBounded : Statement :=
  load (fun v => (v.1, (none, false), v.2.2))
    (goto (fun _ => .inr (.inl .zeroScan)))

/-- Move a stack to another stack, reversing it, one cell per transition. -/
def move (source target : Stack) (again next : OuterLabel) : Statement :=
  pop source setPop
    (branch (fun v => (popped v).isSome)
      (push target (fun v => (popped v).getD false) (go again)) (go next))

def clear (source : Stack) (again next : OuterLabel) : Statement :=
  pop source setPop (branch (fun v => (popped v).isSome) (go again) (go next))

/-- Positions 0--2 are the header reader's source, scratch, and output.
Positions 2--5 are the bounded converter's input, budget, scratch, and output.
The other stacks hold the original input, the unary variable count, the
remaining clause counter, two unused stacks (kept so that the stack layout is
literally the admitted graph validator's), two transfer buffers, the final
output, and an unused spare. -/
def boundPermutation : Fin 15 ≃ Fin 15 where
  toFun k := match k.val with
    | 0 => 2 | 1 => 3 | 2 => 4 | 3 => 5 | 4 => 0 | 5 => 1 | _ => k
  invFun k := match k.val with
    | 0 => 4 | 1 => 5 | 2 => 0 | 3 => 1 | 4 => 2 | 5 => 3 | _ => k
  left_inv := by intro k; fin_cases k <;> rfl
  right_inv := by intro k; fin_cases k <;> rfl

def boundStack : (Fin 4 ⊕ Fin 11) ≃ Stack :=
  finSumFinEquiv.trans boundPermutation

def boundLabel :
    (ProtocolBoundedUnary.Label ⊕ (ProtocolBinaryHeader.Label ⊕ OuterLabel)) ≃ Label where
  toFun := Sum.elim (fun l => .inr (.inl l))
    (Sum.elim Sum.inl (fun l => .inr (.inr l)))
  invFun := Sum.elim (fun l => .inr (.inl l))
    (Sum.elim Sum.inl (fun l => .inr (.inr l)))
  left_inv := by intro l; rcases l with l | (l | l) <;> rfl
  right_inv := by intro l; rcases l with l | (l | l) <;> rfl

def boundControl :
    (ProtocolBoundedUnary.Control × (ProtocolBinaryHeader.Control × OuterControl)) ≃
      Control where
  toFun v := (v.2.1, v.1, v.2.2)
  invFun v := (v.2.1, v.1, v.2.2)
  left_inv := by intro v; rfl
  right_inv := by intro v; rfl

def outerProgram : OuterLabel → Statement
  | .save => pop 0 setPop
      (branch (fun v => (popped v).isSome)
        (push 6 (fun v => (popped v).getD false)
          (push 11 (fun v => (popped v).getD false)
            (push 3 (fun _ => true) (go .save)))) (go .restore))
  | .restore => move 11 0 .restore .vertices
  | .vertices => pop 0 setPop
      (branch (fun v => (popped v).isSome)
        (branch (fun v => (popped v).getD false)
          (push 7 (fun _ => true) (go .vertices))
          (load (fun v => setField v .count) readHeader)) fail)
  | .afterHeader => pop 2 setPop
      (branch (fun v => (popped v).getD false)
        (branch (fun v => decide (field v = .count)) readBounded (go .copyVertices)) fail)
  | .copyVertices => pop 7 setPop
      (branch (fun v => (popped v).isSome)
        (push 12 (fun _ => true) (push 3 (fun _ => true) (go .copyVertices)))
        (go .restoreVertices))
  | .restoreVertices => move 12 7 .restoreVertices .endpointCap
  | .endpointCap => pop 3 setPop
      (branch (fun v => (popped v).isSome) readBounded fail)
  | .afterBound => pop 5 setPop
      (branch (fun v => (popped v).getD false) (go .clearValue) fail)
  | .clearValue => clear 2 .clearValue .clearCap
  | .clearCap => clear 3 .clearCap .clearWork
  | .clearWork => clear 4 .clearWork .store
  | .store => pop 5 setPop
      (branch (fun v => (popped v).isSome)
        (branch (fun v => decide (field v = .count)) (push 8 (fun _ => true) (go .store))
          (go .store))
        (branch (fun v => decide (field v = .count)) (go .clauses)
          (branch (fun v => decide (field v = .lit0))
            (load (fun v => setField v .lit1) (go .sign))
            (branch (fun v => decide (field v = .lit1))
              (load (fun v => setField v .lit2) (go .sign)) (go .clauses)))))
  | .clauses => pop 8 setPop
      (branch (fun v => (popped v).isSome)
        (load (fun v => setField v .lit0) (go .sign)) (go .finalCheck))
  | .sign => pop 0 setPop
      (branch (fun v => (popped v).isSome) readHeader fail)
  | .finalCheck => pop 0 setPop
      (branch (fun v => (popped v).isSome) fail (go .accept))
  | .accept => pop 6 setPop
      (branch (fun v => (popped v).isSome)
        (push 13 (fun v => (popped v).getD false) (go .accept))
        (push 13 (fun _ => true) halt))
  | .reject => push 13 (fun _ => false) halt

def program : Label → Statement
  | .inl l => renameStmt (finSumFinEquiv : (Fin 3 ⊕ Fin 12) ≃ Fin 15)
      (Equiv.refl _) (Equiv.refl _)
      (liftStmt (some (.inr OuterLabel.afterHeader)) (ProtocolBinaryHeader.program l))
  | .inr (.inl l) => renameStmt boundStack boundLabel boundControl
      (liftStmt (some (.inr OuterLabel.afterBound)) (ProtocolBoundedUnary.program l))
  | .inr (.inr l) => outerProgram l

def initialControl : Control := ((none, none), (none, false), .count, none, none)

noncomputable def machine : BitMachine.Machine :=
  ofFinite 0 13 (outer .save) initialControl program

def run (n : Nat) (c : Config) : Config := ((advance program)^[n]) c

/-- The validator's specified output: `true :: input` on a canonical valid
ordered three-CNF word, and `[false]` on every other bitstring. -/
def result (input : List Bool) : List Bool :=
  if (EncodedCNF.decode input).isSome then true :: input else [false]

/-- Named stack contents used only in the correctness proof. They are not
machine registers: the actual program above has finite control. -/
structure Data where
  input : List Bool := []
  saved : List Bool := []
  value : List Bool := []
  cap : List Bool := []
  work : List Bool := []
  unary : List Bool := []
  original : List Bool := []
  vertices : List Bool := []
  clauses : List Bool := []
  spareA : List Bool := []
  spareB : List Bool := []
  temp : List Bool := []
  scratch : List Bool := []
  output : List Bool := []
  spare : List Bool := []

def Data.stacks (d : Data) : Stack → List Bool :=
  ![d.input, d.saved, d.value, d.cap, d.work, d.unary, d.original,
    d.vertices, d.clauses, d.spareA, d.spareB, d.temp, d.scratch, d.output, d.spare]

def cfg (l : Option Label) (v : Control) (d : Data) : Config :=
  ⟨l, v, d.stacks⟩

theorem run_succ {c c' : Config} (h : advance program c = c') (n : Nat) :
    run (n + 1) c = run n c' := by
  exact (Function.iterate_succ_apply _ _ _).trans (congrArg (run n) h)

theorem run_add {c c' : Config} {n : Nat} (h : run n c = c') (m : Nat) :
    run (n + m) c = run m c' := by
  rw [Nat.add_comm, run, Function.iterate_add_apply]
  exact congrArg (run m) h

theorem save_cons (b : Bool) (xs : List Bool) (v : Control) (d : Data) :
    advance program (cfg (some (outer .save)) v {d with input := b :: xs}) =
      cfg (some (outer .save)) (setPop v (some b))
        {d with input := xs, original := b :: d.original, temp := b :: d.temp, cap := true :: d.cap} := by
  simp [advance, TM2.step, program, outerProgram, outer, TM2.stepAux,
    cfg, Data.stacks, popped, setPop, go]
  funext k
  fin_cases k <;> rfl

theorem save_nil (v : Control) (d : Data) :
    advance program (cfg (some (outer .save)) v {d with input := []}) =
      cfg (some (outer .restore)) (setPop v none) {d with input := []} := by
  simp [advance, TM2.step, program, outerProgram, outer, TM2.stepAux,
    cfg, Data.stacks, popped, setPop, go]

theorem save_run (xs : List Bool) (v : Control) (d : Data) :
    run (xs.length + 1) (cfg (some (outer .save)) v {d with input := xs}) =
      cfg (some (outer .restore)) (setPop v none)
        {d with input := [], original := xs.reverse ++ d.original, temp := xs.reverse ++ d.temp,
                cap := List.replicate xs.length true ++ d.cap} := by
  induction xs generalizing v d with
  | nil => simpa using run_succ (save_nil v d) 0
  | cons b xs ih =>
      rw [List.length_cons, run_succ (save_cons b xs v d)]
      rw [ih (setPop v (some b)) {d with original := b :: d.original, temp := b :: d.temp, cap := true :: d.cap}]
      simp [List.reverse_cons, List.append_assoc, List.replicate_succ, cfg, setPop]
      congr 2
      induction xs.length with
      | zero => rfl
      | succ n ih => simpa [List.replicate_succ] using congrArg (true :: ·) ih

theorem restore_cons (b : Bool) (xs : List Bool) (v : Control) (d : Data) :
    advance program (cfg (some (outer .restore)) v {d with temp := b :: xs}) =
      cfg (some (outer .restore)) (setPop v (some b))
        {d with temp := xs, input := b :: d.input} := by
  simp [advance, TM2.step, program, outerProgram, outer, TM2.stepAux,
    cfg, Data.stacks, move, popped, setPop, go]
  funext k
  fin_cases k <;> rfl

theorem restore_nil (v : Control) (d : Data) :
    advance program (cfg (some (outer .restore)) v {d with temp := []}) =
      cfg (some (outer .vertices)) (setPop v none) {d with temp := []} := by
  simp [advance, TM2.step, program, outerProgram, outer, TM2.stepAux,
    cfg, Data.stacks, move, popped, setPop, go]

theorem restore_run (xs : List Bool) (v : Control) (d : Data) :
    run (xs.length + 1) (cfg (some (outer .restore)) v {d with temp := xs}) =
      cfg (some (outer .vertices)) (setPop v none)
        {d with temp := [], input := xs.reverse ++ d.input} := by
  induction xs generalizing v d with
  | nil => simpa using run_succ (restore_nil v d) 0
  | cons b xs ih =>
      rw [List.length_cons, run_succ (restore_cons b xs v d)]
      rw [ih (setPop v (some b)) {d with input := b :: d.input}]
      simp [List.reverse_cons, List.append_assoc, cfg, setPop]

/-- The literal input-copying prologue takes exactly twice its length plus
two transitions, preserving the input and charging one budget cell per bit. -/
theorem startup (input : List Bool) :
    run (2 * input.length + 2) (rawInit 0 (outer .save) initialControl input) =
      cfg (some (outer .vertices)) initialControl
        {input := input, original := input.reverse, cap := List.replicate input.length true} := by
  have hi : rawInit 0 (outer .save) initialControl input =
      cfg (some (outer .save)) initialControl {input := input} := by
    unfold rawInit cfg
    congr 1
    funext k
    fin_cases k <;> rfl
  rw [hi, show 2 * input.length + 2 = (input.length + 1) + (input.length + 1) by omega]
  have hs := save_run input initialControl {}
  simp only [List.append_nil] at hs
  rw [run_add hs]
  simpa [cfg, initialControl, setPop] using restore_run input.reverse
    (setPop initialControl none)
    {input := [], original := input.reverse, cap := List.replicate input.length true}

def headerControl (v : Control) : Control :=
  ((none, none), v.2.1, .count, some false, v.2.2.2.2)

theorem vertices_true (xs : List Bool) (v : Control) (d : Data) :
    advance program (cfg (some (outer .vertices)) v {d with input := true :: xs}) =
      cfg (some (outer .vertices)) (setPop v (some true))
        {d with input := xs, vertices := true :: d.vertices} := by
  simp [advance, TM2.step, program, outerProgram, outer, TM2.stepAux,
    cfg, Data.stacks, popped, setPop, go]
  funext k
  fin_cases k <;> rfl

theorem vertices_false (xs : List Bool) (v : Control) (d : Data) :
    advance program (cfg (some (outer .vertices)) v {d with input := false :: xs}) =
      cfg (some (.inl .scan)) (headerControl v) {d with input := xs} := by
  simp [advance, TM2.step, program, outerProgram, outer, TM2.stepAux,
    cfg, Data.stacks, popped, setPop, setField, headerControl, readHeader]
  funext k
  fin_cases k <;> rfl

theorem vertices_nil (v : Control) (d : Data) :
    advance program (cfg (some (outer .vertices)) v {d with input := []}) =
      cfg (some (outer .reject)) (setPop v none) {d with input := []} := by
  simp [advance, TM2.step, program, outerProgram, outer, TM2.stepAux,
    cfg, Data.stacks, popped, setPop, go, fail]

theorem vertices_run (n : Nat) (rest : List Bool) (v : Control) (d : Data) :
    run (n + 1) (cfg (some (outer .vertices)) v
      {d with input := EncodedGraph.unary n ++ rest}) =
        cfg (some (.inl .scan)) (headerControl v)
          {d with input := rest, vertices := List.replicate n true ++ d.vertices} := by
  induction n generalizing v d with
  | zero => simpa [EncodedGraph.unary] using run_succ (vertices_false rest v d) 0
  | succ n ih =>
      have hs : EncodedGraph.unary (n + 1) ++ rest =
          true :: (EncodedGraph.unary n ++ rest) := by
        simp [EncodedGraph.unary, List.replicate_succ]
      rw [hs, run_succ (vertices_true (EncodedGraph.unary n ++ rest) v d)]
      rw [ih (setPop v (some true)) {d with vertices := true :: d.vertices}]
      have hu : List.replicate n true ++ true :: d.vertices =
          List.replicate (n + 1) true ++ d.vertices := by
        rw [List.replicate_add, List.append_assoc]
        rfl
      simp [headerControl, setPop, hu]

theorem vertices_unterminated (n : Nat) (v : Control) (d : Data) :
    run (n + 1) (cfg (some (outer .vertices)) v
      {d with input := List.replicate n true}) =
        cfg (some (outer .reject)) (setPop v none)
          {d with input := [], vertices := List.replicate n true ++ d.vertices} := by
  induction n generalizing v d with
  | zero => simpa using run_succ (vertices_nil v d) 0
  | succ n ih =>
      rw [List.replicate_succ, run_succ (vertices_true (List.replicate n true) v d)]
      rw [ih (setPop v (some true)) {d with vertices := true :: d.vertices}]
      have hu : List.replicate n true ++ true :: d.vertices =
          List.replicate (n + 1) true ++ d.vertices := by
        rw [List.replicate_add, List.append_assoc]
        rfl
      simp [setPop, hu, List.replicate_succ]

theorem readUnary_failure (input : List Bool)
    (h : EncodedGraph.readUnary input = none) :
    input = List.replicate input.length true := by
  induction input with
  | nil => rfl
  | cons b xs ih =>
      cases b with
      | false => simp [EncodedGraph.readUnary] at h
      | true =>
          cases hr : EncodedGraph.readUnary xs with
          | none => simpa [List.replicate_succ] using congrArg (true :: ·) (ih hr)
          | some p => simp [EncodedGraph.readUnary, hr] at h

theorem reject_step (v : Control) (d : Data) :
    advance program (cfg (some (outer .reject)) v d) =
      cfg none v {d with output := false :: d.output} := by
  simp [advance, TM2.step, program, outerProgram, outer, TM2.stepAux,
    cfg, Data.stacks]
  funext k
  fin_cases k <;> rfl

theorem accept_cons (b : Bool) (xs : List Bool) (v : Control) (d : Data) :
    advance program (cfg (some (outer .accept)) v {d with original := b :: xs}) =
      cfg (some (outer .accept)) (setPop v (some b))
        {d with original := xs, output := b :: d.output} := by
  simp [advance, TM2.step, program, outerProgram, outer, TM2.stepAux,
    cfg, Data.stacks, popped, setPop, go]
  funext k
  fin_cases k <;> rfl

theorem accept_nil (v : Control) (d : Data) :
    advance program (cfg (some (outer .accept)) v {d with original := []}) =
      cfg none (setPop v none) {d with original := [], output := true :: d.output} := by
  simp [advance, TM2.step, program, outerProgram, outer, TM2.stepAux,
    cfg, Data.stacks, popped, setPop, go]
  funext k
  fin_cases k <;> rfl

theorem accept_run (xs : List Bool) (v : Control) (d : Data) :
    run (xs.length + 1) (cfg (some (outer .accept)) v {d with original := xs}) =
      cfg none (setPop v none)
        {d with original := [], output := true :: (xs.reverse ++ d.output)} := by
  induction xs generalizing v d with
  | nil => simpa using run_succ (accept_nil v d) 0
  | cons b xs ih =>
      rw [List.length_cons, run_succ (accept_cons b xs v d)]
      rw [ih (setPop v (some b)) {d with output := b :: d.output}]
      simp [List.reverse_cons, List.append_assoc, cfg, setPop]

abbrev HeaderConfig := TM2.Cfg (fun _ : Fin 3 => Bool)
  ProtocolBinaryHeader.Label ProtocolBinaryHeader.Control

def headerFrame (v : Control) (d : Data) (c : HeaderConfig) : Config :=
  renameCfg (finSumFinEquiv : (Fin 3 ⊕ Fin 12) ≃ Fin 15) (Equiv.refl _) (Equiv.refl _)
    (liftCfg (some (.inr OuterLabel.afterHeader)) v.2
      (fun j => d.stacks (finSumFinEquiv (.inr j))) c)

def headerData (d : Data) (c : HeaderConfig) : Data :=
  {d with input := c.stk 0, saved := c.stk 1, value := c.stk 2}

theorem headerFrame_initial (v : Control) (d : Data) :
    headerFrame v d (ProtocolBinaryHeader.cfg (some .scan) (none, none) d.input [] []) =
      cfg (some (.inl .scan)) ((none, none), v.2) {d with saved := [], value := []} := by
  unfold headerFrame renameCfg liftCfg cfg
  congr 1
  funext k
  fin_cases k <;> rfl

theorem headerFrame_halted (v : Control) (d : Data) (c : HeaderConfig)
    (hc : c.l = none) :
    headerFrame v d c = cfg (some (outer .afterHeader)) (c.var, v.2) (headerData d c) := by
  rcases c with ⟨l, u, S⟩
  change l = none at hc
  subst l
  unfold headerFrame renameCfg liftCfg cfg
  congr 1
  funext k
  fin_cases k <;> rfl

/-- The exact canonical reader runs inside the graph controller without
changing any of the twelve foreign stacks. -/
theorem header_run (v : Control) (d : Data) :
    ∃ t ≤ 2 * d.input.length + 2, ∃ c : HeaderConfig,
      run t (cfg (some (.inl .scan)) ((none, none), v.2) {d with saved := [], value := []}) =
        cfg (some (outer .afterHeader)) (c.var, v.2) (headerData d c) ∧
      ProtocolBinaryHeader.Post none d.input [] [] c := by
  obtain ⟨t, ht, hp⟩ := ProtocolBinaryHeader.scan_correct d.input none none [] []
  obtain ⟨n, hn, he⟩ := BitMachineSubroutineRenaming.lift_outputs_renamed
    (finSumFinEquiv : (Fin 3 ⊕ Fin 12) ≃ Fin 15) (Equiv.refl _) (Equiv.refl _)
    ProtocolBinaryHeader.program program (some (.inr OuterLabel.afterHeader))
    (fun _ => rfl) v.2 (fun j => d.stacks (finSumFinEquiv (.inr j)))
    (ProtocolBinaryHeader.cfg (some .scan) (none, none) d.input [] []) t hp.1
  change run n (headerFrame v d _) = headerFrame v d _ at he
  change run n (headerFrame v d _) = headerFrame v d (ProtocolBinaryHeader.run t _) at he
  rw [headerFrame_initial, headerFrame_halted v d _ hp.1] at he
  refine ⟨n, hn.trans (by simpa using ht), _, he, hp⟩

abbrev BoundConfig := TM2.Cfg (fun _ : Fin 4 => Bool)
  ProtocolBoundedUnary.Label ProtocolBoundedUnary.Control

def boundFrame (v : Control) (d : Data) (c : BoundConfig) : Config :=
  renameCfg boundStack boundLabel boundControl
    (liftCfg (some (.inr OuterLabel.afterBound)) (v.1, v.2.2)
      (fun j => d.stacks (boundStack (.inr j))) c)

def boundData (d : Data) (c : BoundConfig) : Data :=
  {d with value := c.stk 0, cap := c.stk 1, work := c.stk 2, unary := c.stk 3}

theorem boundFrame_initial (v : Control) (d : Data) :
    boundFrame v d (ProtocolBoundedUnary.cfg (some .zeroScan) (none, false)
      d.value d.cap [] []) =
      cfg (some (.inr (.inl .zeroScan))) (v.1, (none, false), v.2.2)
        {d with work := [], unary := []} := by
  unfold boundFrame renameCfg liftCfg cfg
  congr 1
  funext k
  fin_cases k <;> rfl

theorem boundFrame_halted (v : Control) (d : Data) (c : BoundConfig)
    (hc : c.l = none) :
    boundFrame v d c = cfg (some (outer .afterBound)) (v.1, c.var, v.2.2) (boundData d c) := by
  rcases c with ⟨l, u, S⟩
  change l = none at hc
  subst l
  unfold boundFrame renameCfg liftCfg cfg
  congr 1
  funext k
  fin_cases k <;> rfl

/-- Conversion is bounded by the already charged unary budget, including
oversized binary fields. The remaining scratch stacks have bounded length. -/
theorem bounded_run (v : Control) (d : Data) :
    ∃ t ≤ (d.cap.length + 1) * (4 * d.value.length + 5), ∃ c : BoundConfig,
      run t (cfg (some (.inr (.inl .zeroScan))) (v.1, (none, false), v.2.2)
        {d with work := [], unary := []}) =
        cfg (some (outer .afterBound)) (v.1, c.var, v.2.2) (boundData d c) ∧
      c.stk 3 = ProtocolBoundedUnary.result d.value d.cap [] ∧
      (c.stk 0).length = d.value.length ∧ c.stk 2 = [] ∧
      (c.stk 1).length ≤ d.cap.length := by
  obtain ⟨t, c, ht, he, hc, hout, hv, hw, hb⟩ :=
    ProtocolBoundedUnary.bounded_run_framed d.value d.cap []
  obtain ⟨n, hn, hrun⟩ := BitMachineSubroutineRenaming.lift_outputs_renamed
    boundStack boundLabel boundControl ProtocolBoundedUnary.program program
    (some (.inr OuterLabel.afterBound)) (fun _ => rfl) (v.1, v.2.2)
    (fun j => d.stacks (boundStack (.inr j)))
    (ProtocolBoundedUnary.cfg (some .zeroScan) (none, false) d.value d.cap [] []) t
    (by rw [← he] at hc; exact hc)
  change run n (boundFrame v d _) = boundFrame v d _ at hrun
  change run n (boundFrame v d _) = boundFrame v d (ProtocolBoundedUnary.run t _) at hrun
  rw [he, boundFrame_initial, boundFrame_halted v d c hc] at hrun
  exact ⟨n, hn.trans ht, c, hrun, hout, hv, hw, hb⟩

theorem clear_cons (source : Stack) (again next : OuterLabel)
    (hp : program (outer again) = clear source again next)
    (b : Bool) (xs : List Bool) (v : Control) (S : Stack → List Bool) :
    advance program ⟨some (outer again), v, Function.update S source (b :: xs)⟩ =
      ⟨some (outer again), setPop v (some b), Function.update S source xs⟩ := by
  simp [advance, TM2.step, hp, clear, TM2.stepAux, popped, setPop, go]

theorem clear_nil (source : Stack) (again next : OuterLabel)
    (hp : program (outer again) = clear source again next)
    (v : Control) (S : Stack → List Bool) :
    advance program ⟨some (outer again), v, Function.update S source []⟩ =
      ⟨some (outer next), setPop v none, Function.update S source []⟩ := by
  simp [advance, TM2.step, hp, clear, TM2.stepAux, popped, setPop, go]

theorem clear_run (source : Stack) (again next : OuterLabel)
    (hp : program (outer again) = clear source again next)
    (xs : List Bool) (v : Control) (S : Stack → List Bool) :
    run (xs.length + 1) ⟨some (outer again), v, Function.update S source xs⟩ =
      ⟨some (outer next), setPop v none, Function.update S source []⟩ := by
  induction xs generalizing v with
  | nil => simpa using run_succ (clear_nil source again next hp v S) 0
  | cons b xs ih =>
      rw [List.length_cons, run_succ (clear_cons source again next hp b xs v S), ih]
      rfl

/-- All three converter scratch banks are explicitly cleared before reuse. -/
theorem cleanup_run (v : Control) (d : Data) :
    run (d.value.length + d.cap.length + d.work.length + 3)
      (cfg (some (outer .clearValue)) v d) =
        cfg (some (outer .store)) (setPop v none)
          {d with value := [], cap := [], work := []} := by
  have h₁ : cfg (some (outer .clearValue)) v d =
      ⟨some (outer .clearValue), v, Function.update d.stacks 2 d.value⟩ := by
    unfold cfg
    congr 1
    exact (Function.update_eq_self_iff.mpr (show d.value = d.stacks 2 from rfl)).symm
  rw [h₁]
  have hv := clear_run 2 .clearValue .clearCap rfl d.value v d.stacks
  have hc := clear_run 3 .clearCap .clearWork rfl d.cap (setPop v none)
    (Function.update d.stacks 2 [])
  have hw := clear_run 4 .clearWork .store rfl d.work (setPop v none)
    (Function.update (Function.update d.stacks 2 []) 3 [])
  have hcv : Function.update (Function.update d.stacks 2 []) 3 d.cap =
      Function.update d.stacks 2 [] := by
    apply Function.update_eq_self_iff.mpr
    rfl
  have hwc : Function.update (Function.update (Function.update d.stacks 2 []) 3 []) 4 d.work =
      Function.update (Function.update d.stacks 2 []) 3 [] := by
    apply Function.update_eq_self_iff.mpr
    rfl
  rw [hcv] at hc
  rw [hwc] at hw
  have hvv : setPop (setPop v none) none = setPop v none := rfl
  rw [hvv] at hc hw
  rw [show d.value.length + d.cap.length + d.work.length + 3 =
    ((d.value.length + 1) + (d.cap.length + 1)) + (d.work.length + 1) by omega]
  rw [run_add ((run_add hv _).trans hc), hw]
  unfold cfg
  congr 1
  funext k
  fin_cases k <;> rfl

theorem result_of_decoded {input : List Bool} {g : EncodedCNF.Formula}
    (h : EncodedCNF.decode input = some g) : result input = true :: input := by
  simp [result, h]

theorem result_of_malformed {input : List Bool}
    (h : EncodedCNF.decode input = none) : result input = [false] := by
  simp [result, h]

end EthInapproximability.CurrentPaper.CNFValidator
