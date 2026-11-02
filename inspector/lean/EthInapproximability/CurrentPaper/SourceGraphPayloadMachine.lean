import EthInapproximability.CurrentPaper.SourceGraphVectorPayload
import EthInapproximability.CurrentPaper.SourceNormalizationMachineDecode
import EthInapproximability.CurrentPaper.MatrixTableWriter
import EthInapproximability.CurrentPaper.BitMachineSubroutineRenaming
import EthInapproximability.CurrentPaper.SamplerSeedEnumeration
import EthInapproximability.CurrentPaper.MatrixTableInterlaceRowReverse

/-!
# Physical graph-source payload production

Source: frozen v8 `03-exact-hardness.tex`, `lem:exact-source`, and
`B-effectivity-details.tex`, `thm:paper-materialization`.  The semantic
five-copy source is `SourceGraphVectorPayload.exactBits`.  This file starts
with a small, reusable physical endpoint query.  Its indices are unary
stacks, and the endpoint stream has one unary-delimited word per endpoint.
-/

namespace EthInapproximability.CurrentPaper.SourceGraphPayloadMachine

open Turing Turing.TM2.Stmt BitMachineEncoding

/-- The finite controller never stores an unbounded row, edge, or dimension. -/
inductive Phase where
  | beginEdge | first | second | restoreFirst | restoreSecond | copyRest | unwind
  deriving DecidableEq, Fintype

/-- Stream, reversed stream prefix, edge index, vertex index, a temporary
vertex prefix, and the answer stack. -/
abbrev Stack := Fin 6

structure Control where
  popped : Option Bool := none
  selected : Bool := false
  possible : Bool := true
  matched : Bool := false
  deriving DecidableEq, Fintype

abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Phase Control

def cfg (l : Option Phase) (v : Control) (stream saved edge vertex temp answer : List Bool) :
    Config := ⟨l, v, ![stream, saved, edge, vertex, temp, answer]⟩

def readField (next : Phase) : TM2.Stmt (fun _ : Stack => Bool) Phase Control :=
  pop 0 (fun v b => {v with popped := b})
    (branch (fun v => v.popped.isSome)
      (branch (fun v => v.popped.getD false)
        (push 1 (fun _ => true)
          (branch Control.selected
            (pop 3 (fun v b => {v with popped := b, possible := v.possible && b.isSome})
              (branch (fun v => v.popped.isSome)
                (push 4 (fun _ => true) (goto (fun _ => next)))
                (goto (fun _ => next))))
            (goto (fun _ => next))))
        (push 1 (fun _ => false)
          (branch Control.selected
            (peek 3 (fun v b => {v with matched := v.matched || (v.possible && !b.isSome)})
              (goto (fun _ => if next = .first then .restoreFirst else .restoreSecond)))
            (goto (fun _ => if next = .first then .restoreFirst else .restoreSecond)))))
      (goto (fun _ => .copyRest)))

def program : Phase → TM2.Stmt (fun _ : Stack => Bool) Phase Control
  | .beginEdge => pop 2 (fun v b =>
      {v with popped := b, selected := !b.isSome, possible := true})
      (goto (fun _ => .first))
  | .first => readField .first
  | .second => readField .second
  | .restoreFirst => pop 4 (fun v b => {v with popped := b})
      (branch (fun v => v.popped.isSome)
        (push 3 (fun _ => true) (goto (fun _ => .restoreFirst)))
        (load (fun v => {v with possible := true}) (goto (fun _ => .second))))
  | .restoreSecond => pop 4 (fun v b => {v with popped := b})
      (branch (fun v => v.popped.isSome)
        (push 3 (fun _ => true) (goto (fun _ => .restoreSecond)))
        (goto (fun v => if v.selected then .copyRest else .beginEdge)))
  | .copyRest => pop 0 (fun v b => {v with popped := b})
      (branch (fun v => v.popped.isSome)
        (push 1 (fun v => v.popped.getD false) (goto (fun _ => .copyRest)))
        (goto (fun _ => .unwind)))
  | .unwind => pop 1 (fun v b => {v with popped := b})
      (branch (fun v => v.popped.isSome)
        (push 0 (fun v => v.popped.getD false) (goto (fun _ => .unwind)))
        (push 5 Control.matched halt))

def run (t : ℕ) (c : Config) : Config := ((advance program)^[t]) c

/-- The Boolean specification of a single endpoint query; the physical
controller above has no access to this list or to the natural-number index. -/
def endpointHit (edges : List (ℕ × ℕ)) (k vertex : ℕ) : Bool :=
  match edges[k]? with
  | none => false
  | some p => decide (vertex = p.1 ∨ vertex = p.2)

def endpointStream (edges : List (ℕ × ℕ)) : List Bool :=
  edges.flatMap (fun p => EncodedGraph.unary p.1 ++ EncodedGraph.unary p.2)

theorem endpointStream_graph (g : EncodedGraph.Graph) :
    endpointStream g.edges = SourceNormalizationMachineDecode.endpointStream g := by
  change endpointStream g.edges =
    (g.edges.flatMap (fun p => [p.1, p.2])).flatMap EncodedGraph.unary
  induction g.edges with
  | nil => rfl
  | cons p ps ih =>
      simpa [endpointStream, List.flatMap_cons, List.flatMap_append, ih] using ih

theorem run_succ (t : ℕ) (c : Config) :
    run (t + 1) c = run t (advance program c) :=
  Function.iterate_succ_apply _ _ _

theorem run_add (t u : ℕ) (c : Config) :
    run (t + u) c = run u (run t c) := by
  simpa only [run, Nat.add_comm] using Function.iterate_add_apply (advance program) u t c

/-- Every traversal bit is explicitly moved into the saved stack. -/
theorem copyRest_cons (v : Control) (b : Bool)
    (stream saved edge vertex temp answer : List Bool) :
    advance program (cfg (some .copyRest) v (b :: stream) saved edge vertex temp answer) =
      cfg (some .copyRest) {v with popped := some b} stream (b :: saved)
        edge vertex temp answer := by
  simp [advance, TM2.step, TM2.stepAux, program, cfg]
  funext k
  fin_cases k <;> rfl

theorem copyRest_nil (v : Control) (saved edge vertex temp answer : List Bool) :
    advance program (cfg (some .copyRest) v [] saved edge vertex temp answer) =
      cfg (some .unwind) {v with popped := none} [] saved edge vertex temp answer := by
  simp [advance, TM2.step, TM2.stepAux, program, cfg]

theorem copyRest_run (v : Control) (stream saved edge vertex temp answer : List Bool) :
    run (stream.length + 1)
      (cfg (some .copyRest) v stream saved edge vertex temp answer) =
      cfg (some .unwind) {v with popped := none} []
        (stream.reverse ++ saved) edge vertex temp answer := by
  induction stream generalizing v saved with
  | nil => simpa [run_succ] using copyRest_nil v saved edge vertex temp answer
  | cons b stream ih =>
      rw [List.length_cons, run_succ, copyRest_cons]
      simpa [List.reverse_cons, List.append_assoc] using
        ih {v with popped := some b} (b :: saved)

theorem unwind_cons (v : Control) (b : Bool)
    (stream saved edge vertex temp answer : List Bool) :
    advance program (cfg (some .unwind) v stream (b :: saved) edge vertex temp answer) =
      cfg (some .unwind) {v with popped := some b} (b :: stream) saved
        edge vertex temp answer := by
  simp [advance, TM2.step, TM2.stepAux, program, cfg]
  funext k
  fin_cases k <;> rfl

theorem unwind_nil (v : Control)
    (stream edge vertex temp answer : List Bool) :
    advance program (cfg (some .unwind) v stream [] edge vertex temp answer) =
      cfg none {v with popped := none} stream [] edge vertex temp
        (v.matched :: answer) := by
  simp [advance, TM2.step, TM2.stepAux, program, cfg]
  funext k
  fin_cases k <;> rfl

theorem unwind_run (v : Control) (stream saved edge vertex temp answer : List Bool) :
    run (saved.length + 1)
      (cfg (some .unwind) v stream saved edge vertex temp answer) =
      cfg none {v with popped := none} (saved.reverse ++ stream) [] edge vertex temp
        (v.matched :: answer) := by
  induction saved generalizing v stream with
  | nil => simpa [run_succ] using unwind_nil v stream edge vertex temp answer
  | cons b saved ih =>
      rw [List.length_cons, run_succ, unwind_cons]
      simpa [List.reverse_cons, List.append_assoc] using
        ih {v with popped := some b} (b :: stream)

theorem beginEdge_cons (v : Control)
    (stream saved edge vertex temp answer : List Bool) :
    advance program (cfg (some .beginEdge) v stream saved (true :: edge) vertex temp answer) =
      cfg (some .first) {v with popped := some true, selected := false, possible := true}
        stream saved edge vertex temp answer := by
  simp [advance, TM2.step, TM2.stepAux, program, cfg]
  funext k
  fin_cases k <;> rfl

theorem beginEdge_nil (v : Control)
    (stream saved vertex temp answer : List Bool) :
    advance program (cfg (some .beginEdge) v stream saved [] vertex temp answer) =
      cfg (some .first) {v with popped := none, selected := true, possible := true}
        stream saved [] vertex temp answer := by
  simp [advance, TM2.step, TM2.stepAux, program, cfg]

def fieldPhase (second : Bool) : Phase := if second then .second else .first

def state (pop : Option Bool) (selected possible matched : Bool) : Control :=
  ⟨pop, selected, possible, matched⟩

theorem field_true_skip (second : Bool) (v : Control)
    (stream saved edge vertex temp answer : List Bool) :
    advance program (cfg (some (fieldPhase second)) {v with selected := false}
      (true :: stream) saved edge vertex temp answer) =
      cfg (some (fieldPhase second)) {v with selected := false, popped := some true}
        stream (true :: saved) edge vertex temp answer := by
  cases second <;> simp [fieldPhase, advance, TM2.step, TM2.stepAux, program,
    readField, cfg] <;> (funext k; fin_cases k <;> rfl)

theorem field_true_hit_cons (second : Bool) (p h : Bool) (pop : Option Bool)
    (stream saved edge vertex temp answer : List Bool) :
    advance program (cfg (some (fieldPhase second)) (state pop true p h)
      (true :: stream) saved edge (true :: vertex) temp answer) =
      cfg (some (fieldPhase second)) (state (some true) true p h)
        stream (true :: saved) edge vertex (true :: temp) answer := by
  cases second <;> simp [fieldPhase, advance, TM2.step, TM2.stepAux, program,
    readField, cfg, state] <;> (funext k; fin_cases k <;> rfl)

theorem field_true_hit_nil (second : Bool) (p h : Bool) (pop : Option Bool)
    (stream saved edge temp answer : List Bool) :
    advance program (cfg (some (fieldPhase second)) (state pop true p h)
      (true :: stream) saved edge [] temp answer) =
      cfg (some (fieldPhase second)) (state none true false h)
        stream (true :: saved) edge [] temp answer := by
  cases second <;> simp [fieldPhase, advance, TM2.step, TM2.stepAux, program,
    readField, cfg, state] <;> (funext k; fin_cases k <;> rfl)

theorem field_false_skip (second : Bool) (p h : Bool) (pop : Option Bool)
    (stream saved edge vertex temp answer : List Bool) :
    advance program (cfg (some (fieldPhase second)) (state pop false p h)
      (false :: stream) saved edge vertex temp answer) =
      cfg (some (if second then .restoreSecond else .restoreFirst))
        (state (some false) false p h)
        stream (false :: saved) edge vertex temp answer := by
  cases second <;> simp [fieldPhase, advance, TM2.step, TM2.stepAux, program,
    readField, cfg, state] <;> (funext k; fin_cases k <;> rfl)

theorem field_false_hit (second p h : Bool) (pop : Option Bool)
    (stream saved edge vertex temp answer : List Bool) :
    advance program (cfg (some (fieldPhase second)) (state pop true p h)
      (false :: stream) saved edge vertex temp answer) =
      cfg (some (if second then .restoreSecond else .restoreFirst))
        (state (some false) true p (h || (p && vertex.isEmpty)))
        stream (false :: saved) edge vertex temp answer := by
  cases second <;> cases vertex <;>
    simp [fieldPhase, advance, TM2.step, TM2.stepAux, program,
      readField, cfg, state] <;> (funext k; fin_cases k <;> rfl)

private theorem replicate_true_move (u : ℕ) (saved : List Bool) :
    List.replicate u true ++ true :: saved =
      true :: (List.replicate u true ++ saved) := by
  induction u with
  | zero => rfl
  | succ u ih => simp [List.replicate_succ, ih]

/-- A unary endpoint is compared by one physical pop per bit.  The
unconsumed vertex prefix and saved prefix are on actual stacks. -/
theorem field_true_run (second p h : Bool) (pop : Option Bool)
    (u r : ℕ) (rest saved edge temp answer : List Bool) :
    ∃ pop', run u (cfg (some (fieldPhase second)) (state pop true p h)
      (List.replicate u true ++ rest) saved edge (List.replicate r true) temp answer) =
      cfg (some (fieldPhase second)) (state pop' true (p && decide (u ≤ r)) h)
        rest (List.replicate u true ++ saved) edge
        (List.replicate (r-u) true) (List.replicate (min u r) true ++ temp) answer := by
  induction u generalizing r p pop saved temp with
  | zero =>
      refine ⟨pop, ?_⟩
      simp [run, state]
  | succ u ih =>
      cases r with
      | zero =>
          obtain ⟨pop', he⟩ := ih false none 0 (true :: saved) temp
          refine ⟨pop', ?_⟩
          simp only [List.replicate_zero] at he
          simp only [List.replicate_succ, List.cons_append, List.replicate_zero]
          rw [run_succ, field_true_hit_nil, he]
          simp [replicate_true_move]
      | succ r =>
          obtain ⟨pop', he⟩ := ih p (some true) r (true :: saved) (true :: temp)
          refine ⟨pop', ?_⟩
          simp only [List.replicate_succ, List.cons_append]
          rw [run_succ, field_true_hit_cons, he]
          simp [replicate_true_move, Nat.succ_sub_succ_eq_sub,
            List.replicate_succ]

theorem restoreFirst_cons (v : Control)
    (stream saved edge vertex temp answer : List Bool) :
    advance program (cfg (some .restoreFirst) v stream saved edge vertex
      (true :: temp) answer) =
      cfg (some .restoreFirst) {v with popped := some true} stream saved edge
        (true :: vertex) temp answer := by
  simp [advance, TM2.step, TM2.stepAux, program, cfg]
  funext k
  fin_cases k <;> rfl

theorem restoreFirst_nil (v : Control)
    (stream saved edge vertex answer : List Bool) :
    advance program (cfg (some .restoreFirst) v stream saved edge vertex [] answer) =
      cfg (some .second) {v with popped := none, possible := true}
        stream saved edge vertex [] answer := by
  simp [advance, TM2.step, TM2.stepAux, program, cfg]

theorem restoreFirst_run (v : Control) (q : ℕ)
    (stream saved edge vertex answer : List Bool) :
    run (q + 1) (cfg (some .restoreFirst) v stream saved edge vertex
      (List.replicate q true) answer) =
      cfg (some .second) {v with popped := none, possible := true}
        stream saved edge (List.replicate q true ++ vertex) [] answer := by
  induction q generalizing v vertex with
  | zero => simpa [run_succ] using restoreFirst_nil v stream saved edge vertex answer
  | succ q ih =>
      rw [List.replicate_succ, run_succ, restoreFirst_cons]
      simpa [List.replicate_succ, replicate_true_move] using
        ih {v with popped := some true} (true :: vertex)

theorem restoreSecond_cons (v : Control)
    (stream saved edge vertex temp answer : List Bool) :
    advance program (cfg (some .restoreSecond) v stream saved edge vertex
      (true :: temp) answer) =
      cfg (some .restoreSecond) {v with popped := some true} stream saved edge
        (true :: vertex) temp answer := by
  simp [advance, TM2.step, TM2.stepAux, program, cfg]
  funext k
  fin_cases k <;> rfl

theorem restoreSecond_nil (v : Control)
    (stream saved edge vertex answer : List Bool) :
    advance program (cfg (some .restoreSecond) v stream saved edge vertex [] answer) =
      cfg (some (if v.selected then .copyRest else .beginEdge))
        {v with popped := none} stream saved edge vertex [] answer := by
  simp [advance, TM2.step, TM2.stepAux, program, cfg]

theorem restoreSecond_run (v : Control) (q : ℕ)
    (stream saved edge vertex answer : List Bool) :
    run (q + 1) (cfg (some .restoreSecond) v stream saved edge vertex
      (List.replicate q true) answer) =
      cfg (some (if v.selected then .copyRest else .beginEdge))
        {v with popped := none} stream saved edge
        (List.replicate q true ++ vertex) [] answer := by
  induction q generalizing v vertex with
  | zero => simpa [run_succ] using restoreSecond_nil v stream saved edge vertex answer
  | succ q ih =>
      rw [List.replicate_succ, run_succ, restoreSecond_cons]
      simpa [List.replicate_succ, replicate_true_move] using
        ih {v with popped := some true} (true :: vertex)

private theorem unary_test (u r : ℕ) :
    (decide (u ≤ r) && (List.replicate (r-u) true).isEmpty) = decide (u = r) := by
  by_cases hle : u ≤ r
  · by_cases he : u = r
    · subst r; simp
    · have hs : r-u ≠ 0 := by omega
      simp [hle, he, hs]
  · have hne : u ≠ r := by omega
    have hdec₁ : decide (u ≤ r) = false := by simp [hle]
    have hdec₂ : decide (u = r) = false := by simp [hne]
    rw [hdec₁, hdec₂]
    rfl

private theorem unary_restore (u r : ℕ) :
    List.replicate (min u r) true ++ List.replicate (r-u) true =
      List.replicate r true := by
  rw [← List.replicate_add]
  simp
  congr 1
  omega

/-- A complete physical first-endpoint comparison, including restoration of
the vertex counter.  The answer is accumulated, rather than supplied. -/
theorem first_endpoint_run (u r : ℕ) (h : Bool) (pop : Option Bool)
    (rest saved edge answer : List Bool) :
    ∃ t ≤ 2*u+2,
      run t (cfg (some .first) (state pop true true h)
        (EncodedGraph.unary u ++ rest) saved edge (List.replicate r true) [] answer) =
      cfg (some .second) (state none true true (h || decide (u=r)))
        rest (false :: List.replicate u true ++ saved) edge
        (List.replicate r true) [] answer := by
  obtain ⟨last, hs⟩ := field_true_run false true h pop u r
    (false :: rest) saved edge [] answer
  have hd := field_false_hit false (decide (u ≤ r)) h last rest
    (List.replicate u true ++ saved) edge (List.replicate (r-u) true)
    (List.replicate (min u r) true) answer
  have hr := restoreFirst_run
    (state (some false) true (decide (u ≤ r))
      (h || (decide (u ≤ r) && (List.replicate (r-u) true).isEmpty)))
    (min u r) rest (false :: List.replicate u true ++ saved) edge
    (List.replicate (r-u) true) answer
  refine ⟨u + 1 + (min u r + 1), by omega, ?_⟩
  rw [show u + 1 + (min u r + 1) = u + (1 + (min u r + 1)) by omega,
    run_add, run_add]
  simp [fieldPhase] at hs hd
  simp only [EncodedGraph.unary, List.append_assoc, List.singleton_append] at hs ⊢
  rw [hs]
  simp only [show ∀ c : Config, run 1 c = advance program c from fun _ => rfl, hd]
  have htest : (decide (u ≤ r) && decide (r-u=0)) = decide (u=r) := by
    simpa only [List.isEmpty_replicate] using unary_test u r
  have hsum : min u r + (r-u) = r := by omega
  simp only [List.isEmpty_replicate, htest, ← List.replicate_add, hsum] at hr
  simp only [htest]
  simpa [state] using hr

theorem second_endpoint_run (u r : ℕ) (h : Bool) (pop : Option Bool)
    (rest saved edge answer : List Bool) :
    ∃ t ≤ 2*u+2,
      run t (cfg (some .second) (state pop true true h)
        (EncodedGraph.unary u ++ rest) saved edge (List.replicate r true) [] answer) =
      cfg (some .copyRest)
        (state none true (decide (u ≤ r)) (h || decide (u=r)))
        rest (false :: List.replicate u true ++ saved) edge
        (List.replicate r true) [] answer := by
  obtain ⟨last, hs⟩ := field_true_run true true h pop u r
    (false :: rest) saved edge [] answer
  have hd := field_false_hit true (decide (u ≤ r)) h last rest
    (List.replicate u true ++ saved) edge (List.replicate (r-u) true)
    (List.replicate (min u r) true) answer
  have hr := restoreSecond_run
    (state (some false) true (decide (u ≤ r))
      (h || (decide (u ≤ r) && (List.replicate (r-u) true).isEmpty)))
    (min u r) rest (false :: List.replicate u true ++ saved) edge
    (List.replicate (r-u) true) answer
  refine ⟨u + 1 + (min u r + 1), by omega, ?_⟩
  rw [show u + 1 + (min u r + 1) = u + (1 + (min u r + 1)) by omega,
    run_add, run_add]
  simp [fieldPhase] at hs hd
  simp only [EncodedGraph.unary, List.append_assoc, List.singleton_append] at hs ⊢
  rw [hs]
  simp only [show ∀ c : Config, run 1 c = advance program c from fun _ => rfl, hd]
  have htest : (decide (u ≤ r) && decide (r-u=0)) = decide (u=r) := by
    simpa only [List.isEmpty_replicate] using unary_test u r
  have hsum : min u r + (r-u) = r := by omega
  simp only [List.isEmpty_replicate, htest, ← List.replicate_add, hsum] at hr
  simp only [htest]
  simpa [state] using hr

theorem field_true_skip_run (second p h : Bool) (pop : Option Bool) (u : ℕ)
    (rest saved edge vertex answer : List Bool) :
    ∃ pop', run u (cfg (some (fieldPhase second)) (state pop false p h)
      (List.replicate u true ++ rest) saved edge vertex [] answer) =
      cfg (some (fieldPhase second)) (state pop' false p h)
        rest (List.replicate u true ++ saved) edge vertex [] answer := by
  induction u generalizing pop saved with
  | zero => exact ⟨pop, by simp [run]⟩
  | succ u ih =>
      obtain ⟨pop', he⟩ := ih (some true) (true :: saved)
      refine ⟨pop', ?_⟩
      simp only [List.replicate_succ, List.cons_append]
      rw [run_succ]
      have hs := field_true_skip second (state pop false p h)
        (List.replicate u true ++ rest) saved edge vertex [] answer
      have hs' : advance program
          (cfg (some (fieldPhase second)) (state pop false p h)
            (true :: (List.replicate u true ++ rest)) saved edge vertex [] answer) =
          cfg (some (fieldPhase second)) (state (some true) false p h)
            (List.replicate u true ++ rest) (true :: saved) edge vertex [] answer := by
        simpa [state] using hs
      rw [hs', he]
      simp [replicate_true_move]

theorem skip_first_endpoint_run (u : ℕ) (p h : Bool) (pop : Option Bool)
    (rest saved edge vertex answer : List Bool) :
    run (u+2) (cfg (some .first) (state pop false p h)
      (EncodedGraph.unary u ++ rest) saved edge vertex [] answer) =
      cfg (some .second) (state none false true h)
        rest (false :: List.replicate u true ++ saved) edge vertex [] answer := by
  obtain ⟨last, hs⟩ := field_true_skip_run false p h pop u
    (false :: rest) saved edge vertex answer
  have hd := field_false_skip false p h last rest
    (List.replicate u true ++ saved) edge vertex [] answer
  have hr := restoreFirst_nil (state (some false) false p h) rest
    (false :: List.replicate u true ++ saved) edge vertex answer
  rw [show u+2 = u+(1+1) by omega, run_add, run_add]
  simp [fieldPhase] at hs hd
  simp only [EncodedGraph.unary, List.append_assoc, List.singleton_append] at hs ⊢
  rw [hs]
  simp only [show ∀ c : Config, run 1 c = advance program c from fun _ => rfl, hd]
  simpa [state] using hr

theorem skip_second_endpoint_run (u : ℕ) (p h : Bool) (pop : Option Bool)
    (rest saved edge vertex answer : List Bool) :
    run (u+2) (cfg (some .second) (state pop false p h)
      (EncodedGraph.unary u ++ rest) saved edge vertex [] answer) =
      cfg (some .beginEdge) (state none false p h)
        rest (false :: List.replicate u true ++ saved) edge vertex [] answer := by
  obtain ⟨last, hs⟩ := field_true_skip_run true p h pop u
    (false :: rest) saved edge vertex answer
  have hd := field_false_skip true p h last rest
    (List.replicate u true ++ saved) edge vertex [] answer
  have hr := restoreSecond_nil (state (some false) false p h) rest
    (false :: List.replicate u true ++ saved) edge vertex answer
  rw [show u+2 = u+(1+1) by omega, run_add, run_add]
  simp [fieldPhase] at hs hd
  simp only [EncodedGraph.unary, List.append_assoc, List.singleton_append] at hs ⊢
  rw [hs]
  simp only [show ∀ c : Config, run 1 c = advance program c from fun _ => rfl, hd]
  simpa [state] using hr

private theorem unary_reverse (u : ℕ) :
    (EncodedGraph.unary u).reverse = false :: List.replicate u true := by
  simp [EncodedGraph.unary]

private theorem endpointStream_cons (p : ℕ × ℕ) (ps : List (ℕ × ℕ)) :
    endpointStream (p :: ps) =
      EncodedGraph.unary p.1 ++ EncodedGraph.unary p.2 ++ endpointStream ps := rfl

theorem first_nil (v : Control) (saved edge vertex answer : List Bool) :
    advance program (cfg (some .first) v [] saved edge vertex [] answer) =
      cfg (some .copyRest) {v with popped := none} [] saved edge vertex [] answer := by
  simp [advance, TM2.step, TM2.stepAux, program, readField, cfg]

theorem selected_edge_run (u w r : ℕ) (ps : List (ℕ × ℕ))
    (pop : Option Bool) (saved answer : List Bool) :
    ∃ t ≤ 10 * ((endpointStream ((u,w)::ps)).length + saved.length + 1), ∃ c,
      run t (cfg (some .beginEdge) (state pop false true false)
        (endpointStream ((u,w)::ps)) saved [] (List.replicate r true) [] answer) =
      cfg none c (saved.reverse ++ endpointStream ((u,w)::ps)) [] []
        (List.replicate r true) []
        (decide (r=u ∨ r=w) :: answer) := by
  obtain ⟨t₁, ht₁, h₁⟩ := first_endpoint_run u r false none
    (EncodedGraph.unary w ++ endpointStream ps) saved [] answer
  obtain ⟨t₂, ht₂, h₂⟩ := second_endpoint_run w r (decide (u=r)) none
    (endpointStream ps) (false :: List.replicate u true ++ saved) [] answer
  let pre := false :: List.replicate w true ++
    false :: List.replicate u true ++ saved
  let tail := endpointStream ps
  let v : Control := state none true (decide (w ≤ r))
    (decide (u=r) || decide (w=r))
  have hc := copyRest_run v tail pre [] (List.replicate r true) [] answer
  have hu := unwind_run {v with popped := none} []
    (tail.reverse ++ pre) [] (List.replicate r true) [] answer
  let c₀ := cfg (some .beginEdge) (state pop false true false)
    (endpointStream ((u,w)::ps)) saved [] (List.replicate r true) [] answer
  let c₁ := cfg (some .first) (state none true true false)
    (EncodedGraph.unary u ++ EncodedGraph.unary w ++ tail)
    saved [] (List.replicate r true) [] answer
  let c₂ := cfg (some .second) (state none true true (decide (u=r)))
    (EncodedGraph.unary w ++ tail) (false :: List.replicate u true ++ saved)
    [] (List.replicate r true) [] answer
  let c₃ := cfg (some .copyRest) v tail pre [] (List.replicate r true) [] answer
  let c₄ := cfg (some .unwind) {v with popped := none} []
    (tail.reverse ++ pre) [] (List.replicate r true) [] answer
  have h₀ : run 1 c₀ = c₁ := by
    simp [c₀, c₁, tail, endpointStream_cons, List.append_assoc, run,
      advance, TM2.step, TM2.stepAux, program, cfg, state]
  have h₁' : run t₁ c₁ = c₂ := by
    simpa [c₁, c₂, tail] using h₁
  have h₂' : run t₂ c₂ = c₃ := by
    simpa [c₂, c₃, pre, tail, v] using h₂
  have h₃' : run (tail.length+1) c₃ = c₄ := by
    simpa [c₃, c₄] using hc
  have h₄' : run ((tail.reverse ++ pre).length+1) c₄ =
      cfg none v ((tail.reverse ++ pre).reverse) [] []
        (List.replicate r true) [] (v.matched :: answer) := by
    simpa [c₄, v, state] using hu
  have hall : run (1+t₁+t₂+(tail.length+1)+((tail.reverse ++ pre).length+1)) c₀ =
      cfg none v ((tail.reverse ++ pre).reverse) [] []
        (List.replicate r true) [] (v.matched :: answer) := by
    rw [run_add (1+t₁+t₂+(tail.length+1)) ((tail.reverse ++ pre).length+1),
      run_add (1+t₁+t₂) (tail.length+1), run_add (1+t₁) t₂,
      run_add 1 t₁, h₀, h₁', h₂', h₃', h₄']
  refine ⟨1+t₁+t₂+(tail.length+1)+((tail.reverse ++ pre).length+1), ?_, v, ?_⟩
  · have hlen : (endpointStream ((u,w)::ps)).length = u+w+2+tail.length := by
      simp [endpointStream_cons, EncodedGraph.unary, tail]
      omega
    have hpre : pre.length = u+w+2+saved.length := by
      simp [pre]
      omega
    simp only [List.length_append, List.length_reverse]
    omega
  have hhit : decide (r=u ∨ r=w) = (decide (u=r) || decide (w=r)) := by
    by_cases hu : r=u
    · subst u
      simp
    · by_cases hw : r=w
      · subst w
        simp
      · have hno : ¬(r=u ∨ r=w) := by
          intro h
          exact h.elim hu hw
        have hun : u≠r := Ne.symm hu
        have hwn : w≠r := Ne.symm hw
        simp [hno, hun, hwn]
  simpa [c₀, pre, tail, v, endpointStream_cons, EncodedGraph.unary,
    List.reverse_append, List.append_assoc, hhit] using hall

theorem skipped_edge_run (u w r k : ℕ) (ps : List (ℕ × ℕ))
    (pop : Option Bool) (saved answer : List Bool) :
    run (1+(u+2)+(w+2))
      (cfg (some .beginEdge) (state pop false true false)
        (endpointStream ((u,w)::ps)) saved (true :: List.replicate k true)
        (List.replicate r true) [] answer) =
      cfg (some .beginEdge) (state none false true false)
        (endpointStream ps)
        (false :: List.replicate w true ++ false :: List.replicate u true ++ saved)
        (List.replicate k true) (List.replicate r true) [] answer := by
  let c₀ := cfg (some .beginEdge) (state pop false true false)
    (endpointStream ((u,w)::ps)) saved (true :: List.replicate k true)
    (List.replicate r true) [] answer
  let c₁ := cfg (some .first) (state (some true) false true false)
    (EncodedGraph.unary u ++ EncodedGraph.unary w ++ endpointStream ps)
    saved (List.replicate k true) (List.replicate r true) [] answer
  let c₂ := cfg (some .second) (state none false true false)
    (EncodedGraph.unary w ++ endpointStream ps)
    (false :: List.replicate u true ++ saved)
    (List.replicate k true) (List.replicate r true) [] answer
  let c₃ := cfg (some .beginEdge) (state none false true false)
    (endpointStream ps)
    (false :: List.replicate w true ++ false :: List.replicate u true ++ saved)
    (List.replicate k true) (List.replicate r true) [] answer
  have h₀ : run 1 c₀ = c₁ := by
    simpa [c₀, c₁, endpointStream_cons, List.append_assoc, run, state] using
      beginEdge_cons (state pop false true false)
        (endpointStream ((u,w)::ps)) saved (List.replicate k true)
        (List.replicate r true) [] answer
  have h₁ : run (u+2) c₁ = c₂ := by
    simpa [c₁, c₂, List.append_assoc] using
      skip_first_endpoint_run u true false (some true)
        (EncodedGraph.unary w ++ endpointStream ps) saved
        (List.replicate k true) (List.replicate r true) answer
  have h₂ : run (w+2) c₂ = c₃ := by
    simpa [c₂, c₃] using
      skip_second_endpoint_run w true false none
        (endpointStream ps) (false :: List.replicate u true ++ saved)
        (List.replicate k true) (List.replicate r true) answer
  change run (1+(u+2)+(w+2)) c₀ = c₃
  rw [run_add (1+(u+2)) (w+2), run_add 1 (u+2), h₀, h₁, h₂]

theorem empty_query_run (k r : ℕ) (pop : Option Bool)
    (saved answer : List Bool) :
    ∃ t ≤ saved.length+4, ∃ c,
      run t (cfg (some .beginEdge) (state pop false true false)
        [] saved (List.replicate k true) (List.replicate r true) [] answer) =
      cfg none c saved.reverse [] (List.replicate (k-1) true)
        (List.replicate r true) [] (false :: answer) := by
  let edge := List.replicate (k-1) true
  let firstControl : Control :=
    if k=0 then state none true true false else state (some true) false true false
  have h₀ : run 1 (cfg (some .beginEdge) (state pop false true false)
      [] saved (List.replicate k true) (List.replicate r true) [] answer) =
      cfg (some .first) firstControl [] saved edge (List.replicate r true) [] answer := by
    cases k with
    | zero =>
        simpa [edge, firstControl, run, state] using
          beginEdge_nil (state pop false true false) [] saved
            (List.replicate r true) [] answer
    | succ k =>
        simpa [edge, firstControl, run, state, List.replicate_succ] using
          beginEdge_cons (state pop false true false) [] saved
            (List.replicate k true) (List.replicate r true) [] answer
  have h₁ : run 1 (cfg (some .first) firstControl [] saved edge
      (List.replicate r true) [] answer) =
      cfg (some .copyRest) {firstControl with popped := none}
        [] saved edge (List.replicate r true) [] answer := by
    simpa [run] using first_nil firstControl saved edge
      (List.replicate r true) answer
  have h₂ : run 1 (cfg (some .copyRest) {firstControl with popped := none}
      [] saved edge (List.replicate r true) [] answer) =
      cfg (some .unwind) {firstControl with popped := none}
        [] saved edge (List.replicate r true) [] answer := by
    simpa [run] using copyRest_nil {firstControl with popped := none}
      saved edge (List.replicate r true) [] answer
  have h₃ := unwind_run {firstControl with popped := none}
    [] saved edge (List.replicate r true) [] answer
  refine ⟨3+(saved.length+1), by omega,
    {{firstControl with popped := none} with popped := none}, ?_⟩
  rw [run_add 3 (saved.length+1)]
  have hfirst : run 3 (cfg (some .beginEdge) (state pop false true false)
      [] saved (List.replicate k true) (List.replicate r true) [] answer) =
      cfg (some .unwind) {firstControl with popped := none}
        [] saved edge (List.replicate r true) [] answer := by
    rw [show 3 = 1+(1+1) by omega, run_add, h₀,
      run_add, h₁, h₂]
  rw [hfirst, h₃]
  cases k <;> simp [firstControl, state, edge]

/-- Whole-edge physical query.  The stream and vertex counter are restored;
the unary edge counter is intentionally consumed, so callers copy it when
they need to retain that input.  Every result bit is generated by the fixed
finite controller above, not looked up in an input Boolean array. -/
theorem endpoint_query_run (edges : List (ℕ × ℕ)) (k r : ℕ)
    (pop : Option Bool) (saved answer : List Bool) :
    ∃ t ≤ 16 * ((endpointStream edges).length + saved.length + 1) *
        (edges.length + 1), ∃ c edge,
      run t (cfg (some .beginEdge) (state pop false true false)
        (endpointStream edges) saved (List.replicate k true)
        (List.replicate r true) [] answer) =
      cfg none c (saved.reverse ++ endpointStream edges) [] edge
        (List.replicate r true) [] (endpointHit edges k r :: answer) ∧
      edge.length ≤ k := by
  induction edges generalizing k pop saved with
  | nil =>
      obtain ⟨t,ht,c,he⟩ := empty_query_run k r pop saved answer
      refine ⟨t, ?_, c, List.replicate (k-1) true, ?_, ?_⟩
      · simp [endpointStream] at ht ⊢
        omega
      · simpa [endpointStream, endpointHit] using he
      · simp
  | cons p ps ih =>
      cases k with
      | zero =>
          obtain ⟨t,ht,c,he⟩ := selected_edge_run p.1 p.2 r ps pop saved answer
          refine ⟨t, ?_, c, [], ?_, by simp⟩
          · have hlen : 0 < (p::ps).length+1 := by simp
            nlinarith
          simpa [endpointHit] using he
      | succ k =>
          let pre := false :: List.replicate p.2 true ++
            false :: List.replicate p.1 true ++ saved
          obtain ⟨t,ht,c,edge,he,hlen⟩ := ih k none pre
          have hs := skipped_edge_run p.1 p.2 r k ps pop saved answer
          refine ⟨1+(p.1+2)+(p.2+2)+t, ?_, c, edge, ?_, by omega⟩
          · have hlen : (endpointStream (p::ps)).length =
                p.1+p.2+2+(endpointStream ps).length := by
              simp [endpointStream_cons, EncodedGraph.unary]
              omega
            have hpre : pre.length = p.1+p.2+2+saved.length := by
              simp [pre]
              omega
            have htotal : (endpointStream ps).length + pre.length + 1 =
                (endpointStream (p::ps)).length + saved.length + 1 := by omega
            rw [htotal] at ht
            simp only [List.length_cons]
            nlinarith
          have hs' : run (1+(p.1+2)+(p.2+2))
              (cfg (some .beginEdge) (state pop false true false)
                (endpointStream (p::ps)) saved (List.replicate (k+1) true)
                (List.replicate r true) [] answer) =
              cfg (some .beginEdge) (state none false true false)
                (endpointStream ps) pre (List.replicate k true)
                (List.replicate r true) [] answer := by
            simpa [List.replicate_succ, pre] using hs
          rw [run_add, hs', he]
          simp [pre, endpointStream_cons, endpointHit, EncodedGraph.unary,
            List.reverse_append, List.append_assoc]

/-- The physical query's Boolean target is exactly the endpoint predicate
used by the frozen five-copy vector source. -/
theorem endpointHit_graph (g : EncodedGraph.Graph) (hg : g.Valid)
    (k : Fin g.edges.length) (r : Fin g.vertices) :
    endpointHit g.edges k.val r.val =
      decide (∃ j : Fin 2, r = EncodedGraph.endpoints g hg k j) := by
  classical
  have h₀ : r = EncodedGraph.endpoints g hg k 0 ↔
      r.val = (g.edges.get k).1 := by
    constructor
    · intro h
      simpa only [EncodedGraph.endpoints_zero] using congrArg Fin.val h
    · intro h
      apply Fin.ext
      simpa only [EncodedGraph.endpoints_zero] using h
  have h₁ : r = EncodedGraph.endpoints g hg k 1 ↔
      r.val = (g.edges.get k).2 := by
    constructor
    · intro h
      simpa only [EncodedGraph.endpoints_one] using congrArg Fin.val h
    · intro h
      apply Fin.ext
      simpa only [EncodedGraph.endpoints_one] using h
  have htarget : (∃ j : Fin 2, r = EncodedGraph.endpoints g hg k j) ↔
      (r.val = (g.edges.get k).1 ∨ r.val = (g.edges.get k).2) := by
    simpa only [Fin.exists_fin_two] using or_congr h₀ h₁
  have hp : g.edges[k.val]? = some (g.edges.get k) := by simp
  simp only [endpointHit, hp]
  have hget : g.edges.get k = g.edges[k.val] := rfl
  rw [hget] at htarget
  clear h₀ h₁
  by_cases h : r.val = g.edges[k.val].1 ∨ r.val = g.edges[k.val].2
  · have h' := htarget.mpr h
    simp [h, h']
  · have h' : ¬(∃ j : Fin 2, r = EncodedGraph.endpoints g hg k j) :=
      fun hp => h (htarget.mp hp)
    simp [h, h']

theorem endpointStream_length_le (edges : List (ℕ × ℕ)) (n : ℕ)
    (h : ∀ p ∈ edges, p.1 < n ∧ p.2 < n) :
    (endpointStream edges).length ≤ 2 * edges.length * (n+1) := by
  induction edges with
  | nil => simp [endpointStream]
  | cons p ps ih =>
      have hp := h p (by simp)
      have hps : ∀ q ∈ ps, q.1 < n ∧ q.2 < n := by
        intro q hq
        exact h q (by simp [hq])
      have hi := ih hps
      simp only [endpointStream_cons, List.length_append, List.length_cons,
        EncodedGraph.unary, List.length_replicate] at hi ⊢
      have hfactor : 2 * (ps.length + 1) * (n+1) =
          2 * ps.length * (n+1) + 2*(n+1) := by ring
      rw [hfactor]
      simp only [List.length_nil, Nat.zero_add] at *
      nlinarith

/-- The unary-endpoint query itself has a cubic bit-transition bound in the
canonical encoded graph length.  This does not yet include row/column
enumeration or production of the complete source array. -/
theorem encoded_query_run (g : EncodedGraph.Graph) (hg : g.Valid)
    (k r : ℕ) (answer : List Bool) :
    let N := (EncodedGraph.encode g).length
    ∃ t ≤ 48 * (N+1)^3, ∃ c edge,
      run t (cfg (some .beginEdge) (state none false true false)
        (SourceNormalizationMachineDecode.endpointStream g) []
        (List.replicate k true) (List.replicate r true) [] answer) =
      cfg none c (SourceNormalizationMachineDecode.endpointStream g) [] edge
        (List.replicate r true) [] (endpointHit g.edges k r :: answer) := by
  let N := (EncodedGraph.encode g).length
  obtain ⟨t,ht,c,edge,he,_⟩ := endpoint_query_run g.edges k r none [] answer
  have hs : (endpointStream g.edges).length ≤ 2*g.edges.length*(g.vertices+1) :=
    endpointStream_length_le g.edges g.vertices
      (fun p hp => ⟨(hg p hp).1, (hg p hp).2.1⟩)
  have hn := EncodedGraph.encode_length_lower g
  have hv : g.vertices ≤ N := by dsimp [N]; omega
  have hm : g.edges.length ≤ N := by dsimp [N]; omega
  have hp : (endpointStream g.edges).length + 1 ≤ 3*(N+1)^2 := by
    have hmul := Nat.mul_le_mul hm (Nat.add_le_add_right hv 1)
    nlinarith
  have hproduct := Nat.mul_le_mul hp (Nat.add_le_add_right hm 1)
  have ht' : t ≤ 48*(N+1)^3 := by
    have hx : (3*(N+1)^2)*(N+1) = 3*(N+1)^3 := by ring
    calc
      t ≤ 16 * (((endpointStream g.edges).length+1) * (g.edges.length+1)) := by
        simpa [Nat.mul_assoc] using ht
      _ ≤ 16 * (3*(N+1)^3) :=
        Nat.mul_le_mul_left 16 (by simpa only [hx] using hproduct)
      _ = 48*(N+1)^3 := by ring
  refine ⟨t, ht', c, edge, ?_⟩
  simpa [endpointStream_graph] using he

end EthInapproximability.CurrentPaper.SourceGraphPayloadMachine


namespace EthInapproximability.CurrentPaper.SourceGraphPayloadMachine.BaseCell

open Turing Turing.TM2.Stmt BitMachineEncoding BitMachineComposition
open EthInapproximability.CurrentPaper.SourceGraphPayloadMachine

set_option maxRecDepth 1000

/- The writer's first seven persistent cells are respectively the endpoint
stream, saved stream prefix, edge-index copy, vertex-index copy, query
scratch, copy scratch, and a spare cell.  The writer itself supplies the
original row and column indices and receives the answer in its third local
cell.  No incidence table is present in the input bank. -/
abbrev Stack := MatrixTableWriter.CellStack 7

inductive Admin where
  | copyRowScan | copyRowRestore | copyColScan | copyColRestore
  | clearVertex | clearEdge
  deriving DecidableEq, Fintype

abbrev Label := Phase ⊕ Admin
abbrev Control := SourceGraphPayloadMachine.Control
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

def initial : Control := ⟨none, false, true, false⟩
def start : Label := .inr .copyRowScan

def scannerSlots : Fin 6 ⊕ Fin 4 ≃ Stack where
  toFun
    | .inl 0 => .inl 0
    | .inl 1 => .inl 1
    | .inl 2 => .inl 2
    | .inl 3 => .inl 3
    | .inl 4 => .inl 4
    | .inl 5 => .inr 2
    | .inr 0 => .inl 5
    | .inr 1 => .inl 6
    | .inr 2 => .inr 0
    | .inr 3 => .inr 1
  invFun
    | .inl 0 => .inl 0
    | .inl 1 => .inl 1
    | .inl 2 => .inl 2
    | .inl 3 => .inl 3
    | .inl 4 => .inl 4
    | .inl 5 => .inr 0
    | .inl 6 => .inr 1
    | .inr 0 => .inr 2
    | .inr 1 => .inr 3
    | .inr 2 => .inl 5
  left_inv k := by rcases k with k | k <;> fin_cases k <;> rfl
  right_inv k := by rcases k with k | k <;> fin_cases k <;> rfl

def controlSlots : Control × Unit ≃ Control where
  toFun := Prod.fst
  invFun v := (v, ())
  left_inv x := by rcases x with ⟨x, ⟨⟩⟩; rfl
  right_inv _ := rfl

def adminProgram : Admin → TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .copyRowScan => pop (.inr 0) (fun v b => {v with popped := b})
      (branch (fun v => v.popped.isSome)
        (push (.inl 5) (fun v => v.popped.getD false)
          (goto (fun _ => .inr .copyRowScan)))
        (goto (fun _ => .inr .copyRowRestore)))
  | .copyRowRestore => pop (.inl 5) (fun v b => {v with popped := b})
      (branch (fun v => v.popped.isSome)
        (push (.inr 0) (fun v => v.popped.getD false)
          (push (.inl 3) (fun v => v.popped.getD false)
            (goto (fun _ => .inr .copyRowRestore))))
        (goto (fun _ => .inr .copyColScan)))
  | .copyColScan => pop (.inr 1) (fun v b => {v with popped := b})
      (branch (fun v => v.popped.isSome)
        (push (.inl 5) (fun v => v.popped.getD false)
          (goto (fun _ => .inr .copyColScan)))
        (goto (fun _ => .inr .copyColRestore)))
  | .copyColRestore => pop (.inl 5) (fun v b => {v with popped := b})
      (branch (fun v => v.popped.isSome)
        (push (.inr 1) (fun v => v.popped.getD false)
          (push (.inl 2) (fun v => v.popped.getD false)
            (goto (fun _ => .inr .copyColRestore))))
        (load (fun _ => initial) (goto (fun _ => .inl .beginEdge))))
  | .clearVertex => pop (.inl 3) (fun v b => {v with popped := b})
      (branch (fun v => v.popped.isSome)
        (goto (fun _ => .inr .clearVertex))
        (goto (fun _ => .inr .clearEdge)))
  | .clearEdge => pop (.inl 2) (fun v b => {v with popped := b})
      (branch (fun v => v.popped.isSome)
        (goto (fun _ => .inr .clearEdge)) halt)

def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .inl l => renameStmt scannerSlots (Equiv.refl _) controlSlots
      (liftStmt (some .clearVertex) (SourceGraphPayloadMachine.program l))
  | .inr l => adminProgram l

def bank (stream : List Bool) : Fin 7 → List Bool :=
  ![stream, [], [], [], [], [], []]

def cell (l : Option Label) (v : Control) (stream saved edge vertex temp scratch spare
    row col answer : List Bool) : Config :=
  ⟨l, v, Sum.elim (![stream, saved, edge, vertex, temp, scratch, spare] : Fin 7 → List Bool)
    (![row, col, answer] : Fin 3 → List Bool)⟩

def run (t : ℕ) (c : Config) : Config := ((advance program)^[t]) c

theorem run_succ (t : ℕ) (c : Config) :
    run (t+1) c = run t (advance program c) :=
  Function.iterate_succ_apply _ _ _

theorem run_add {c d : Config} {t : ℕ} (h : run t c = d) (u : ℕ) :
    run (t+u) c = run u d := by
  rw [Nat.add_comm t u]
  simp only [run, Function.iterate_add_apply] at h ⊢
  rw [h]

theorem copyRowScan_cons (v : Control) (b : Bool)
    (stream saved edge vertex temp scratch spare row col answer : List Bool) :
    advance program (cell (some (.inr .copyRowScan)) v stream saved edge vertex
      temp scratch spare (b::row) col answer) =
    cell (some (.inr .copyRowScan)) {v with popped := some b} stream saved edge vertex
      temp (b::scratch) spare row col answer := by
  simp only [advance, TM2.step, TM2.stepAux, program, adminProgram, cell,
    Sum.elim_inr, Matrix.cons_val_zero, List.head?_cons, List.tail_cons,
    Option.isSome_some, cond_true, Option.getD_some]
  congr 1
  funext k
  cases k with
  | inl k => fin_cases k <;> simp [Function.update]
  | inr k => fin_cases k <;> simp [Function.update]

theorem copyRowScan_nil (v : Control)
    (stream saved edge vertex temp scratch spare col answer : List Bool) :
    advance program (cell (some (.inr .copyRowScan)) v stream saved edge vertex
      temp scratch spare [] col answer) =
    cell (some (.inr .copyRowRestore)) {v with popped := none} stream saved edge vertex
      temp scratch spare [] col answer := by
  simp only [advance, TM2.step, TM2.stepAux, program, adminProgram, cell,
    Sum.elim_inr, Matrix.cons_val_zero, List.head?_nil, List.tail_nil,
    Option.isSome_none, cond_false, Option.getD_some]
  congr 1
  funext k
  cases k with
  | inl k => fin_cases k <;> simp [Function.update]
  | inr k => fin_cases k <;> simp [Function.update]

theorem copyRowRestore_cons (v : Control) (b : Bool)
    (stream saved edge vertex temp scratch spare row col answer : List Bool) :
    advance program (cell (some (.inr .copyRowRestore)) v stream saved edge vertex
      temp (b::scratch) spare row col answer) =
    cell (some (.inr .copyRowRestore)) {v with popped := some b} stream saved edge
      (b::vertex) temp scratch spare (b::row) col answer := by
  simp only [advance, TM2.step, TM2.stepAux, program, adminProgram, cell,
    Sum.elim_inl]
  have hscratch :
      (![stream, saved, edge, vertex, temp, b::scratch, spare] : Fin 7 → List Bool) 5 =
        b::scratch := rfl
  simp only [hscratch,
    List.head?_cons, List.tail_cons, Option.isSome_some, cond_true, Option.getD_some]
  congr 1
  funext k
  cases k with
  | inl k => fin_cases k <;> simp [Function.update]
  | inr k => fin_cases k <;> simp [Function.update]

theorem copyRowRestore_nil (v : Control)
    (stream saved edge vertex temp spare row col answer : List Bool) :
    advance program (cell (some (.inr .copyRowRestore)) v stream saved edge vertex
      temp [] spare row col answer) =
    cell (some (.inr .copyColScan)) {v with popped := none} stream saved edge vertex
      temp [] spare row col answer := by
  simp only [advance, TM2.step, TM2.stepAux, program, adminProgram, cell,
    Sum.elim_inl]
  have hscratch :
      (![stream, saved, edge, vertex, temp, ([] : List Bool), spare] : Fin 7 → List Bool) 5 =
        [] := rfl
  simp only [hscratch,
    List.head?_nil, List.tail_nil, Option.isSome_none, cond_false, Option.getD_some]
  congr 1
  funext k
  cases k with
  | inl k => fin_cases k <;> simp [Function.update]
  | inr k => fin_cases k <;> simp [Function.update]

theorem row_scan (v : Control) (stream saved edge vertex temp scratch spare
    row col answer : List Bool) :
    run (row.length+1) (cell (some (.inr .copyRowScan)) v stream saved edge vertex
      temp scratch spare row col answer) =
    cell (some (.inr .copyRowRestore)) {v with popped := none} stream saved edge vertex
      temp (row.reverse ++ scratch) spare [] col answer := by
  induction row generalizing v scratch with
  | nil => simpa using run_succ 0 _ ▸ copyRowScan_nil v stream saved edge vertex temp scratch spare col answer
  | cons b row ih =>
      rw [List.length_cons, run_succ, copyRowScan_cons]
      simpa [List.reverse_cons, List.append_assoc] using
        ih {v with popped := some b} (b::scratch)

theorem row_restore (v : Control) (stream saved edge vertex temp scratch spare
    row col answer : List Bool) :
    run (scratch.length+1) (cell (some (.inr .copyRowRestore)) v stream saved edge vertex
      temp scratch spare row col answer) =
    cell (some (.inr .copyColScan)) {v with popped := none} stream saved edge
      (scratch.reverse ++ vertex) temp [] spare (scratch.reverse ++ row) col answer := by
  induction scratch generalizing v vertex row with
  | nil => simpa using run_succ 0 _ ▸ copyRowRestore_nil v stream saved edge vertex temp spare row col answer
  | cons b scratch ih =>
      rw [List.length_cons, run_succ, copyRowRestore_cons]
      simpa [List.reverse_cons, List.append_assoc] using
        ih {v with popped := some b} (b::vertex) (b::row)

theorem copy_row (v : Control) (stream saved edge vertex temp spare
    row col answer : List Bool) :
    run (2*row.length+2) (cell (some (.inr .copyRowScan)) v stream saved edge vertex
      temp [] spare row col answer) =
    cell (some (.inr .copyColScan)) {v with popped := none} stream saved edge
      (row ++ vertex) temp [] spare row col answer := by
  have hs := row_scan v stream saved edge vertex temp [] spare row col answer
  have hr := row_restore {v with popped := none} stream saved edge vertex temp
    row.reverse spare [] col answer
  simp only [List.append_nil, List.length_reverse, List.reverse_reverse] at hs hr
  have h := run_add hs (row.length+1) |>.trans hr
  simpa only [Nat.two_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

theorem copyColScan_cons (v : Control) (b : Bool)
    (stream saved edge vertex temp scratch spare row col answer : List Bool) :
    advance program (cell (some (.inr .copyColScan)) v stream saved edge vertex
      temp scratch spare row (b::col) answer) =
    cell (some (.inr .copyColScan)) {v with popped := some b} stream saved edge vertex
      temp (b::scratch) spare row col answer := by
  simp only [advance, TM2.step, TM2.stepAux, program, adminProgram, cell,
    Sum.elim_inr, Matrix.cons_val_one, Matrix.cons_val_zero,
    List.head?_cons, List.tail_cons, Option.isSome_some, cond_true, Option.getD_some]
  congr 1
  funext k
  cases k with
  | inl k => fin_cases k <;> simp [Function.update]
  | inr k => fin_cases k <;> simp [Function.update]

theorem copyColScan_nil (v : Control)
    (stream saved edge vertex temp scratch spare row answer : List Bool) :
    advance program (cell (some (.inr .copyColScan)) v stream saved edge vertex
      temp scratch spare row [] answer) =
    cell (some (.inr .copyColRestore)) {v with popped := none} stream saved edge vertex
      temp scratch spare row [] answer := by
  simp only [advance, TM2.step, TM2.stepAux, program, adminProgram, cell,
    Sum.elim_inr, Matrix.cons_val_one, Matrix.cons_val_zero,
    List.head?_nil, List.tail_nil, Option.isSome_none, cond_false, Option.getD_some]
  congr 1
  funext k
  cases k with
  | inl k => fin_cases k <;> simp [Function.update]
  | inr k => fin_cases k <;> simp [Function.update]

theorem copyColRestore_cons (v : Control) (b : Bool)
    (stream saved edge vertex temp scratch spare row col answer : List Bool) :
    advance program (cell (some (.inr .copyColRestore)) v stream saved edge vertex
      temp (b::scratch) spare row col answer) =
    cell (some (.inr .copyColRestore)) {v with popped := some b} stream saved
      (b::edge) vertex temp scratch spare row (b::col) answer := by
  simp only [advance, TM2.step, TM2.stepAux, program, adminProgram, cell,
    Sum.elim_inl]
  have hscratch :
      (![stream, saved, edge, vertex, temp, b::scratch, spare] : Fin 7 → List Bool) 5 =
        b::scratch := rfl
  simp only [hscratch,
    List.head?_cons, List.tail_cons, Option.isSome_some, cond_true, Option.getD_some]
  congr 1
  funext k
  cases k with
  | inl k => fin_cases k <;> simp [Function.update]
  | inr k => fin_cases k <;> simp [Function.update]

theorem copyColRestore_nil (v : Control)
    (stream saved edge vertex temp spare row col answer : List Bool) :
    advance program (cell (some (.inr .copyColRestore)) v stream saved edge vertex
      temp [] spare row col answer) =
    cell (some (.inl .beginEdge)) initial stream saved edge vertex
      temp [] spare row col answer := by
  simp only [advance, TM2.step, TM2.stepAux, program, adminProgram, cell,
    Sum.elim_inl]
  have hscratch :
      (![stream, saved, edge, vertex, temp, ([] : List Bool), spare] : Fin 7 → List Bool) 5 =
        [] := rfl
  simp only [hscratch,
    List.head?_nil, List.tail_nil, Option.isSome_none, cond_false, Option.getD_some]
  congr 1
  funext k
  cases k with
  | inl k => fin_cases k <;> simp [Function.update]
  | inr k => fin_cases k <;> simp [Function.update]

theorem col_scan (v : Control) (stream saved edge vertex temp scratch spare
    row col answer : List Bool) :
    run (col.length+1) (cell (some (.inr .copyColScan)) v stream saved edge vertex
      temp scratch spare row col answer) =
    cell (some (.inr .copyColRestore)) {v with popped := none} stream saved edge vertex
      temp (col.reverse ++ scratch) spare row [] answer := by
  induction col generalizing v scratch with
  | nil => simpa using run_succ 0 _ ▸
      copyColScan_nil v stream saved edge vertex temp scratch spare row answer
  | cons b col ih =>
      rw [List.length_cons, run_succ, copyColScan_cons]
      simpa [List.reverse_cons, List.append_assoc] using
        ih {v with popped := some b} (b::scratch)

theorem col_restore (v : Control) (stream saved edge vertex temp scratch spare
    row col answer : List Bool) :
    run (scratch.length+1) (cell (some (.inr .copyColRestore)) v stream saved edge vertex
      temp scratch spare row col answer) =
    cell (some (.inl .beginEdge)) initial stream saved (scratch.reverse ++ edge)
      vertex temp [] spare row (scratch.reverse ++ col) answer := by
  induction scratch generalizing v edge col with
  | nil => simpa using run_succ 0 _ ▸
      copyColRestore_nil v stream saved edge vertex temp spare row col answer
  | cons b scratch ih =>
      rw [List.length_cons, run_succ, copyColRestore_cons]
      simpa [List.reverse_cons, List.append_assoc] using
        ih {v with popped := some b} (b::edge) (b::col)

theorem copy_col (v : Control) (stream saved edge vertex temp spare
    row col answer : List Bool) :
    run (2*col.length+2) (cell (some (.inr .copyColScan)) v stream saved edge vertex
      temp [] spare row col answer) =
    cell (some (.inl .beginEdge)) initial stream saved (col ++ edge)
      vertex temp [] spare row col answer := by
  have hs := col_scan v stream saved edge vertex temp [] spare row col answer
  have hr := col_restore {v with popped := none} stream saved edge vertex temp
    col.reverse spare row [] answer
  simp only [List.append_nil, List.length_reverse, List.reverse_reverse] at hs hr
  have h := run_add hs (col.length+1) |>.trans hr
  simpa only [Nat.two_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

def scanFrame (scratch spare row col : List Bool)
    (c : SourceGraphPayloadMachine.Config) : Config :=
  renameCfg scannerSlots (Equiv.refl _) controlSlots
    (liftCfg (some .clearVertex) ()
      (![scratch, spare, row, col] : Fin 4 → List Bool) c)

theorem scanFrame_cell (l : Option Phase) (v : Control)
    (stream saved edge vertex temp answer scratch spare row col : List Bool) :
    scanFrame scratch spare row col
      (SourceGraphPayloadMachine.cfg l v stream saved edge vertex temp answer) =
    cell (match l with | none => some (.inr .clearVertex) | some q => some (.inl q))
      v stream saved edge vertex temp scratch spare row col answer := by
  unfold scanFrame renameCfg liftCfg SourceGraphPayloadMachine.cfg cell
  cases l <;> simp only [Option.map_none, Option.map_some, Equiv.refl_apply]
  all_goals
    congr 1
    funext k
    cases k with
    | inl k => fin_cases k <;> rfl
    | inr k => fin_cases k <;> rfl

theorem query_run (edges : List (ℕ × ℕ)) (k r : ℕ)
    (scratch spare row col answer : List Bool) :
    ∃ t ≤ 16 * ((SourceGraphPayloadMachine.endpointStream edges).length + 1) *
        (edges.length + 1), ∃ c edge,
      run t (cell (some (.inl .beginEdge)) initial
        (SourceGraphPayloadMachine.endpointStream edges) []
        (List.replicate k true) (List.replicate r true) []
        scratch spare row col answer) =
      cell (some (.inr .clearVertex)) c
        (SourceGraphPayloadMachine.endpointStream edges) [] edge
        (List.replicate r true) [] scratch spare row col
        (SourceGraphPayloadMachine.endpointHit edges k r :: answer) ∧
      edge.length ≤ k := by
  open BitMachineSubroutineRenaming in
    obtain ⟨t, ht, c, edge, he, hlen⟩ :=
      SourceGraphPayloadMachine.endpoint_query_run edges k r none [] answer
  have he' : SourceGraphPayloadMachine.run t
      (SourceGraphPayloadMachine.cfg (some .beginEdge) initial
        (SourceGraphPayloadMachine.endpointStream edges) []
        (List.replicate k true) (List.replicate r true) [] answer) =
      SourceGraphPayloadMachine.cfg none c
        (SourceGraphPayloadMachine.endpointStream edges) [] edge
        (List.replicate r true) []
        (SourceGraphPayloadMachine.endpointHit edges k r :: answer) := by
    simpa only [initial, SourceGraphPayloadMachine.state,
      List.reverse_nil, List.nil_append, List.length_nil, Nat.zero_add] using he
  have hhalt :
      (((advance SourceGraphPayloadMachine.program)^[t])
        (SourceGraphPayloadMachine.cfg (some .beginEdge) initial
          (SourceGraphPayloadMachine.endpointStream edges) []
          (List.replicate k true) (List.replicate r true) [] answer)).l = none := by
    change (SourceGraphPayloadMachine.run t _).l = none
    rw [he']
    rfl
  obtain ⟨u, hu, hr⟩ :=
    BitMachineSubroutineRenaming.lift_outputs_renamed scannerSlots
      (Equiv.refl _) controlSlots SourceGraphPayloadMachine.program program
      (some .clearVertex) (fun _ => rfl) ()
      (![scratch, spare, row, col] : Fin 4 → List Bool)
      (SourceGraphPayloadMachine.cfg (some .beginEdge) initial
        (SourceGraphPayloadMachine.endpointStream edges) []
        (List.replicate k true) (List.replicate r true) [] answer) t hhalt
  change run u (scanFrame scratch spare row col _) =
    scanFrame scratch spare row col (SourceGraphPayloadMachine.run t _) at hr
  rw [he'] at hr
  refine ⟨u, by simpa using hu.trans ht, c, edge, ?_, hlen⟩
  simpa only [scanFrame_cell] using hr

theorem clearVertex_cons (v : Control) (b : Bool)
    (stream saved edge vertex temp scratch spare row col answer : List Bool) :
    advance program (cell (some (.inr .clearVertex)) v stream saved edge
      (b::vertex) temp scratch spare row col answer) =
    cell (some (.inr .clearVertex)) {v with popped := some b} stream saved edge
      vertex temp scratch spare row col answer := by
  simp only [advance, TM2.step, TM2.stepAux, program, adminProgram, cell,
    Sum.elim_inl]
  have hv :
      (![stream, saved, edge, b::vertex, temp, scratch, spare] : Fin 7 → List Bool) 3 =
        b::vertex := rfl
  simp only [hv, List.head?_cons, List.tail_cons, Option.isSome_some, cond_true,
    Option.getD_some]
  congr 1
  funext k
  cases k with
  | inl k => fin_cases k <;> simp [Function.update]
  | inr k => fin_cases k <;> simp [Function.update]

theorem clearVertex_nil (v : Control)
    (stream saved edge temp scratch spare row col answer : List Bool) :
    advance program (cell (some (.inr .clearVertex)) v stream saved edge
      [] temp scratch spare row col answer) =
    cell (some (.inr .clearEdge)) {v with popped := none} stream saved edge
      [] temp scratch spare row col answer := by
  simp only [advance, TM2.step, TM2.stepAux, program, adminProgram, cell,
    Sum.elim_inl]
  have hv :
      (![stream, saved, edge, ([] : List Bool), temp, scratch, spare] : Fin 7 → List Bool) 3 =
        [] := rfl
  simp only [hv, List.head?_nil, List.tail_nil, Option.isSome_none, cond_false,
    Option.getD_some]
  congr 1
  funext k
  cases k with
  | inl k => fin_cases k <;> simp [Function.update]
  | inr k => fin_cases k <;> simp [Function.update]

theorem clearEdge_cons (v : Control) (b : Bool)
    (stream saved edge vertex temp scratch spare row col answer : List Bool) :
    advance program (cell (some (.inr .clearEdge)) v stream saved
      (b::edge) vertex temp scratch spare row col answer) =
    cell (some (.inr .clearEdge)) {v with popped := some b} stream saved
      edge vertex temp scratch spare row col answer := by
  simp only [advance, TM2.step, TM2.stepAux, program, adminProgram, cell,
    Sum.elim_inl]
  have he :
      (![stream, saved, b::edge, vertex, temp, scratch, spare] : Fin 7 → List Bool) 2 =
        b::edge := rfl
  simp only [he, List.head?_cons, List.tail_cons, Option.isSome_some, cond_true,
    Option.getD_some]
  congr 1
  funext k
  cases k with
  | inl k => fin_cases k <;> simp [Function.update]
  | inr k => fin_cases k <;> simp [Function.update]

theorem clearEdge_nil (v : Control)
    (stream saved vertex temp scratch spare row col answer : List Bool) :
    advance program (cell (some (.inr .clearEdge)) v stream saved
      [] vertex temp scratch spare row col answer) =
    cell none {v with popped := none} stream saved [] vertex
      temp scratch spare row col answer := by
  simp only [advance, TM2.step, TM2.stepAux, program, adminProgram, cell,
    Sum.elim_inl]
  have he :
      (![stream, saved, ([] : List Bool), vertex, temp, scratch, spare] : Fin 7 → List Bool) 2 =
        [] := rfl
  simp only [he, List.head?_nil, List.tail_nil, Option.isSome_none, cond_false,
    Option.getD_some]
  congr 1
  funext k
  cases k with
  | inl k => fin_cases k <;> simp [Function.update]
  | inr k => fin_cases k <;> simp [Function.update]

theorem clear_vertex (v : Control)
    (stream saved edge vertex temp scratch spare row col answer : List Bool) :
    run (vertex.length+1) (cell (some (.inr .clearVertex)) v stream saved edge
      vertex temp scratch spare row col answer) =
    cell (some (.inr .clearEdge)) {v with popped := none} stream saved edge
      [] temp scratch spare row col answer := by
  induction vertex generalizing v with
  | nil => simpa using run_succ 0 _ ▸
      clearVertex_nil v stream saved edge temp scratch spare row col answer
  | cons b vertex ih =>
      rw [List.length_cons, run_succ, clearVertex_cons]
      exact ih {v with popped := some b}

theorem clear_edge (v : Control)
    (stream saved edge vertex temp scratch spare row col answer : List Bool) :
    run (edge.length+1) (cell (some (.inr .clearEdge)) v stream saved edge
      vertex temp scratch spare row col answer) =
    cell none {v with popped := none} stream saved [] vertex
      temp scratch spare row col answer := by
  induction edge generalizing v with
  | nil => simpa using run_succ 0 _ ▸
      clearEdge_nil v stream saved vertex temp scratch spare row col answer
  | cons b edge ih =>
      rw [List.length_cons, run_succ, clearEdge_cons]
      exact ih {v with popped := some b}

/-- The writer callback receives only the ordered unary endpoint stream and
the writer's two physical unary indices.  It restores all persistent cells
and both indices, and returns exactly one incidence bit. -/
theorem cell_run (edges : List (ℕ × ℕ)) (x y : ℕ) :
    let stream := SourceGraphPayloadMachine.endpointStream edges
    ∃ t ≤ 3*x + 3*y + 6 + 16*(stream.length+1)*(edges.length+1), ∃ v,
      run t (cell (some start) initial stream [] [] [] [] [] []
        (List.replicate x true) (List.replicate y true) []) =
      cell none v stream [] [] [] [] [] []
        (List.replicate x true) (List.replicate y true)
        [SourceGraphPayloadMachine.endpointHit edges y x] := by
  let stream := SourceGraphPayloadMachine.endpointStream edges
  let row := List.replicate x true
  let col := List.replicate y true
  have hr := copy_row initial stream [] [] [] [] [] row col []
  have hc := copy_col {initial with popped := none} stream [] [] row [] [] row col []
  obtain ⟨q,hq,c,edge,hquery,hlen⟩ := query_run edges y x [] [] row col []
  have hv := clear_vertex c stream [] edge row [] [] [] row col
    [SourceGraphPayloadMachine.endpointHit edges y x]
  have he := clear_edge {c with popped := none} stream [] edge [] [] [] [] row col
    [SourceGraphPayloadMachine.endpointHit edges y x]
  refine ⟨2*x+2+2*y+2+q+(x+1)+(edge.length+1), ?_, {c with popped := none}, ?_⟩
  · simp only [row, col, List.length_replicate] at hr hc hv he
    omega
  · change run _ (cell (some (.inr .copyRowScan)) initial stream [] [] [] [] [] []
      row col []) = _
    simp only [row, col, List.length_replicate, List.append_nil] at hr hc hv he hquery ⊢
    have hcomp : run ((2*x+2)+((2*y+2)+(q+((x+1)+(edge.length+1)))))
        (cell (some (.inr .copyRowScan)) initial stream [] [] [] [] [] []
          (List.replicate x true) (List.replicate y true) []) =
        cell none {c with popped := none} stream [] [] [] [] [] []
          (List.replicate x true) (List.replicate y true)
          [SourceGraphPayloadMachine.endpointHit edges y x] := by
      rw [run_add hr, run_add hc, run_add hquery, run_add hv, he]
    have htime : 2*x+2+2*y+2+q+(x+1)+(edge.length+1) =
        (2*x+2)+((2*y+2)+(q+((x+1)+(edge.length+1)))) := by omega
    rw [htime]
    exact hcomp

theorem frame (l : Option Label) (v : Control) (stream : List Bool)
    (x y : ℕ) (answer : List Bool) :
    cell l v stream [] [] [] [] [] []
      (List.replicate x true) (List.replicate y true) answer =
    MatrixTableWriter.cellCfg l v (bank stream) x y answer := by
  unfold cell MatrixTableWriter.cellCfg bank
  congr 1

def entry (edges : List (ℕ × ℕ)) (x y : ℕ) : Bool :=
  SourceGraphPayloadMachine.endpointHit edges y x

def entryBound (edges : List (ℕ × ℕ)) (vertices : ℕ) : ℕ :=
  3*vertices + 3*edges.length + 6 +
    16*((SourceGraphPayloadMachine.endpointStream edges).length+1)*(edges.length+1)

theorem entry_runs (edges : List (ℕ × ℕ)) (vertices : ℕ) :
    MatrixTableWriter.EntryRuns program start initial
      (bank (SourceGraphPayloadMachine.endpointStream edges))
      vertices edges.length (entryBound edges vertices) (entry edges) := by
  intro x hx y hy
  obtain ⟨t,ht,v,hr⟩ := cell_run edges x y
  refine ⟨t, ?_, v, ?_⟩
  · dsimp only [entryBound] at *
    omega
  · simpa only [frame, entry] using hr

def baseBits (g : EncodedGraph.Graph) (hg : g.Valid) : List Bool :=
  MatrixMaterialization.rowMajor
    (fun i α => decide (∃ j : Fin 2, i = EncodedGraph.endpoints g hg α j))

theorem write_base (g : EncodedGraph.Graph) (hg : g.Valid) (output : List Bool) :
    ∃ t ≤ MatrixTableWriter.writerBound g.vertices g.edges.length
        (entryBound g.edges g.vertices), ∃ v,
      MatrixTableWriter.run program start initial t
        (MatrixTableWriter.cfg (some (.inr (.copy .rows))) (initial, none)
          (MatrixTableWriter.ready
            (bank (SourceNormalizationMachineDecode.endpointStream g))
            g.vertices g.edges.length 0 0 0 0 [] output)) =
      MatrixTableWriter.cfg none v
        (MatrixTableWriter.ready
          (bank (SourceNormalizationMachineDecode.endpointStream g))
          g.vertices g.edges.length 0 0 0 0 []
          (baseBits g hg ++ output)) := by
  let f : Fin g.vertices → Fin g.edges.length → Bool :=
    fun i α => decide (∃ j : Fin 2, i = EncodedGraph.endpoints g hg α j)
  have hentry : ∀ i α, entry g.edges i.val α.val = f i α := by
    intro i α
    exact SourceGraphPayloadMachine.endpointHit_graph g hg α i
  have hr := MatrixTableWriter.write_rowMajor program start initial
    (bank (SourceGraphPayloadMachine.endpointStream g.edges))
    g.vertices g.edges.length (entryBound g.edges g.vertices)
    (entry g.edges) f hentry (entry_runs g.edges g.vertices) output
  simpa only [SourceGraphPayloadMachine.endpointStream_graph, baseBits, f] using hr

end EthInapproximability.CurrentPaper.SourceGraphPayloadMachine.BaseCell

namespace EthInapproximability.CurrentPaper.SourceGraphPayloadMachine.Expansion

open Turing Turing.TM2.Stmt BitMachineEncoding

/- A streaming expansion of the physically written one-copy incidence table.
Only the copy and group selectors are finite control data.  All unbounded
source, dimension, vertex and edge counts live in Boolean stacks. -/

abbrev Stack := Fin 11

inductive Kind where
  | base | vertices | edges | dimension
  deriving DecidableEq, Fintype

inductive Label where
  | startCopy (c : Fin 6)
  | copyScan (kind : Kind) (c j : Fin 6)
  | copyRestore (kind : Kind) (c j : Fin 6)
  | startRow (c : Fin 6)
  | startGroup (c j : Fin 6)
  | groupStep (c j : Fin 6)
  | emit (c j : Fin 6)
  | padding (c : Fin 6)
  | reverse
  deriving DecidableEq, Fintype

structure Control where
  popped : Option Bool := none
  bit : Bool := false
  available : Bool := false
  deriving DecidableEq, Fintype

abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

def source : Kind → Stack
  | .base => 0
  | .vertices => 1
  | .edges => 2
  | .dimension => 3

def target : Kind → Stack
  | .base => 4
  | .vertices => 6
  | .edges => 7
  | .dimension => 8

def next (j : Fin 6) : Fin 6 := ⟨min 5 (j.val+1), by omega⟩

def afterCopy (kind : Kind) (c j : Fin 6) : Label :=
  match kind with
  | .base => .copyScan .vertices c 0
  | .vertices => .startRow c
  | .edges => .groupStep c j
  | .dimension => .startGroup c 0

def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .startCopy c =>
      if c = 5 then goto (fun _ => .reverse)
      else goto (fun _ => .copyScan .base c 0)
  | .copyScan kind c j =>
      pop (source kind) (fun v b => {v with popped := b})
        (branch (fun v => v.popped.isSome)
          (push 5 (fun v => v.popped.getD false)
            (goto (fun _ => .copyScan kind c j)))
          (goto (fun _ => .copyRestore kind c j)))
  | .copyRestore kind c j =>
      pop 5 (fun v b => {v with popped := b})
        (branch (fun v => v.popped.isSome)
          (push (source kind) (fun v => v.popped.getD false)
            (push (target kind) (fun v => v.popped.getD false)
              (goto (fun _ => .copyRestore kind c j))))
          (goto (fun _ => afterCopy kind c j)))
  | .startRow c =>
      pop 6 (fun v b => {v with popped := b})
        (branch (fun v => v.popped.isSome)
          (goto (fun _ => .copyScan .dimension c 0))
          (goto (fun _ => .startCopy (next c))))
  | .startGroup c j =>
      if j = 5 then goto (fun _ => .padding c)
      else goto (fun _ => .copyScan .edges c j)
  | .groupStep c j =>
      pop 7 (fun v b => {v with popped := b})
        (branch (fun v => v.popped.isSome)
          (if c = j then
            pop 4 (fun v b => {v with bit := b.getD false})
              (goto (fun _ => .emit c j))
          else goto (fun _ => .emit c j))
          (goto (fun _ => .startGroup c (next j))))
  | .emit c j =>
      pop 8 (fun v b => {v with available := b.isSome})
        (branch Control.available
          (push 9 (fun v => if c = j then v.bit else false)
            (goto (fun _ => .groupStep c j)))
          (goto (fun _ => .groupStep c j)))
  | .padding c =>
      pop 8 (fun v b => {v with available := b.isSome})
        (branch Control.available
          (push 9 (fun _ => false) (goto (fun _ => .padding c)))
          (goto (fun _ => .startRow c)))
  | .reverse =>
      pop 9 (fun v b => {v with popped := b})
        (branch (fun v => v.popped.isSome)
          (push 10 (fun v => v.popped.getD false) (goto (fun _ => .reverse)))
          halt)

def cfg (l : Option Label) (s : Control)
    (base vertices edges dimension cursor scratch rowsLeft groupLeft dimLeft
      buffer output : List Bool) : Config :=
  ⟨l, s, ![base, vertices, edges, dimension, cursor, scratch, rowsLeft,
    groupLeft, dimLeft, buffer, output]⟩

def run (t : ℕ) (c : Config) : Config := ((advance program)^[t]) c

def input (base : List Bool) (v m D : ℕ) : Config :=
  cfg (some (.startCopy 0)) {} base
    (List.replicate v true) (List.replicate m true) (List.replicate D true)
    [] [] [] [] [] [] []

def output (base : List Bool) (v m D : ℕ) (bits : List Bool) : Config :=
  cfg none {} base
    (List.replicate v true) (List.replicate m true) (List.replicate D true)
    [] [] [] [] [] [] bits

structure Data where
  base : List Bool := []
  vertices : List Bool := []
  edges : List Bool := []
  dimension : List Bool := []
  cursor : List Bool := []
  scratch : List Bool := []
  rowsLeft : List Bool := []
  groupLeft : List Bool := []
  dimLeft : List Bool := []
  buffer : List Bool := []
  output : List Bool := []

def Data.contents (d : Data) : Stack → List Bool :=
  ![d.base, d.vertices, d.edges, d.dimension, d.cursor, d.scratch,
    d.rowsLeft, d.groupLeft, d.dimLeft, d.buffer, d.output]

def frame (l : Option Label) (s : Control) (d : Data) : Config :=
  ⟨l, s, d.contents⟩

def Data.get (d : Data) : Kind → List Bool
  | .base => d.base
  | .vertices => d.vertices
  | .edges => d.edges
  | .dimension => d.dimension

def Data.set (d : Data) (kind : Kind) (bits : List Bool) : Data :=
  match kind with
  | .base => {d with base := bits}
  | .vertices => {d with vertices := bits}
  | .edges => {d with edges := bits}
  | .dimension => {d with dimension := bits}

def Data.addTarget (d : Data) (kind : Kind) (bits : List Bool) : Data :=
  match kind with
  | .base => {d with cursor := bits ++ d.cursor}
  | .vertices => {d with rowsLeft := bits ++ d.rowsLeft}
  | .edges => {d with groupLeft := bits ++ d.groupLeft}
  | .dimension => {d with dimLeft := bits ++ d.dimLeft}

@[simp] theorem Data.contents_source (d : Data) (kind : Kind) :
    d.contents (source kind) = d.get kind := by cases kind <;> rfl

@[simp] theorem Data.contents_scratch (d : Data) : d.contents 5 = d.scratch := rfl
@[simp] theorem Data.contents_cursor (d : Data) : d.contents 4 = d.cursor := rfl
@[simp] theorem Data.contents_rowsLeft (d : Data) : d.contents 6 = d.rowsLeft := rfl
@[simp] theorem Data.contents_groupLeft (d : Data) : d.contents 7 = d.groupLeft := rfl
@[simp] theorem Data.contents_dimLeft (d : Data) : d.contents 8 = d.dimLeft := rfl
@[simp] theorem Data.contents_buffer (d : Data) : d.contents 9 = d.buffer := rfl

theorem run_succ (t : ℕ) (c : Config) :
    run (t+1) c = run t (advance program c) :=
  Function.iterate_succ_apply _ _ _

theorem run_add {c d : Config} {t : ℕ} (h : run t c = d) (u : ℕ) :
    run (t+u) c = run u d := by
  rw [Nat.add_comm t u]
  simp only [run, Function.iterate_add_apply] at h ⊢
  rw [h]

theorem copyScan_cons (kind : Kind) (c j : Fin 6) (s : Control)
    (b : Bool) (bits : List Bool) (d : Data) (h : d.get kind = b::bits) :
    advance program (frame (some (.copyScan kind c j)) s d) =
    frame (some (.copyScan kind c j)) {s with popped := some b}
      {(d.set kind bits) with scratch := b::d.scratch} := by
  cases kind <;> simp only [Data.get] at h
  all_goals
    simp only [advance, TM2.step, TM2.stepAux, program, frame,
      Data.contents_source, Data.get, h, List.head?_cons, List.tail_cons,
      Option.isSome_some, cond_true, Option.getD_some]
    congr 1
    funext k
    fin_cases k <;> simp [source, Function.update, Data.contents, Data.set]

theorem copyScan_nil (kind : Kind) (c j : Fin 6) (s : Control)
    (d : Data) (h : d.get kind = []) :
    advance program (frame (some (.copyScan kind c j)) s d) =
    frame (some (.copyRestore kind c j)) {s with popped := none} d := by
  cases kind <;> simp only [Data.get] at h
  all_goals
    simp only [advance, TM2.step, TM2.stepAux, program, frame,
      Data.contents_source, Data.get, h, List.head?_nil, List.tail_nil,
      Option.isSome_none, cond_false, Option.getD_some]
    congr 1
    funext k
    fin_cases k <;> simp [source, Function.update, Data.contents, h]

theorem copyRestore_cons (kind : Kind) (c j : Fin 6) (s : Control)
    (b : Bool) (bits : List Bool) (d : Data) (h : d.scratch = b::bits) :
    advance program (frame (some (.copyRestore kind c j)) s d) =
    frame (some (.copyRestore kind c j)) {s with popped := some b}
      (({d with scratch := bits}.set kind (b::d.get kind)).addTarget kind [b]) := by
  cases kind
  all_goals
    simp only [advance, TM2.step, TM2.stepAux, program,
      frame, Data.contents_scratch, h,
      List.head?_cons, List.tail_cons, Option.isSome_some, cond_true, Option.getD_some,
      List.singleton_append]
    congr 1
    funext k
    fin_cases k <;> simp [source, target, Function.update,
      Data.contents, Data.get, Data.set, Data.addTarget]

theorem copyRestore_nil (kind : Kind) (c j : Fin 6) (s : Control)
    (d : Data) (h : d.scratch = []) :
    advance program (frame (some (.copyRestore kind c j)) s d) =
    frame (some (afterCopy kind c j)) {s with popped := none} d := by
  cases kind
  all_goals
    simp only [advance, TM2.step, TM2.stepAux, program, afterCopy,
      frame, Data.contents_scratch, h, List.head?_nil, List.tail_nil,
      Option.isSome_none, cond_false, Option.getD_some]
    congr 1
    funext k
    fin_cases k <;> simp [Function.update, Data.contents, h]

theorem copy_scan_run (kind : Kind) (c j : Fin 6) (s : Control) (d : Data) :
    run ((d.get kind).length+1) (frame (some (.copyScan kind c j)) s d) =
    frame (some (.copyRestore kind c j)) {s with popped := none}
      {(d.set kind []) with scratch := (d.get kind).reverse ++ d.scratch} := by
  generalize h : d.get kind = bits
  induction bits generalizing s d with
  | nil =>
      rw [show ([] : List Bool).length+1 = 0+1 from rfl,
        run_succ, copyScan_nil kind c j s d h]
      simp only [run, Function.iterate_zero, id_eq, List.reverse_nil, List.nil_append]
      congr 1
      cases kind <;> cases d <;> simp_all [Data.get, Data.set]
  | cons b bits ih =>
      rw [List.length_cons, run_succ, copyScan_cons kind c j s b bits d h,
        ih _ _ (by cases kind <;> rfl)]
      cases kind <;> simp [Data.get, Data.set, List.reverse_cons,
        List.append_assoc]

theorem copy_restore_run (kind : Kind) (c j : Fin 6) (s : Control) (d : Data) :
    run (d.scratch.length+1) (frame (some (.copyRestore kind c j)) s d) =
    frame (some (afterCopy kind c j)) {s with popped := none}
      (({d with scratch := []}.set kind (d.scratch.reverse ++ d.get kind)).addTarget
        kind d.scratch.reverse) := by
  generalize h : d.scratch = bits
  induction bits generalizing s d with
  | nil =>
      rw [show ([] : List Bool).length+1 = 0+1 from rfl,
        run_succ, copyRestore_nil kind c j s d h]
      simp only [run, Function.iterate_zero, id_eq, List.reverse_nil, List.nil_append]
      congr 1
      cases kind <;> cases d <;> simp_all [Data.get, Data.set, Data.addTarget]
  | cons b bits ih =>
      rw [List.length_cons, run_succ, copyRestore_cons kind c j s b bits d h,
        ih _ _ (by cases kind <;> rfl)]
      cases kind <;> simp [Data.get, Data.set, Data.addTarget,
        List.reverse_cons, List.append_assoc]

theorem copy_run (kind : Kind) (c j : Fin 6) (s : Control) (d : Data)
    (h : d.scratch = []) :
    run (2*(d.get kind).length+2) (frame (some (.copyScan kind c j)) s d) =
    frame (some (afterCopy kind c j)) {s with popped := none}
      (d.addTarget kind (d.get kind)) := by
  have hs := copy_scan_run kind c j s d
  have hr := copy_restore_run kind c j {s with popped := none}
    {(d.set kind []) with scratch := (d.get kind).reverse ++ d.scratch}
  simp only [h, List.append_nil] at hs
  simp only [h, List.append_nil, List.length_reverse, List.reverse_reverse] at hr
  have hrun := run_add hs ((d.get kind).length+1) |>.trans hr
  have htime : (d.get kind).length+1+((d.get kind).length+1) =
      2*(d.get kind).length+2 := by omega
  rw [htime] at hrun
  rcases d with ⟨base, vertices, edges, dimension, cursor, scratch,
    rowsLeft, groupLeft, dimLeft, buffer, output⟩
  simp only [Data.scratch] at h
  subst scratch
  cases kind <;>
    simpa [Data.get, Data.set, Data.addTarget] using hrun

theorem startCopy_more (c : Fin 6) (s : Control) (d : Data) (hc : c ≠ 5) :
    advance program (frame (some (.startCopy c)) s d) =
    frame (some (.copyScan .base c 0)) s d := by
  simp [advance, TM2.step, TM2.stepAux, program, frame, hc]

theorem startCopy_done (s : Control) (d : Data) :
    advance program (frame (some (.startCopy 5)) s d) =
    frame (some .reverse) s d := by
  simp [advance, TM2.step, TM2.stepAux, program, frame]

theorem startRow_cons (c : Fin 6) (s : Control) (b : Bool) (bits : List Bool)
    (d : Data) (h : d.rowsLeft = b::bits) :
    advance program (frame (some (.startRow c)) s d) =
    frame (some (.copyScan .dimension c 0)) {s with popped := some b}
      {d with rowsLeft := bits} := by
  simp only [advance, TM2.step, TM2.stepAux, program, frame,
    Data.contents_rowsLeft, h, List.head?_cons, List.tail_cons,
    Option.isSome_some, cond_true, Option.getD_some]
  congr 1
  funext k
  fin_cases k <;> simp [Function.update, Data.contents]

theorem startRow_nil (c : Fin 6) (s : Control) (d : Data)
    (h : d.rowsLeft = []) :
    advance program (frame (some (.startRow c)) s d) =
    frame (some (.startCopy (next c))) {s with popped := none} d := by
  simp only [advance, TM2.step, TM2.stepAux, program, frame,
    Data.contents_rowsLeft, h, List.head?_nil, List.tail_nil,
    Option.isSome_none, cond_false, Option.getD_some]
  congr 1
  funext k
  fin_cases k <;> simp [Function.update, Data.contents, h]

theorem startGroup_more (c j : Fin 6) (s : Control) (d : Data) (hj : j ≠ 5) :
    advance program (frame (some (.startGroup c j)) s d) =
    frame (some (.copyScan .edges c j)) s d := by
  simp [advance, TM2.step, TM2.stepAux, program, frame, hj]

theorem startGroup_done (c : Fin 6) (s : Control) (d : Data) :
    advance program (frame (some (.startGroup c 5)) s d) =
    frame (some (.padding c)) s d := by
  simp [advance, TM2.step, TM2.stepAux, program, frame]

theorem padding_cons (c : Fin 6) (s : Control) (b : Bool) (bits : List Bool)
    (d : Data) (h : d.dimLeft = b::bits) :
    advance program (frame (some (.padding c)) s d) =
    frame (some (.padding c)) {s with available := true}
      {d with dimLeft := bits, buffer := false::d.buffer} := by
  simp only [advance, TM2.step, TM2.stepAux, program, frame,
    Data.contents_dimLeft, h, List.head?_cons, List.tail_cons,
    Option.isSome_some, cond_true, Option.getD_some]
  congr 1
  funext k
  fin_cases k <;> simp [Function.update, Data.contents]

theorem padding_nil (c : Fin 6) (s : Control) (d : Data)
    (h : d.dimLeft = []) :
    advance program (frame (some (.padding c)) s d) =
    frame (some (.startRow c)) {s with available := false} d := by
  simp only [advance, TM2.step, TM2.stepAux, program, frame,
    Data.contents_dimLeft, h, List.head?_nil, List.tail_nil,
    Option.isSome_none, cond_false, Option.getD_some]
  congr 1
  funext k
  fin_cases k <;> simp [Function.update, Data.contents, h]

theorem reverse_cons (s : Control) (b : Bool) (bits : List Bool)
    (d : Data) (h : d.buffer = b::bits) :
    advance program (frame (some .reverse) s d) =
    frame (some .reverse) {s with popped := some b}
      {d with buffer := bits, output := b::d.output} := by
  simp only [advance, TM2.step, TM2.stepAux, program, frame,
    Data.contents_buffer, h, List.head?_cons, List.tail_cons,
    Option.isSome_some, cond_true, Option.getD_some]
  congr 1
  funext k
  fin_cases k <;> simp [Function.update, Data.contents]

theorem reverse_nil (s : Control) (d : Data) (h : d.buffer = []) :
    advance program (frame (some .reverse) s d) =
    frame none {s with popped := none} d := by
  simp only [advance, TM2.step, TM2.stepAux, program, frame,
    Data.contents_buffer, h, List.head?_nil, List.tail_nil,
    Option.isSome_none, cond_false, Option.getD_some]
  congr 1
  funext k
  fin_cases k <;> simp [Function.update, Data.contents, h]

theorem padding_run (c : Fin 6) (s : Control) (d : Data) :
    run (d.dimLeft.length+1) (frame (some (.padding c)) s d) =
    frame (some (.startRow c)) {s with available := false}
      {d with dimLeft := [], buffer := List.replicate d.dimLeft.length false ++ d.buffer} := by
  generalize h : d.dimLeft = bits
  induction bits generalizing s d with
  | nil =>
      rw [show ([] : List Bool).length+1 = 0+1 from rfl,
        run_succ, padding_nil c s d h]
      simp only [run, Function.iterate_zero, id_eq, List.length_nil,
        List.replicate_zero, List.nil_append]
      cases d <;> simp_all
  | cons b bits ih =>
      rw [List.length_cons, run_succ, padding_cons c s b bits d h,
        ih _ _ (by rfl)]
      have hrotate (n : ℕ) (tail : List Bool) :
          List.replicate n false ++ false::tail =
            false::(List.replicate n false ++ tail) := by
        induction n with
        | zero => rfl
        | succ n ih => simpa [List.replicate_succ, List.append_assoc] using ih
      simp only [List.length_cons, List.replicate_succ, hrotate]
      simp only [List.cons_append, List.append_assoc]

theorem reverse_run (s : Control) (d : Data) :
    run (d.buffer.length+1) (frame (some .reverse) s d) =
    frame none {s with popped := none}
      {d with buffer := [], output := d.buffer.reverse ++ d.output} := by
  generalize h : d.buffer = bits
  induction bits generalizing s d with
  | nil =>
      rw [show ([] : List Bool).length+1 = 0+1 from rfl,
        run_succ, reverse_nil s d h]
      simp only [run, Function.iterate_zero, id_eq, List.reverse_nil, List.nil_append]
      cases d <;> simp_all
  | cons b bits ih =>
      rw [List.length_cons, run_succ, reverse_cons s b bits d h,
        ih _ _ (by rfl)]
      simp [List.reverse_cons, List.append_assoc]

theorem groupStep_nil (c j : Fin 6) (s : Control) (d : Data)
    (h : d.groupLeft = []) :
    advance program (frame (some (.groupStep c j)) s d) =
    frame (some (.startGroup c (next j))) {s with popped := none} d := by
  simp only [advance, TM2.step, TM2.stepAux, program, frame,
    Data.contents_groupLeft, h, List.head?_nil, List.tail_nil,
    Option.isSome_none, cond_false, Option.getD_some]
  congr 1
  funext k
  fin_cases k <;> simp [Function.update, Data.contents, h]

theorem groupStep_match (c : Fin 6) (s : Control) (d : Data)
    (b a : Bool) (bs rest : List Bool)
    (hg : d.groupLeft = b::bs) (hc : d.cursor = a::rest) :
    advance program (frame (some (.groupStep c c)) s d) =
    frame (some (.emit c c)) {s with popped := some b, bit := a}
      {d with groupLeft := bs, cursor := rest} := by
  simp only [advance, TM2.step, TM2.stepAux, program, frame,
    Data.contents_groupLeft, Data.contents_cursor, hg, hc,
    List.head?_cons, List.tail_cons, Option.isSome_some, cond_true,
    Option.getD_some, ↓reduceIte]
  have hcursor : Function.update d.contents (7 : Stack) bs 4 = a::rest := by
    simp [Function.update, Data.contents_cursor, hc]
  simp only [hcursor, List.head?_cons, List.tail_cons, Option.getD_some]
  congr 1
  funext k
  fin_cases k <;> simp [Function.update, Data.contents]

theorem groupStep_other (c j : Fin 6) (hneq : c ≠ j) (s : Control)
    (d : Data) (b : Bool) (bs : List Bool) (hg : d.groupLeft = b::bs) :
    advance program (frame (some (.groupStep c j)) s d) =
    frame (some (.emit c j)) {s with popped := some b}
      {d with groupLeft := bs} := by
  simp only [advance, TM2.step, TM2.stepAux, program, frame,
    Data.contents_groupLeft, hg, List.head?_cons, List.tail_cons,
    Option.isSome_some, cond_true, Option.getD_some]
  simp only [if_neg hneq]
  simp only [TM2.stepAux]
  congr 1
  funext k
  fin_cases k <;> simp [Function.update, Data.contents]

theorem emit_cons (c j : Fin 6) (s : Control) (d : Data)
    (b : Bool) (bs : List Bool) (hd : d.dimLeft = b::bs) :
    advance program (frame (some (.emit c j)) s d) =
    frame (some (.groupStep c j)) {s with available := true}
      {d with dimLeft := bs, buffer := (if c=j then s.bit else false)::d.buffer} := by
  simp only [advance, TM2.step, TM2.stepAux, program, frame,
    Data.contents_dimLeft, hd, List.head?_cons, List.tail_cons,
    Option.isSome_some, cond_true, Option.getD_some]
  congr 1
  funext k
  fin_cases k <;> simp [Function.update, Data.contents]

theorem match_pair (c : Fin 6) (s : Control) (d : Data)
    (b a : Bool) (bs rest dimRest : List Bool)
    (hg : d.groupLeft = b::bs) (hc : d.cursor = a::rest)
    (hd : d.dimLeft = true::dimRest) :
    run 2 (frame (some (.groupStep c c)) s d) =
    frame (some (.groupStep c c))
      {s with popped := some b, bit := a, available := true}
      {d with groupLeft := bs, cursor := rest, dimLeft := dimRest, buffer := a::d.buffer} := by
  rw [show 2 = 1+1 by omega, run_succ 1, groupStep_match c s d b a bs rest hg hc,
    run_succ 0, emit_cons c c {s with popped := some b, bit := a}
      {d with groupLeft := bs, cursor := rest} true dimRest (by simpa using hd)]
  simp [run]

theorem other_pair (c j : Fin 6) (hneq : c ≠ j) (s : Control)
    (d : Data) (b : Bool) (bs dimRest : List Bool)
    (hg : d.groupLeft = b::bs) (hd : d.dimLeft = true::dimRest) :
    run 2 (frame (some (.groupStep c j)) s d) =
    frame (some (.groupStep c j))
      {s with popped := some b, available := true}
      {d with groupLeft := bs, dimLeft := dimRest, buffer := false::d.buffer} := by
  rw [show 2 = 1+1 by omega, run_succ 1, groupStep_other c j hneq s d b bs hg,
    run_succ 0, emit_cons c j {s with popped := some b}
      {d with groupLeft := bs} true dimRest (by simpa using hd)]
  simp [run, hneq]

theorem match_group (c : Fin 6) (s : Control) (d : Data)
    (word tail dimRest : List Bool)
    (hg : d.groupLeft = List.replicate word.length true)
    (hc : d.cursor = word ++ tail)
    (hd : d.dimLeft = List.replicate word.length true ++ dimRest) :
    ∃ s', run (2*word.length+1) (frame (some (.groupStep c c)) s d) =
      frame (some (.startGroup c (next c))) s'
        {d with groupLeft := [], cursor := tail, dimLeft := dimRest, buffer := word.reverse ++ d.buffer} := by
  induction word generalizing s d with
  | nil =>
      refine ⟨{s with popped := none}, ?_⟩
      have hs := groupStep_nil c c s d (by simpa only [List.length_nil, List.replicate_zero] using hg)
      have heq : d = {d with groupLeft := [], cursor := tail, dimLeft := dimRest, buffer := d.buffer} := by
        cases d <;> simp_all
      have hs' : advance program (frame (some (.groupStep c c)) s d) =
          frame (some (.startGroup c (next c))) {s with popped := none}
            {d with groupLeft := [], cursor := tail, dimLeft := dimRest, buffer := d.buffer} := by
        rw [← heq]
        exact hs
      simpa only [List.length_nil, Nat.mul_zero, Nat.zero_add,
        List.reverse_nil, List.nil_append, run_succ, run,
        Function.iterate_zero, id_eq] using hs'
  | cons a word ih =>
      let d' : Data := {d with groupLeft := List.replicate word.length true, cursor := word ++ tail, dimLeft := List.replicate word.length true ++ dimRest, buffer := a::d.buffer}
      let s' : Control := {s with popped := some true, bit := a, available := true}
      have hpair : run 2 (frame (some (.groupStep c c)) s d) =
          frame (some (.groupStep c c)) s' d' := by
        apply match_pair c s d true a (List.replicate word.length true)
          (word ++ tail) (List.replicate word.length true ++ dimRest)
        · simpa [List.replicate_succ] using hg
        · simpa using hc
        · simpa [List.replicate_succ, List.cons_append] using hd
      obtain ⟨s'', hrest⟩ := ih s' d' rfl rfl rfl
      refine ⟨s'', ?_⟩
      have hrun := run_add hpair (2*word.length+1) |>.trans hrest
      have ht : 2*(a::word).length+1 = 2+(2*word.length+1) := by simp; omega
      rw [ht]
      simpa [d', List.reverse_cons, List.append_assoc] using hrun

theorem other_group (c j : Fin 6) (hneq : c ≠ j) (s : Control) (d : Data)
    (m : ℕ) (dimRest : List Bool)
    (hg : d.groupLeft = List.replicate m true)
    (hd : d.dimLeft = List.replicate m true ++ dimRest) :
    ∃ s', run (2*m+1) (frame (some (.groupStep c j)) s d) =
      frame (some (.startGroup c (next j))) s'
        {d with groupLeft := [], dimLeft := dimRest, buffer := List.replicate m false ++ d.buffer} := by
  induction m generalizing s d with
  | zero =>
      refine ⟨{s with popped := none}, ?_⟩
      have hs := groupStep_nil c j s d (by simpa only [List.replicate_zero] using hg)
      have heq : d = {d with groupLeft := [], dimLeft := dimRest, buffer := d.buffer} := by
        cases d <;> simp_all
      have hs' : advance program (frame (some (.groupStep c j)) s d) =
          frame (some (.startGroup c (next j))) {s with popped := none}
            {d with groupLeft := [], dimLeft := dimRest, buffer := d.buffer} := by
        rw [← heq]
        exact hs
      simpa only [Nat.mul_zero, Nat.zero_add, List.replicate_zero,
        List.nil_append, run_succ, run, Function.iterate_zero, id_eq] using hs'
  | succ m ih =>
      let d' : Data := {d with groupLeft := List.replicate m true, dimLeft := List.replicate m true ++ dimRest, buffer := false::d.buffer}
      let s' : Control := {s with popped := some true, available := true}
      have hpair : run 2 (frame (some (.groupStep c j)) s d) =
          frame (some (.groupStep c j)) s' d' := by
        apply other_pair c j hneq s d true (List.replicate m true)
          (List.replicate m true ++ dimRest)
        · simpa [List.replicate_succ] using hg
        · simpa [List.replicate_succ, List.cons_append] using hd
      obtain ⟨s'', hrest⟩ := ih s' d' rfl rfl
      refine ⟨s'', ?_⟩
      have hrun := run_add hpair (2*m+1) |>.trans hrest
      have ht : 2*(m+1)+1 = 2+(2*m+1) := by omega
      rw [ht]
      have hrotate (n : ℕ) (tail : List Bool) :
          List.replicate n false ++ false::tail =
            false::(List.replicate n false ++ tail) := by
        induction n with
        | zero => rfl
        | succ n ih => simpa [List.replicate_succ, List.append_assoc] using ih
      simpa [d', List.replicate_succ, hrotate, List.cons_append,
        List.append_assoc] using hrun

theorem start_group_match (c : Fin 6) (s : Control) (d : Data)
    (word tail dimRest : List Bool)
    (he : d.edges = List.replicate word.length true)
    (hg : d.groupLeft = []) (hs : d.scratch = [])
    (hc : d.cursor = word ++ tail)
    (hd : d.dimLeft = List.replicate word.length true ++ dimRest)
    (h5 : c ≠ 5) :
    ∃ s', run (4*word.length+4) (frame (some (.startGroup c c)) s d) =
      frame (some (.startGroup c (next c))) s'
        {d with cursor := tail, dimLeft := dimRest, buffer := word.reverse ++ d.buffer} := by
  have hstart := startGroup_more c c s d h5
  have hcopy := copy_run .edges c c s d hs
  have hdata : (d.addTarget .edges (d.get .edges)).groupLeft =
      List.replicate word.length true := by simp [Data.addTarget, Data.get, hg, he]
  obtain ⟨s', hgroup⟩ := match_group c {s with popped := none}
    (d.addTarget .edges (d.get .edges)) word tail dimRest hdata
    (by simpa [Data.addTarget, Data.get] using hc)
    (by simpa [Data.addTarget, Data.get] using hd)
  refine ⟨s', ?_⟩
  have hfirst : run (1+(2*word.length+2)) (frame (some (.startGroup c c)) s d) =
      frame (some (.groupStep c c)) {s with popped := none}
        (d.addTarget .edges (d.get .edges)) := by
    rw [run_add (by simpa [run_succ, run] using hstart) (2*word.length+2)]
    simpa [Data.get, he] using hcopy
  have hrun := run_add hfirst (2*word.length+1) |>.trans hgroup
  have ht : 4*word.length+4 = 1+(2*word.length+2)+(2*word.length+1) := by omega
  rw [ht]
  simpa [Data.get, Data.addTarget, hg, he] using hrun

theorem start_group_other (c j : Fin 6) (hneq : c ≠ j) (hj : j ≠ 5)
    (s : Control) (d : Data) (m : ℕ) (dimRest : List Bool)
    (he : d.edges = List.replicate m true)
    (hg : d.groupLeft = []) (hs : d.scratch = [])
    (hd : d.dimLeft = List.replicate m true ++ dimRest) :
    ∃ s', run (4*m+4) (frame (some (.startGroup c j)) s d) =
      frame (some (.startGroup c (next j))) s'
        {d with dimLeft := dimRest, buffer := List.replicate m false ++ d.buffer} := by
  have hstart := startGroup_more c j s d hj
  have hcopy := copy_run .edges c j s d hs
  have hdata : (d.addTarget .edges (d.get .edges)).groupLeft =
      List.replicate m true := by simp [Data.addTarget, Data.get, hg, he]
  obtain ⟨s', hgroup⟩ := other_group c j hneq {s with popped := none}
    (d.addTarget .edges (d.get .edges)) m dimRest hdata
    (by simpa [Data.addTarget, Data.get] using hd)
  refine ⟨s', ?_⟩
  have hfirst : run (1+(2*m+2)) (frame (some (.startGroup c j)) s d) =
      frame (some (.groupStep c j)) {s with popped := none}
        (d.addTarget .edges (d.get .edges)) := by
    rw [run_add (by simpa [run_succ, run] using hstart) (2*m+2)]
    simpa [Data.get, he] using hcopy
  have hrun := run_add hfirst (2*m+1) |>.trans hgroup
  have ht : 4*m+4 = 1+(2*m+2)+(2*m+1) := by omega
  rw [ht]
  simpa [Data.get, Data.addTarget, hg, he] using hrun

def cursorBefore (c j : Fin 6) (word tail : List Bool) : List Bool :=
  if j.val ≤ c.val then word ++ tail else tail

def block (c j : Fin 6) (word : List Bool) : List Bool :=
  if c = j then word else List.replicate word.length false

theorem next_val (j : Fin 6) (hj : j ≠ 5) : (next j).val = j.val+1 := by
  have h : j.val < 5 := by
    have := j.isLt
    by_contra hn
    have he : j.val = 5 := by omega
    exact hj (Fin.ext he)
  change min 5 (j.val+1) = j.val+1
  exact Nat.min_eq_right (by omega)

theorem cursor_after_other (c j : Fin 6) (hj : j ≠ 5) (hneq : c ≠ j)
    (word tail : List Bool) :
    cursorBefore c (next j) word tail = cursorBefore c j word tail := by
  unfold cursorBefore
  rw [next_val j hj]
  by_cases h : j.val ≤ c.val
  · have hlt : j.val < c.val := by
      have hne : j.val ≠ c.val := fun he => hneq (Fin.ext he.symm)
      omega
    simp only [h, ↓reduceIte]
    have : j.val+1 ≤ c.val := by omega
    simp [this]
  · have h' : ¬ j.val+1 ≤ c.val := by omega
    simp [h,h']

theorem cursor_after_match (c : Fin 6) (hc : c ≠ 5)
    (word tail : List Bool) :
    cursorBefore c c word tail = word ++ tail ∧
    cursorBefore c (next c) word tail = tail := by
  constructor
  · simp [cursorBefore]
  · simp [cursorBefore, next_val c hc]

theorem one_group (c j : Fin 6) (hj : j ≠ 5) (s : Control) (d : Data)
    (word tail dimRest : List Bool)
    (he : d.edges = List.replicate word.length true)
    (hg : d.groupLeft = []) (hs : d.scratch = [])
    (hc : d.cursor = cursorBefore c j word tail)
    (hd : d.dimLeft = List.replicate word.length true ++ dimRest) :
    ∃ s', run (4*word.length+4) (frame (some (.startGroup c j)) s d) =
      frame (some (.startGroup c (next j))) s'
        {d with cursor := cursorBefore c (next j) word tail, dimLeft := dimRest, buffer := (block c j word).reverse ++ d.buffer} := by
  by_cases hmatch : c = j
  · subst j
    obtain ⟨hcur,hnext⟩ := cursor_after_match c hj word tail
    obtain ⟨s',hr⟩ := start_group_match c s d word tail dimRest he hg hs
      (hc.trans hcur) hd hj
    refine ⟨s', ?_⟩
    simpa only [block, ↓reduceIte, hnext] using hr
  · have hcur := cursor_after_other c j hj hmatch word tail
    obtain ⟨s',hr⟩ := start_group_other c j hmatch hj s d word.length dimRest
      he hg hs hd
    refine ⟨s', ?_⟩
    simpa only [block, if_neg hmatch, List.reverse_replicate, hcur, hc] using hr

def fiveBlocks (c : Fin 6) (word : List Bool) : List Bool :=
  block c 0 word ++ block c 1 word ++ block c 2 word ++
    block c 3 word ++ block c 4 word

theorem five_groups (c : Fin 6) (hc5 : c ≠ 5) (s : Control) (d : Data)
    (word tail pad : List Bool)
    (he : d.edges = List.replicate word.length true)
    (hg : d.groupLeft = []) (hs : d.scratch = [])
    (hcur : d.cursor = word ++ tail)
    (hd : d.dimLeft = List.replicate (5*word.length) true ++ pad) :
    ∃ s', run (5*(4*word.length+4)+1) (frame (some (.startGroup c 0)) s d) =
      frame (some (.padding c)) s'
        {d with cursor := tail, dimLeft := pad, buffer := (fiveBlocks c word).reverse ++ d.buffer} := by
  let m := word.length
  let d₁ : Data := {d with cursor := cursorBefore c 1 word tail, dimLeft := List.replicate (4*m) true ++ pad, buffer := (block c 0 word).reverse ++ d.buffer}
  let d₂ : Data := {d₁ with cursor := cursorBefore c 2 word tail, dimLeft := List.replicate (3*m) true ++ pad, buffer := (block c 1 word).reverse ++ d₁.buffer}
  let d₃ : Data := {d₂ with cursor := cursorBefore c 3 word tail, dimLeft := List.replicate (2*m) true ++ pad, buffer := (block c 2 word).reverse ++ d₂.buffer}
  let d₄ : Data := {d₃ with cursor := cursorBefore c 4 word tail, dimLeft := List.replicate m true ++ pad, buffer := (block c 3 word).reverse ++ d₃.buffer}
  let d₅ : Data := {d₄ with cursor := cursorBefore c 5 word tail, dimLeft := pad, buffer := (block c 4 word).reverse ++ d₄.buffer}
  have hdim₀ : d.dimLeft = List.replicate m true ++ (List.replicate (4*m) true ++ pad) := by
    rw [hd]
    have hn : 5*m = m+4*m := by omega
    rw [hn, List.replicate_add, List.append_assoc]
  have hcur₀ : d.cursor = cursorBefore c 0 word tail := by
    simpa [cursorBefore] using hcur
  obtain ⟨s₁,h₁⟩ := one_group c 0 (by decide) s d word tail
    (List.replicate (4*m) true ++ pad) he hg hs hcur₀ hdim₀
  have hdim₁ : d₁.dimLeft = List.replicate m true ++ (List.replicate (3*m) true ++ pad) := by
    change List.replicate (4*m) true ++ pad = _
    have hn : 4*m = m+3*m := by omega
    rw [hn, List.replicate_add, List.append_assoc]
  obtain ⟨s₂,h₂⟩ := one_group c 1 (by decide) s₁ d₁ word tail
    (List.replicate (3*m) true ++ pad) (by simpa [d₁] using he)
    (by simpa [d₁] using hg) (by simpa [d₁] using hs) rfl hdim₁
  have hdim₂ : d₂.dimLeft = List.replicate m true ++ (List.replicate (2*m) true ++ pad) := by
    change List.replicate (3*m) true ++ pad = _
    have hn : 3*m = m+2*m := by omega
    rw [hn, List.replicate_add, List.append_assoc]
  obtain ⟨s₃,h₃⟩ := one_group c 2 (by decide) s₂ d₂ word tail
    (List.replicate (2*m) true ++ pad) (by simpa [d₂,d₁] using he)
    (by simpa [d₂,d₁] using hg) (by simpa [d₂,d₁] using hs) rfl hdim₂
  have hdim₃ : d₃.dimLeft = List.replicate m true ++ (List.replicate m true ++ pad) := by
    change List.replicate (2*m) true ++ pad = _
    have hn : 2*m = m+m := by omega
    rw [hn, List.replicate_add, List.append_assoc]
  obtain ⟨s₄,h₄⟩ := one_group c 3 (by decide) s₃ d₃ word tail
    (List.replicate m true ++ pad) (by simpa [d₃,d₂,d₁] using he)
    (by simpa [d₃,d₂,d₁] using hg) (by simpa [d₃,d₂,d₁] using hs) rfl hdim₃
  obtain ⟨s₅,h₅⟩ := one_group c 4 (by decide) s₄ d₄ word tail pad
    (by simpa [d₄,d₃,d₂,d₁] using he)
    (by simpa [d₄,d₃,d₂,d₁] using hg)
    (by simpa [d₄,d₃,d₂,d₁] using hs) rfl (by rfl)
  have hnext₀ : next (0 : Fin 6) = 1 := rfl
  have hnext₁ : next (1 : Fin 6) = 2 := rfl
  have hnext₂ : next (2 : Fin 6) = 3 := rfl
  have hnext₃ : next (3 : Fin 6) = 4 := rfl
  have hnext₄ : next (4 : Fin 6) = 5 := rfl
  have hstep₀ : run (4*m+4) (frame (some (.startGroup c 0)) s d) =
      frame (some (.startGroup c 1)) s₁ d₁ := by simpa [d₁,hnext₀,m] using h₁
  have hstep₁ : run (4*m+4) (frame (some (.startGroup c 1)) s₁ d₁) =
      frame (some (.startGroup c 2)) s₂ d₂ := by simpa [d₂,hnext₁,m] using h₂
  have hstep₂ : run (4*m+4) (frame (some (.startGroup c 2)) s₂ d₂) =
      frame (some (.startGroup c 3)) s₃ d₃ := by simpa [d₃,hnext₂,m] using h₃
  have hstep₃ : run (4*m+4) (frame (some (.startGroup c 3)) s₃ d₃) =
      frame (some (.startGroup c 4)) s₄ d₄ := by simpa [d₄,hnext₃,m] using h₄
  have hstep₄ : run (4*m+4) (frame (some (.startGroup c 4)) s₄ d₄) =
      frame (some (.startGroup c 5)) s₅ d₅ := by simpa [d₅,hnext₄,m] using h₅
  have hdone := startGroup_done c s₅ d₅
  refine ⟨s₅, ?_⟩
  have h01 := run_add hstep₀ (4*m+4) |>.trans hstep₁
  have h012 := run_add h01 (4*m+4) |>.trans hstep₂
  have h0123 := run_add h012 (4*m+4) |>.trans hstep₃
  have h01234 := run_add h0123 (4*m+4) |>.trans hstep₄
  have hrun := run_add h01234 1
  rw [show 5*(4*word.length+4)+1 =
      (4*m+4)+(4*m+4)+(4*m+4)+(4*m+4)+(4*m+4)+1 by omega]
  rw [hrun]
  change run 1 (frame (some (.startGroup c 5)) s₅ d₅) = _
  rw [run_succ 0, hdone]
  have hlt : c.val < 5 := by
    have := c.isLt
    by_contra hn
    have he : c.val = 5 := by omega
    exact hc5 (Fin.ext he)
  have hnot : ¬5 ≤ c.val := by omega
  simp [run, d₅, d₄, d₃, d₂, d₁, fiveBlocks, m,
    List.reverse_append, List.append_assoc, cursorBefore, hnot]

def rowContent (c : Fin 6) (word : List Bool) (pad : ℕ) : List Bool :=
  fiveBlocks c word ++ List.replicate pad false

theorem one_row (c : Fin 6) (hc5 : c ≠ 5) (s : Control) (d : Data)
    (word tail : List Bool) (rowsRest : List Bool) (pad : ℕ)
    (hr : d.rowsLeft = true::rowsRest)
    (he : d.edges = List.replicate word.length true)
    (hd : d.dimension = List.replicate (5*word.length+pad) true)
    (hc : d.cursor = word ++ tail)
    (hg : d.groupLeft = []) (hl : d.dimLeft = []) (hs : d.scratch = []) :
    ∃ s', run (1+(2*(5*word.length+pad)+2)+
        (5*(4*word.length+4)+1)+(pad+1))
      (frame (some (.startRow c)) s d) =
      frame (some (.startRow c)) s'
        {d with rowsLeft := rowsRest, cursor := tail, buffer := (rowContent c word pad).reverse ++ d.buffer} := by
  let d₁ : Data := {d with rowsLeft := rowsRest}
  have hstart := startRow_cons c s true rowsRest d hr
  have hcopy := copy_run .dimension c 0 {s with popped := some true} d₁
    (by simpa [d₁] using hs)
  let d₂ : Data := d₁.addTarget .dimension (d₁.get .dimension)
  have hdim₂ : d₂.dimLeft = List.replicate (5*word.length) true ++
      List.replicate pad true := by
    have hsplit : List.replicate (5*word.length+pad) true =
        List.replicate (5*word.length) true ++ List.replicate pad true := by
      rw [List.replicate_add]
    simpa [d₂, d₁, Data.addTarget, Data.get, hl, hd] using hsplit
  obtain ⟨s₂,hgroups⟩ := five_groups c hc5
    {s with popped := none} d₂ word tail (List.replicate pad true)
    (by simpa [d₂,d₁] using he)
    (by simpa [d₂,d₁] using hg)
    (by simpa [d₂,d₁] using hs)
    (by simpa [d₂,d₁] using hc) hdim₂
  let d₃ : Data := {d₂ with cursor := tail, dimLeft := List.replicate pad true, buffer := (fiveBlocks c word).reverse ++ d₂.buffer}
  have hpad := padding_run c s₂ d₃
  refine ⟨{s₂ with available := false}, ?_⟩
  have hfirst : run (1+(2*(5*word.length+pad)+2))
      (frame (some (.startRow c)) s d) =
      frame (some (.startGroup c 0)) {s with popped := none} d₂ := by
    rw [run_add (by simpa [run_succ, run] using hstart)
      (2*(5*word.length+pad)+2)]
    simpa [d₂, d₁, Data.get, hd] using hcopy
  have hsecond := run_add hfirst (5*(4*word.length+4)+1) |>.trans hgroups
  have hsecond' : run (1+(2*(5*word.length+pad)+2)+
      (5*(4*word.length+4)+1)) (frame (some (.startRow c)) s d) =
      frame (some (.padding c)) s₂ d₃ := by simpa [d₃] using hsecond
  have hthird := run_add hsecond' (pad+1)
  have hp : d₃.dimLeft.length = pad := by simp [d₃]
  rw [hp] at hpad
  rw [hthird, hpad]
  cases d
  simp only [Data.dimLeft] at hl
  rw [hl]
  simp [d₃, d₂, d₁, Data.addTarget, Data.get, rowContent,
    List.reverse_append, List.append_assoc]

def rowTime (m pad : ℕ) : ℕ :=
  1+(2*(5*m+pad)+2)+(5*(4*m+4)+1)+(pad+1)

theorem rows_run (c : Fin 6) (hc5 : c ≠ 5)
    (rows : List (List Bool)) (m pad : ℕ)
    (hrows : ∀ word ∈ rows, word.length = m)
    (s : Control) (d : Data)
    (hr : d.rowsLeft = List.replicate rows.length true)
    (he : d.edges = List.replicate m true)
    (hd : d.dimension = List.replicate (5*m+pad) true)
    (hc : d.cursor = rows.flatten)
    (hg : d.groupLeft = []) (hl : d.dimLeft = []) (hs : d.scratch = []) :
    ∃ s', run (rows.length*rowTime m pad+1)
      (frame (some (.startRow c)) s d) =
      frame (some (.startCopy (next c))) s'
        {d with rowsLeft := [], cursor := [], buffer := ((rows.map (fun word => rowContent c word pad)).flatten).reverse ++ d.buffer} := by
  induction rows generalizing s d with
  | nil =>
      refine ⟨{s with popped := none}, ?_⟩
      have hstep := startRow_nil c s d (by simpa using hr)
      have hdata : {d with rowsLeft := [], cursor := [], buffer := d.buffer} = d := by
        cases d
        simp_all
      simpa [run_succ, run, hdata] using hstep
  | cons word tail ih =>
      have hw : word.length = m := hrows word (by simp)
      have ht : ∀ w ∈ tail, w.length = m := by
        intro w h
        exact hrows w (by simp [h])
      let d₁ : Data := {d with rowsLeft := List.replicate tail.length true, cursor := tail.flatten, buffer := (rowContent c word pad).reverse ++ d.buffer}
      obtain ⟨s₁,hfirst⟩ := one_row c hc5 s d word tail.flatten
        (List.replicate tail.length true) pad
        (by simpa using hr)
        (by simpa [hw] using he)
        (by simpa [hw] using hd)
        (by simpa using hc) hg hl hs
      have hfirst' : run (rowTime m pad)
          (frame (some (.startRow c)) s d) =
          frame (some (.startRow c)) s₁ d₁ := by
        simpa [rowTime, hw, d₁] using hfirst
      obtain ⟨s₂,hsecond⟩ := ih ht s₁ d₁
        (by rfl) (by simpa [d₁] using he)
        (by simpa [d₁] using hd) (by rfl)
        (by simpa [d₁] using hg)
        (by simpa [d₁] using hl)
        (by simpa [d₁] using hs)
      refine ⟨s₂, ?_⟩
      have hjoin : ((List.map (fun w => rowContent c w pad) (word::tail)).flatten).reverse =
          ((tail.map (fun w => rowContent c w pad)).flatten).reverse ++
            (rowContent c word pad).reverse := by
        simp only [List.map_cons, List.flatten_cons, List.reverse_append]
      have htime : (word::tail).length*rowTime m pad+1 =
          rowTime m pad+(tail.length*rowTime m pad+1) := by
        simp [Nat.succ_mul, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]
      rw [htime, run_add hfirst' (tail.length*rowTime m pad+1), hsecond]
      rw [hjoin]
      simp only [d₁, List.append_assoc, List.nil_append]

def passTime (baseLength v m pad : ℕ) : ℕ :=
  1+(2*baseLength+2)+(2*v+2)+(v*rowTime m pad+1)

theorem one_pass (c : Fin 6) (hc5 : c ≠ 5)
    (rows : List (List Bool)) (m pad : ℕ)
    (hrows : ∀ word ∈ rows, word.length = m)
    (s : Control) (d : Data)
    (hb : d.base = rows.flatten)
    (hv : d.vertices = List.replicate rows.length true)
    (he : d.edges = List.replicate m true)
    (hd : d.dimension = List.replicate (5*m+pad) true)
    (hc : d.cursor = []) (hr : d.rowsLeft = [])
    (hg : d.groupLeft = []) (hl : d.dimLeft = []) (hs : d.scratch = []) :
    ∃ s', run (passTime d.base.length rows.length m pad)
      (frame (some (.startCopy c)) s d) =
      frame (some (.startCopy (next c))) s'
        {d with buffer := ((rows.map (fun word => rowContent c word pad)).flatten).reverse ++ d.buffer} := by
  let d₁ : Data := d.addTarget .base d.base
  let d₂ : Data := d₁.addTarget .vertices d₁.vertices
  have hstart : run 1 (frame (some (.startCopy c)) s d) =
      frame (some (.copyScan .base c 0)) s d := by
    simpa [run_succ, run] using startCopy_more c s d hc5
  have hbase := copy_run .base c 0 s d hs
  have hbase' : run (2*d.base.length+2) (frame (some (.copyScan .base c 0)) s d) =
      frame (some (.copyScan .vertices c 0)) {s with popped := none} d₁ := by
    simpa [d₁, Data.get, afterCopy] using hbase
  have hvertices := copy_run .vertices c 0 {s with popped := none} d₁
    (by simpa [d₁] using hs)
  have hvertices' : run (2*rows.length+2)
      (frame (some (.copyScan .vertices c 0)) {s with popped := none} d₁) =
      frame (some (.startRow c)) {s with popped := none} d₂ := by
    simpa [d₂, d₁, Data.get, Data.addTarget, afterCopy, hv] using hvertices
  obtain ⟨s₂,hrowsRun⟩ := rows_run c hc5 rows m pad hrows
    {s with popped := none} d₂
    (by simpa [d₂,d₁,Data.addTarget, hv, hr] using hv)
    (by simpa [d₂,d₁] using he)
    (by simpa [d₂,d₁] using hd)
    (by simpa [d₂,d₁,Data.addTarget, hb, hc] using hb)
    (by simpa [d₂,d₁] using hg)
    (by simpa [d₂,d₁] using hl)
    (by simpa [d₂,d₁] using hs)
  refine ⟨s₂, ?_⟩
  have hfirst := run_add hstart (2*d.base.length+2) |>.trans hbase'
  have hsecond := run_add hfirst (2*rows.length+2) |>.trans hvertices'
  have hthird := run_add hsecond (rows.length*rowTime m pad+1) |>.trans hrowsRun
  simpa [passTime, d₂, d₁, Data.addTarget, hc, hr] using hthird

def copyContent (c : Fin 6) (rows : List (List Bool)) (pad : ℕ) : List Bool :=
  (rows.map (fun word => rowContent c word pad)).flatten

def fiveContent (rows : List (List Bool)) (pad : ℕ) : List Bool :=
  copyContent 0 rows pad ++ copyContent 1 rows pad ++
  copyContent 2 rows pad ++ copyContent 3 rows pad ++
  copyContent 4 rows pad

theorem five_passes (rows : List (List Bool)) (m pad : ℕ)
    (hrows : ∀ word ∈ rows, word.length = m)
    (s : Control) (d : Data)
    (hb : d.base = rows.flatten)
    (hv : d.vertices = List.replicate rows.length true)
    (he : d.edges = List.replicate m true)
    (hd : d.dimension = List.replicate (5*m+pad) true)
    (hc : d.cursor = []) (hr : d.rowsLeft = [])
    (hg : d.groupLeft = []) (hl : d.dimLeft = []) (hs : d.scratch = []) :
    ∃ s', run (5*passTime d.base.length rows.length m pad)
      (frame (some (.startCopy 0)) s d) =
      frame (some (.startCopy 5)) s'
        {d with buffer := (fiveContent rows pad).reverse ++ d.buffer} := by
  let T := passTime d.base.length rows.length m pad
  have hpass (c : Fin 6) (h : c ≠ 5) (s₀ : Control) (buf : List Bool) :
      ∃ s₁, run T (frame (some (.startCopy c)) s₀ {d with buffer := buf}) =
        frame (some (.startCopy (next c))) s₁
          {d with buffer := (copyContent c rows pad).reverse ++ buf} := by
    have hh := one_pass c h rows m pad hrows s₀ {d with buffer := buf}
      (by simpa using hb) (by simpa using hv)
      (by simpa using he) (by simpa using hd)
      (by simpa using hc) (by simpa using hr)
      (by simpa using hg) (by simpa using hl)
      (by simpa using hs)
    simpa [T, copyContent] using hh
  obtain ⟨s₁,h₀⟩ := hpass 0 (by decide) s d.buffer
  obtain ⟨s₂,h₁⟩ := hpass 1 (by decide) s₁
    ((copyContent 0 rows pad).reverse ++ d.buffer)
  obtain ⟨s₃,h₂⟩ := hpass 2 (by decide) s₂
    ((copyContent 1 rows pad).reverse ++ (copyContent 0 rows pad).reverse ++ d.buffer)
  obtain ⟨s₄,h₃⟩ := hpass 3 (by decide) s₃
    ((copyContent 2 rows pad).reverse ++ (copyContent 1 rows pad).reverse ++
      (copyContent 0 rows pad).reverse ++ d.buffer)
  obtain ⟨s₅,h₄⟩ := hpass 4 (by decide) s₄
    ((copyContent 3 rows pad).reverse ++ (copyContent 2 rows pad).reverse ++
      (copyContent 1 rows pad).reverse ++ (copyContent 0 rows pad).reverse ++ d.buffer)
  refine ⟨s₅, ?_⟩
  have h₀' : run T (frame (some (.startCopy 0)) s d) =
      frame (some (.startCopy 1)) s₁
        {d with buffer := (copyContent 0 rows pad).reverse ++ d.buffer} := by
    simpa [T, next] using h₀
  have h₁' := run_add h₀' T |>.trans (by simpa [next, List.append_assoc] using h₁)
  have h₂' := run_add h₁' T |>.trans (by simpa [next, List.append_assoc] using h₂)
  have h₃' := run_add h₂' T |>.trans (by simpa [next, List.append_assoc] using h₃)
  have h₄' := run_add h₃' T |>.trans (by simpa [next, List.append_assoc] using h₄)
  have htime : T+T+T+T+T = 5*T := by omega
  rw [htime] at h₄'
  simpa [T, fiveContent, List.reverse_append, List.append_assoc] using h₄'

def expansionTime (rows : List (List Bool)) (m pad : ℕ) : ℕ :=
  5*passTime rows.flatten.length rows.length m pad + 1 +
    (fiveContent rows pad).length + 1

theorem expand_rows (rows : List (List Bool)) (m pad : ℕ)
    (hrows : ∀ word ∈ rows, word.length = m) :
    ∃ s, run (expansionTime rows m pad)
      (input rows.flatten rows.length m (5*m+pad)) =
      frame none s
        {base := rows.flatten, vertices := List.replicate rows.length true,
         edges := List.replicate m true,
         dimension := List.replicate (5*m+pad) true,
         output := fiveContent rows pad} := by
  let d : Data :=
    {base := rows.flatten, vertices := List.replicate rows.length true,
     edges := List.replicate m true,
     dimension := List.replicate (5*m+pad) true}
  obtain ⟨s,hpass⟩ := five_passes rows m pad hrows {} d
    (by rfl) (by rfl) (by rfl) (by rfl)
    (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
  have hstart : input rows.flatten rows.length m (5*m+pad) =
      frame (some (.startCopy 0)) {} d := by
    rfl
  have hnext : run 1 (frame (some (.startCopy 5)) s
      {d with buffer := (fiveContent rows pad).reverse}) =
      frame (some .reverse) s
        {d with buffer := (fiveContent rows pad).reverse} := by
    simpa [run_succ, run] using
      startCopy_done s {d with buffer := (fiveContent rows pad).reverse}
  have hreverse := reverse_run s
    {d with buffer := (fiveContent rows pad).reverse}
  have hlength : ((fiveContent rows pad).reverse).length =
      (fiveContent rows pad).length := List.length_reverse
  rw [hlength] at hreverse
  have hfirst : run (5*passTime rows.flatten.length rows.length m pad+1)
      (input rows.flatten rows.length m (5*m+pad)) =
      frame (some .reverse) s
        {d with buffer := (fiveContent rows pad).reverse} := by
    rw [hstart, run_add hpass 1]
    simpa [d] using hnext
  have hfinal := run_add hfirst ((fiveContent rows pad).length+1) |>.trans hreverse
  refine ⟨{s with popped := none}, ?_⟩
  simpa [expansionTime, d] using hfinal

end EthInapproximability.CurrentPaper.SourceGraphPayloadMachine.Expansion

namespace EthInapproximability.CurrentPaper.SourceGraphPayloadMachine

def incidenceRows (g : EncodedGraph.Graph) (hg : g.Valid) : List (List Bool) :=
  List.ofFn fun i : Fin g.vertices =>
    List.ofFn fun α : Fin g.edges.length =>
      decide (∃ j : Fin 2, i = EncodedGraph.endpoints g hg α j)

theorem incidenceRows_length (g : EncodedGraph.Graph) (hg : g.Valid) :
    (incidenceRows g hg).length = g.vertices := by simp [incidenceRows]

theorem incidenceRows_width (g : EncodedGraph.Graph) (hg : g.Valid) :
    ∀ word ∈ incidenceRows g hg, word.length = g.edges.length := by
  intro word hw
  simp only [incidenceRows, List.mem_ofFn] at hw
  obtain ⟨i,rfl⟩ := hw
  simp

theorem incidenceRows_flatten (g : EncodedGraph.Graph) (hg : g.Valid) :
    (incidenceRows g hg).flatten = BaseCell.baseBits g hg := by
  unfold incidenceRows BaseCell.baseBits MatrixMaterialization.rowMajor
  rw [List.ofFn_mul]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext i
  apply congrArg List.ofFn
  funext α
  have hidx : (⟨i.val * g.edges.length + α.val, by
      have hi := i.isLt
      have hα := α.isLt
      nlinarith⟩ : Fin (g.vertices * g.edges.length)) =
      finProdFinEquiv (i, α) := by
    apply Fin.ext
    simp [finProdFinEquiv_apply_val]
    ring
  simp [hidx]

theorem fiveBlocks_ofFn (c : Fin 6) (m : ℕ) (f : Fin m → Bool) :
    Expansion.fiveBlocks c (List.ofFn f) =
      (List.ofFn fun q : Fin 5 =>
        List.ofFn fun α : Fin m =>
          if c = Fin.castLE (by omega : 5 ≤ 6) q then f α else false).flatten := by
  simp only [Expansion.fiveBlocks, Expansion.block, List.length_ofFn]
  fin_cases c <;>
    simp [List.ofFn_succ, List.ofFn_zero, List.flatten_cons,
      List.flatten_nil, List.ofFn_const, List.append_assoc,
      Nat.add_assoc] <;>
    simp only [List.replicate_add, List.append_assoc]

theorem rowContent_ofFn (c : Fin 6) (m pad : ℕ) (f : Fin m → Bool) :
    Expansion.rowContent c (List.ofFn f) pad =
      (List.ofFn fun k : Fin (5*m) =>
        let q := finProdFinEquiv.symm k
        if c = Fin.castLE (by omega : 5 ≤ 6) q.1 then f q.2 else false) ++
      List.replicate pad false := by
  unfold Expansion.rowContent
  rw [fiveBlocks_ofFn]
  exact congrArg (fun bits : List Bool => bits ++ List.replicate pad false)
    (SamplerSeedEnumeration.ofFn_pair_labels
      (fun q : Fin 5 × Fin m =>
        if c = Fin.castLE (by omega : 5 ≤ 6) q.1 then f q.2 else false)).symm

theorem rowContent_source {v m : ℕ} (e : Fin m → Fin 2 → Fin v)
    (c : Fin 5) (i : Fin v) (pad : ℕ) :
    Expansion.rowContent (Fin.castLE (by omega : 5 ≤ 6) c)
      (List.ofFn fun α : Fin m => decide (∃ j : Fin 2, i = e α j)) pad =
    List.ofFn fun α : Fin (5*m+pad) =>
      ExactConstruction.sourceVectors (5*m+pad) e
        (finProdFinEquiv (c,i)) α := by
  rw [rowContent_ofFn, List.ofFn_add]
  congr 1
  · apply congrArg List.ofFn
    funext k
    have hcast : (Fin.castLE (by omega : 5*m ≤ 5*m+pad) k).val = k.val := rfl
    simp only [ExactConstruction.sourceVectors, ExactConstruction.padVectors,
      ExactConstruction.encodedFiveCopyVectors, ExactConstruction.fiveCopyVectors,
      Equiv.symm_apply_apply]
    have hk : k.val < 5*m := k.isLt
    simp [hcast, hk]
  · simp [ExactConstruction.sourceVectors, ExactConstruction.padVectors]

theorem copyContent_source (g : EncodedGraph.Graph) (hg : g.Valid)
    (c : Fin 5) (pad : ℕ) :
    Expansion.copyContent (Fin.castLE (by omega : 5 ≤ 6) c)
      (incidenceRows g hg) pad =
    MatrixMaterialization.rowMajor (fun i : Fin g.vertices =>
      fun α : Fin (5*g.edges.length+pad) =>
        ExactConstruction.sourceVectors (5*g.edges.length+pad)
          (EncodedGraph.endpoints g hg) (finProdFinEquiv (c,i)) α) := by
  let f : Fin g.vertices → Fin (5*g.edges.length+pad) → Bool :=
    fun i α => ExactConstruction.sourceVectors (5*g.edges.length+pad)
      (EncodedGraph.endpoints g hg) (finProdFinEquiv (c,i)) α
  calc
    Expansion.copyContent (Fin.castLE (by omega : 5 ≤ 6) c)
        (incidenceRows g hg) pad =
        (List.ofFn fun i : Fin g.vertices =>
          List.ofFn fun α : Fin (5*g.edges.length+pad) => f i α).flatten := by
      simp only [Expansion.copyContent, incidenceRows, List.map_ofFn,
        Function.comp_def]
      apply congrArg List.flatten
      apply congrArg List.ofFn
      funext i
      exact rowContent_source (EncodedGraph.endpoints g hg) c i pad
    _ = MatrixMaterialization.rowMajor f := by
      unfold MatrixMaterialization.rowMajor
      exact (SamplerSeedEnumeration.ofFn_pair_labels
        (fun p : Fin g.vertices × Fin (5*g.edges.length+pad) => f p.1 p.2)).symm

theorem fiveContent_ofFn (rows : List (List Bool)) (pad : ℕ) :
    Expansion.fiveContent rows pad =
      (List.ofFn fun c : Fin 5 =>
        Expansion.copyContent (Fin.castLE (by omega : 5 ≤ 6) c) rows pad).flatten := by
  simp [Expansion.fiveContent, List.ofFn_succ, List.ofFn_zero,
    List.flatten_cons, List.flatten_nil]

theorem fiveContent_exactBits (g : EncodedGraph.Graph) (hg : g.Valid)
    (pad : ℕ) :
    Expansion.fiveContent (incidenceRows g hg) pad =
      SourceGraphVectorPayload.exactBits g hg (5*g.edges.length+pad) := by
  let D := 5*g.edges.length+pad
  let f : Fin (5*g.vertices) → Fin D → Bool :=
    ExactConstruction.sourceVectors D (EncodedGraph.endpoints g hg)
  calc
    Expansion.fiveContent (incidenceRows g hg) pad =
        (List.ofFn fun c : Fin 5 =>
          Expansion.copyContent (Fin.castLE (by omega : 5 ≤ 6) c)
            (incidenceRows g hg) pad).flatten := fiveContent_ofFn _ _
    _ = (MatrixTableInterlaceRowReverse.blocksOf 5 g.vertices D f).flatten := by
      apply congrArg List.flatten
      apply congrArg List.ofFn
      funext c
      rw [copyContent_source]
      unfold MatrixMaterialization.rowMajor
      apply congrArg List.ofFn
      funext z
      simp only [f, D, MatrixTableInterlaceCodes.rowCode]
    _ = MatrixMaterialization.rowMajor f :=
      MatrixTableInterlaceRowReverse.blocksOf_flatten 5 g.vertices D f
    _ = SourceGraphVectorPayload.exactBits g hg D := rfl

theorem baseBits_length (g : EncodedGraph.Graph) (hg : g.Valid) :
    (BaseCell.baseBits g hg).length = g.vertices * g.edges.length := by
  simp [BaseCell.baseBits]

theorem fiveContent_length (g : EncodedGraph.Graph) (hg : g.Valid)
    (pad : ℕ) :
    (Expansion.fiveContent (incidenceRows g hg) pad).length =
      (5*g.vertices)*(5*g.edges.length+pad) := by
  rw [fiveContent_exactBits]
  exact SourceGraphVectorPayload.exactBits_length g hg _

theorem expand_graph (g : EncodedGraph.Graph) (hg : g.Valid)
    (pad : ℕ) :
    ∃ s, Expansion.run
      (Expansion.expansionTime (incidenceRows g hg) g.edges.length pad)
      (Expansion.input (BaseCell.baseBits g hg) g.vertices
        g.edges.length (5*g.edges.length+pad)) =
      Expansion.frame none s
        {base := BaseCell.baseBits g hg,
         vertices := List.replicate g.vertices true,
         edges := List.replicate g.edges.length true,
         dimension := List.replicate (5*g.edges.length+pad) true,
         output := SourceGraphVectorPayload.exactBits g hg (5*g.edges.length+pad)} := by
  obtain ⟨s,hs⟩ := Expansion.expand_rows (incidenceRows g hg)
    g.edges.length pad (incidenceRows_width g hg)
  refine ⟨s, ?_⟩
  simpa only [incidenceRows_length, incidenceRows_flatten,
    fiveContent_exactBits] using hs

end EthInapproximability.CurrentPaper.SourceGraphPayloadMachine
namespace EthInapproximability.CurrentPaper.SourceGraphPayloadMachine.Integrated

open Turing Turing.TM2.Stmt BitMachineEncoding BitMachineComposition BitMachineSubroutine

abbrev WriterStack := MatrixTableWriter.Stack 7
abbrev WriterLabel := MatrixTableWriter.Label BaseCell.Label
abbrev WriterControl := MatrixTableWriter.Control BaseCell.Control
abbrev ForeignStack := MatrixTableWriter.CellStack 7 ⊕ Fin 4
abbrev Stack := WriterStack ⊕ Fin 8
abbrev Label := WriterLabel ⊕ Expansion.Label
abbrev Control := WriterControl × Expansion.Control
abbrev Config := TM2.Cfg (fun _ : Stack => Bool) Label Control

def expansionSlots : Expansion.Stack ⊕ ForeignStack ≃ Stack where
  toFun
    | .inl 0 => .inl (.inr .output)
    | .inl 1 => .inl (.inr .rows)
    | .inl 2 => .inl (.inr .cols)
    | .inl 3 => .inr 0
    | .inl 4 => .inr 1
    | .inl 5 => .inr 2
    | .inl 6 => .inr 3
    | .inl 7 => .inr 4
    | .inl 8 => .inr 5
    | .inl 9 => .inr 6
    | .inl 10 => .inr 7
    | .inr (.inl k) => .inl (.inl k)
    | .inr (.inr 0) => .inl (.inr .rowsLeft)
    | .inr (.inr 1) => .inl (.inr .colsLeft)
    | .inr (.inr 2) => .inl (.inr .temp)
    | .inr (.inr 3) => .inl (.inr .buffer)
  invFun
    | .inl (.inl k) => .inr (.inl k)
    | .inl (.inr .rows) => .inl 1
    | .inl (.inr .cols) => .inl 2
    | .inl (.inr .rowsLeft) => .inr (.inr 0)
    | .inl (.inr .colsLeft) => .inr (.inr 1)
    | .inl (.inr .temp) => .inr (.inr 2)
    | .inl (.inr .buffer) => .inr (.inr 3)
    | .inl (.inr .output) => .inl 0
    | .inr 0 => .inl 3
    | .inr 1 => .inl 4
    | .inr 2 => .inl 5
    | .inr 3 => .inl 6
    | .inr 4 => .inl 7
    | .inr 5 => .inl 8
    | .inr 6 => .inl 9
    | .inr 7 => .inl 10
  left_inv := by
    intro k
    rcases k with k | (k | k)
    · fin_cases k <;> rfl
    · rfl
    · fin_cases k <;> rfl
  right_inv := by
    intro k
    rcases k with (k | k) | k
    · rfl
    · cases k <;> rfl
    · fin_cases k <;> rfl

def expansionLabels : Expansion.Label ⊕ WriterLabel ≃ Label where
  toFun := Sum.elim Sum.inr Sum.inl
  invFun := Sum.elim Sum.inr Sum.inl
  left_inv := by intro k; cases k <;> rfl
  right_inv := by intro k; cases k <;> rfl

def expansionControl : Expansion.Control × WriterControl ≃ Control where
  toFun := fun v => (v.2, v.1)
  invFun := fun v => (v.2, v.1)
  left_inv := by intro v; rfl
  right_inv := by intro v; rfl

def program : Label → TM2.Stmt (fun _ : Stack => Bool) Label Control
  | .inl l => liftStmt (some (.startCopy 0))
      (MatrixTableWriter.program BaseCell.program BaseCell.start BaseCell.initial l)
  | .inr l => renameStmt expansionSlots expansionLabels expansionControl
      (liftStmt none (Expansion.program l))

def run (t : ℕ) (c : Config) : Config := ((advance program)^[t]) c

def fresh (D : ℕ) : Fin 8 → List Bool :=
  fun k => if k = 0 then List.replicate D true else []

theorem run_add {c d : Config} {t : ℕ} (h : run t c = d) (u : ℕ) :
    run (t+u) c = run u d := by
  rw [Nat.add_comm t u]
  simp only [run, Function.iterate_add_apply] at h ⊢
  rw [h]

def writerStart (g : EncodedGraph.Graph) :
    MatrixTableWriter.Config 7 BaseCell.Label BaseCell.Control :=
  MatrixTableWriter.cfg (some (.inr (.copy .rows)))
    (BaseCell.initial, none)
    (MatrixTableWriter.ready
      (BaseCell.bank (SourceNormalizationMachineDecode.endpointStream g))
      g.vertices g.edges.length 0 0 0 0 [] [])

def writerEnd (g : EncodedGraph.Graph) (hg : g.Valid) (w : WriterControl) :
    MatrixTableWriter.Config 7 BaseCell.Label BaseCell.Control :=
  MatrixTableWriter.cfg none w
    (MatrixTableWriter.ready
      (BaseCell.bank (SourceNormalizationMachineDecode.endpointStream g))
      g.vertices g.edges.length 0 0 0 0 [] (BaseCell.baseBits g hg))

def input (g : EncodedGraph.Graph) (D : ℕ) : Config :=
  liftCfg (some (.startCopy 0)) ({} : Expansion.Control) (fresh D)
    (writerStart g)

theorem renameStmt_id (q : TM2.Stmt (fun _ : Stack => Bool) Label Control) :
    renameStmt (Equiv.refl Stack) (Equiv.refl Label) (Equiv.refl Control) q = q := by
  induction q with
  | push k f q ih => simp [renameStmt, ih]
  | peek k f q ih => simp [renameStmt, ih]
  | pop k f q ih => simp [renameStmt, ih]
  | load f q ih => simp [renameStmt, ih]
  | branch f q r ihq ihr => simp [renameStmt, ihq, ihr]
  | goto f => simp [renameStmt]
  | halt => rfl

theorem renameCfg_id (c : Config) :
    renameCfg (Equiv.refl Stack) (Equiv.refl Label) (Equiv.refl Control) c = c := by
  cases c
  simp [renameCfg]

theorem writer_stage (g : EncodedGraph.Graph) (hg : g.Valid) (D : ℕ) :
    ∃ t ≤ MatrixTableWriter.writerBound g.vertices g.edges.length
        (BaseCell.entryBound g.edges g.vertices), ∃ w : WriterControl,
      run t (input g D) =
        liftCfg (some (.startCopy 0)) ({} : Expansion.Control) (fresh D)
          (writerEnd g hg w) := by
  obtain ⟨t,ht,w,hw⟩ := BaseCell.write_base g hg []
  have hw' : MatrixTableWriter.run BaseCell.program BaseCell.start BaseCell.initial t
      (writerStart g) = writerEnd g hg w := by
    simpa [writerStart, writerEnd] using hw
  have hh : (MatrixTableWriter.run BaseCell.program BaseCell.start
      BaseCell.initial t (writerStart g)).l = none := by rw [hw']; rfl
  obtain ⟨n,hn,hmain⟩ :=
    BitMachineSubroutineRenaming.lift_outputs_renamed
      (Equiv.refl Stack) (Equiv.refl Label) (Equiv.refl Control)
      (MatrixTableWriter.program BaseCell.program BaseCell.start BaseCell.initial)
      program (some (.startCopy 0))
      (by intro l; simp [program, renameStmt_id])
      ({} : Expansion.Control) (fresh D) (writerStart g) t hh
  refine ⟨n, hn.trans ht, w, ?_⟩
  change ((advance (MatrixTableWriter.program BaseCell.program BaseCell.start
    BaseCell.initial))^[t]) (writerStart g) = writerEnd g hg w at hw'
  rw [hw'] at hmain
  simpa [run, input, renameCfg_id] using hmain

def writerFinalFrame (g : EncodedGraph.Graph) (hg : g.Valid)
    (D : ℕ) (w : WriterControl) : Config :=
  liftCfg (some (.startCopy 0)) ({} : Expansion.Control) (fresh D)
    (writerEnd g hg w)

def foreign (g : EncodedGraph.Graph) (hg : g.Valid)
    (D : ℕ) (w : WriterControl) : ForeignStack → List Bool :=
  fun k => (writerFinalFrame g hg D w).stk (expansionSlots (.inr k))

theorem finalFrame_as_expansion (g : EncodedGraph.Graph) (hg : g.Valid)
    (D : ℕ) (w : WriterControl) :
    writerFinalFrame g hg D w =
      renameCfg expansionSlots expansionLabels expansionControl
        (liftCfg none w (foreign g hg D w)
          (Expansion.input (BaseCell.baseBits g hg) g.vertices g.edges.length D)) := by
  unfold writerFinalFrame liftCfg renameCfg
  congr 1
  funext k
  cases k with
  | inl k =>
      cases k with
      | inl k =>
          cases k with
          | inl k => fin_cases k <;> simp [liftCfg, foreign, expansionSlots,
              writerEnd, MatrixTableWriter.cfg, MatrixTableWriter.Data.contents,
              MatrixTableWriter.Data.cell, MatrixTableWriter.Data.foreign,
              MatrixTableWriter.ready, BaseCell.bank, Expansion.input,
              Expansion.cfg, fresh, writerFinalFrame]
          | inr k => fin_cases k <;> simp [liftCfg, foreign, expansionSlots,
              writerEnd, MatrixTableWriter.cfg, MatrixTableWriter.Data.contents,
              MatrixTableWriter.Data.cell, MatrixTableWriter.Data.foreign,
              MatrixTableWriter.ready, BaseCell.bank, Expansion.input,
              Expansion.cfg, fresh, writerFinalFrame]
      | inr k => cases k <;> simp [liftCfg, foreign, expansionSlots,
          writerEnd, MatrixTableWriter.cfg, MatrixTableWriter.Data.contents,
          MatrixTableWriter.Data.cell, MatrixTableWriter.Data.foreign,
          MatrixTableWriter.ready, BaseCell.bank, Expansion.input,
          Expansion.cfg, fresh, writerFinalFrame]
  | inr k => fin_cases k <;> simp [liftCfg, foreign, expansionSlots,
      writerEnd, MatrixTableWriter.cfg, MatrixTableWriter.Data.contents,
      MatrixTableWriter.Data.cell, MatrixTableWriter.Data.foreign,
      MatrixTableWriter.ready, BaseCell.bank, Expansion.input,
      Expansion.cfg, fresh, writerFinalFrame]

theorem expansion_stage (g : EncodedGraph.Graph) (hg : g.Valid)
    (pad : ℕ) (w : WriterControl) :
    ∃ t ≤ Expansion.expansionTime (incidenceRows g hg) g.edges.length pad,
      ∃ s : Expansion.Control,
      run t (writerFinalFrame g hg (5*g.edges.length+pad) w) =
        renameCfg expansionSlots expansionLabels expansionControl
          (liftCfg none w (foreign g hg (5*g.edges.length+pad) w)
            (Expansion.frame none s
              {base := BaseCell.baseBits g hg,
               vertices := List.replicate g.vertices true,
               edges := List.replicate g.edges.length true,
               dimension := List.replicate (5*g.edges.length+pad) true,
               output := SourceGraphVectorPayload.exactBits g hg
                 (5*g.edges.length+pad)})) := by
  obtain ⟨s,hs⟩ := expand_graph g hg pad
  have hh : (Expansion.run
      (Expansion.expansionTime (incidenceRows g hg) g.edges.length pad)
      (Expansion.input (BaseCell.baseBits g hg) g.vertices g.edges.length
        (5*g.edges.length+pad))).l = none := by
    rw [hs]
    rfl
  obtain ⟨t,ht,hmain⟩ :=
    BitMachineSubroutineRenaming.lift_outputs_renamed
      expansionSlots expansionLabels expansionControl
      Expansion.program program none (by intro l; rfl)
      w (foreign g hg (5*g.edges.length+pad) w)
      (Expansion.input (BaseCell.baseBits g hg) g.vertices
        g.edges.length (5*g.edges.length+pad))
      (Expansion.expansionTime (incidenceRows g hg) g.edges.length pad) hh
  refine ⟨t,ht,s,?_⟩
  rw [finalFrame_as_expansion]
  change ((advance program)^[t]) _ = _
  change ((advance Expansion.program)^[Expansion.expansionTime
    (incidenceRows g hg) g.edges.length pad])
      (Expansion.input (BaseCell.baseBits g hg) g.vertices
        g.edges.length (5*g.edges.length+pad)) = _ at hs
  rw [hs] at hmain
  simpa [run] using hmain

theorem expansion_stage_source (g : EncodedGraph.Graph) (hg : g.Valid)
    (pad : ℕ) (w : WriterControl) :
    ∃ t ≤ Expansion.expansionTime (incidenceRows g hg) g.edges.length pad,
      (run t (writerFinalFrame g hg (5*g.edges.length+pad) w)).stk (.inr 7) =
        SourceGraphVectorPayload.exactBits g hg (5*g.edges.length+pad) := by
  obtain ⟨t,ht,s,hs⟩ := expansion_stage g hg pad w
  refine ⟨t,ht,?_⟩
  rw [hs]
  rfl

theorem write_source (g : EncodedGraph.Graph) (hg : g.Valid)
    (pad : ℕ) :
    ∃ t ≤ MatrixTableWriter.writerBound g.vertices g.edges.length
          (BaseCell.entryBound g.edges g.vertices) +
        Expansion.expansionTime (incidenceRows g hg) g.edges.length pad,
      ∃ w : WriterControl, ∃ s : Expansion.Control,
      run t (input g (5*g.edges.length+pad)) =
        renameCfg expansionSlots expansionLabels expansionControl
          (liftCfg none w (foreign g hg (5*g.edges.length+pad) w)
            (Expansion.frame none s
              {base := BaseCell.baseBits g hg,
               vertices := List.replicate g.vertices true,
               edges := List.replicate g.edges.length true,
               dimension := List.replicate (5*g.edges.length+pad) true,
               output := SourceGraphVectorPayload.exactBits g hg
                 (5*g.edges.length+pad)})) := by
  obtain ⟨tw,hw,w,hwriter⟩ := writer_stage g hg (5*g.edges.length+pad)
  obtain ⟨te,he,s,hexpand⟩ := expansion_stage g hg pad w
  refine ⟨tw+te, by omega, w, s, ?_⟩
  have hfirst : run tw (input g (5*g.edges.length+pad)) =
      writerFinalFrame g hg (5*g.edges.length+pad) w := hwriter
  exact (by rw [run_add hfirst te]; exact hexpand)

theorem write_source_cell (g : EncodedGraph.Graph) (hg : g.Valid)
    (pad : ℕ) :
    ∃ t ≤ MatrixTableWriter.writerBound g.vertices g.edges.length
          (BaseCell.entryBound g.edges g.vertices) +
        Expansion.expansionTime (incidenceRows g hg) g.edges.length pad,
      (run t (input g (5*g.edges.length+pad))).stk (.inr 7) =
        SourceGraphVectorPayload.exactBits g hg (5*g.edges.length+pad) := by
  obtain ⟨t,ht,w,s,hs⟩ := write_source g hg pad
  refine ⟨t,ht,?_⟩
  rw [hs]
  rfl

theorem expansionTime_polynomial (g : EncodedGraph.Graph) (hg : g.Valid)
    (pad : ℕ) :
    Expansion.expansionTime (incidenceRows g hg) g.edges.length pad ≤
      300*((EncodedGraph.encode g).length+5*g.edges.length+pad+1)^2 := by
  let v := g.vertices
  let m := g.edges.length
  let D := 5*m+pad
  let N := (EncodedGraph.encode g).length
  let Q := N+D+1
  have hsize := EncodedGraph.encode_length_lower g
  have hv : v ≤ Q := by dsimp [v,Q,N,D]; omega
  have hm : m ≤ Q := by dsimp [m,Q,N,D]; omega
  have hD : D ≤ Q := by dsimp [Q]; omega
  have hp : pad ≤ Q := by dsimp [Q,D]; omega
  have hQ : 1 ≤ Q := by dsimp [Q]; omega
  have hvm : v*m ≤ Q^2 := by
    have := Nat.mul_le_mul hv hm
    nlinarith
  have hvD : v*D ≤ Q^2 := by
    have := Nat.mul_le_mul hv hD
    nlinarith
  have hvp : v*pad ≤ Q^2 := by
    have := Nat.mul_le_mul hv hp
    nlinarith
  have hformula : Expansion.expansionTime (incidenceRows g hg) m pad =
      110*v*m+15*v*D+5*v*pad+135*v+32 := by
    simp only [Expansion.expansionTime, Expansion.passTime,
      Expansion.rowTime, incidenceRows_flatten, incidenceRows_length,
      baseBits_length, fiveContent_length]
    dsimp [v,m,D]
    ring
  rw [hformula]
  have hqsmall : Q ≤ Q^2 := by nlinarith
  have hQeq : Q = (EncodedGraph.encode g).length+5*g.edges.length+pad+1 := by
    dsimp [Q,N,D,m]
    omega
  rw [← hQeq]
  nlinarith

theorem writerTime_polynomial (g : EncodedGraph.Graph) (hg : g.Valid)
    (pad : ℕ) :
    MatrixTableWriter.writerBound g.vertices g.edges.length
      (BaseCell.entryBound g.edges g.vertices) ≤
      200*((EncodedGraph.encode g).length+5*g.edges.length+pad+1)^5 := by
  let v := g.vertices
  let m := g.edges.length
  let L := (endpointStream g.edges).length
  let B := BaseCell.entryBound g.edges g.vertices
  let Q := (EncodedGraph.encode g).length+5*m+pad+1
  have hsize := EncodedGraph.encode_length_lower g
  have hv : v ≤ Q := by dsimp [v,Q,m]; omega
  have hm : m ≤ Q := by dsimp [m,Q]; omega
  have hm1 : m+1 ≤ Q := by dsimp [m,Q]; omega
  have hq : 1 ≤ Q := by dsimp [Q]; omega
  have hs : L ≤ 2*m*(v+1) :=
    endpointStream_length_le g.edges g.vertices
      (fun p hp => ⟨(hg p hp).1, (hg p hp).2.1⟩)
  have hmul := Nat.mul_le_mul hm (Nat.add_le_add_right hv 1)
  have hL : L+1 ≤ 3*Q^2 := by nlinarith
  have hprod : (L+1)*(m+1) ≤ 3*Q^3 := by
    have hh := Nat.mul_le_mul hL hm1
    nlinarith
  have hq3 : Q ≤ Q^3 := by nlinarith
  have hB : B ≤ 100*Q^3 := by
    dsimp [B, BaseCell.entryBound]
    nlinarith
  have hvm : v*m ≤ Q^2 := by
    have hh := Nat.mul_le_mul hv hm
    nlinarith
  have hvmB : v*m*B ≤ 100*Q^5 := by
    have hh := Nat.mul_le_mul hvm hB
    nlinarith
  have hq2to5 : Q^2 ≤ Q^5 := by nlinarith
  have hqto5 : Q ≤ Q^5 := by nlinarith
  have hone5 : 1 ≤ Q^5 := by nlinarith
  have hformula : MatrixTableWriter.writerBound v m B =
      v*m*B+6*v*m+8*v+5 := by
    dsimp [MatrixTableWriter.writerBound]
    ring
  rw [hformula]
  have hQeq : Q = (EncodedGraph.encode g).length+5*g.edges.length+pad+1 := rfl
  rw [← hQeq]
  nlinarith

theorem write_source_polynomial (g : EncodedGraph.Graph) (hg : g.Valid)
    (D : ℕ) (hD : 5*g.edges.length ≤ D) :
    ∃ t ≤ 500*((EncodedGraph.encode g).length+D+1)^5,
      (run t (input g D)).stk (.inr 7) =
        SourceGraphVectorPayload.exactBits g hg D := by
  let pad := D-5*g.edges.length
  have hpad : 5*g.edges.length+pad = D := by dsimp [pad]; omega
  obtain ⟨t,ht,hs⟩ := write_source_cell g hg pad
  have hw := writerTime_polynomial g hg pad
  have he := expansionTime_polynomial g hg pad
  let Q := (EncodedGraph.encode g).length+D+1
  have hq : 1 ≤ Q := by dsimp [Q]; omega
  have hq2to5 : Q^2 ≤ Q^5 := Nat.pow_le_pow_right hq (by omega)
  have hqold : (EncodedGraph.encode g).length+5*g.edges.length+pad+1 = Q := by
    dsimp [Q]
    omega
  refine ⟨t, ?_, ?_⟩
  · rw [hqold] at hw he
    change t ≤ 500*Q^5
    change MatrixTableWriter.writerBound g.vertices g.edges.length
      (BaseCell.entryBound g.edges g.vertices) ≤ 200*Q^5 at hw
    change Expansion.expansionTime (incidenceRows g hg) g.edges.length pad ≤
      300*Q^2 at he
    nlinarith
  · simpa only [hpad] using hs

def final (g : EncodedGraph.Graph) (hg : g.Valid) (pad : ℕ)
    (w : WriterControl) (s : Expansion.Control) : Config :=
  renameCfg expansionSlots expansionLabels expansionControl
    (liftCfg none w (foreign g hg (5*g.edges.length+pad) w)
      (Expansion.frame none s
        {base := BaseCell.baseBits g hg,
         vertices := List.replicate g.vertices true,
         edges := List.replicate g.edges.length true,
         dimension := List.replicate (5*g.edges.length+pad) true,
         output := SourceGraphVectorPayload.exactBits g hg
           (5*g.edges.length+pad)}))

theorem write_source_final (g : EncodedGraph.Graph) (hg : g.Valid)
    (pad : ℕ) :
    ∃ t ≤ MatrixTableWriter.writerBound g.vertices g.edges.length
          (BaseCell.entryBound g.edges g.vertices) +
        Expansion.expansionTime (incidenceRows g hg) g.edges.length pad,
      ∃ w s, run t (input g (5*g.edges.length+pad)) = final g hg pad w s := by
  simpa only [final] using write_source g hg pad

theorem final_halt (g : EncodedGraph.Graph) (hg : g.Valid)
    (pad : ℕ) (w : WriterControl) (s : Expansion.Control) :
    (final g hg pad w s).l = none := rfl

theorem final_source (g : EncodedGraph.Graph) (hg : g.Valid)
    (pad : ℕ) (w : WriterControl) (s : Expansion.Control) :
    (final g hg pad w s).stk (.inr 7) =
      SourceGraphVectorPayload.exactBits g hg (5*g.edges.length+pad) := rfl

theorem final_vertices (g : EncodedGraph.Graph) (hg : g.Valid)
    (pad : ℕ) (w : WriterControl) (s : Expansion.Control) :
    (final g hg pad w s).stk (.inl (.inr .rows)) =
      List.replicate g.vertices true := rfl

theorem final_edges (g : EncodedGraph.Graph) (hg : g.Valid)
    (pad : ℕ) (w : WriterControl) (s : Expansion.Control) :
    (final g hg pad w s).stk (.inl (.inr .cols)) =
      List.replicate g.edges.length true := rfl

theorem final_dimension (g : EncodedGraph.Graph) (hg : g.Valid)
    (pad : ℕ) (w : WriterControl) (s : Expansion.Control) :
    (final g hg pad w s).stk (.inr 0) =
      List.replicate (5*g.edges.length+pad) true := rfl

theorem final_endpointStream (g : EncodedGraph.Graph) (hg : g.Valid)
    (pad : ℕ) (w : WriterControl) (s : Expansion.Control) :
    (final g hg pad w s).stk (.inl (.inl (.inl 0))) =
      SourceNormalizationMachineDecode.endpointStream g := rfl

theorem append_source
    {J K I L W V : Type*} [DecidableEq J] [DecidableEq K]
    (ek : Stack ⊕ J ≃ K) (el : Label ⊕ I ≃ L) (ev : Control × W ≃ V)
    (Q : L → TM2.Stmt (fun _ : K => Bool) L V) (halt : Option I)
    (hQ : ∀ l, Q (el (.inl l)) =
      renameStmt ek el ev (liftStmt halt (program l)))
    (foreignControl : W) (foreignBank : J → List Bool)
    (g : EncodedGraph.Graph) (hg : g.Valid) (pad : ℕ) :
    ∃ t ≤ MatrixTableWriter.writerBound g.vertices g.edges.length
          (BaseCell.entryBound g.edges g.vertices) +
        Expansion.expansionTime (incidenceRows g hg) g.edges.length pad,
      ∃ w s,
      ((advance Q)^[t])
          (renameCfg ek el ev
            (liftCfg halt foreignControl foreignBank
              (input g (5*g.edges.length+pad)))) =
        renameCfg ek el ev
          (liftCfg halt foreignControl foreignBank (final g hg pad w s)) := by
  obtain ⟨t,ht,w,s,hraw⟩ := write_source_final g hg pad
  have hh : (run t (input g (5*g.edges.length+pad))).l = none := by
    rw [hraw]
    exact final_halt g hg pad w s
  obtain ⟨n,hn,hmain⟩ :=
    BitMachineSubroutineRenaming.lift_outputs_renamed
      ek el ev program Q halt hQ foreignControl foreignBank
      (input g (5*g.edges.length+pad)) t hh
  refine ⟨n,hn.trans ht,w,s,?_⟩
  change ((advance program)^[t])
      (input g (5*g.edges.length+pad)) = final g hg pad w s at hraw
  rw [hraw] at hmain
  exact hmain

theorem append_source_polynomial
    {J K I L W V : Type*} [DecidableEq J] [DecidableEq K]
    (ek : Stack ⊕ J ≃ K) (el : Label ⊕ I ≃ L) (ev : Control × W ≃ V)
    (Q : L → TM2.Stmt (fun _ : K => Bool) L V) (halt : Option I)
    (hQ : ∀ l, Q (el (.inl l)) =
      renameStmt ek el ev (liftStmt halt (program l)))
    (foreignControl : W) (foreignBank : J → List Bool)
    (g : EncodedGraph.Graph) (hg : g.Valid) (pad : ℕ) :
    ∃ t ≤ 500*((EncodedGraph.encode g).length+5*g.edges.length+pad+1)^5,
      ∃ w s,
      ((advance Q)^[t])
          (renameCfg ek el ev
            (liftCfg halt foreignControl foreignBank
              (input g (5*g.edges.length+pad)))) =
        renameCfg ek el ev
          (liftCfg halt foreignControl foreignBank (final g hg pad w s)) := by
  obtain ⟨t,ht,w,s,hr⟩ := append_source ek el ev Q halt hQ
    foreignControl foreignBank g hg pad
  let Z := (EncodedGraph.encode g).length+5*g.edges.length+pad+1
  have hz : 1 ≤ Z := by dsimp [Z]; omega
  have hp := Nat.pow_le_pow_right hz (by omega : 2 ≤ 5)
  have hw := writerTime_polynomial g hg pad
  have he := expansionTime_polynomial g hg pad
  refine ⟨t, ?_, w, s, hr⟩
  dsimp [Z] at hp
  nlinarith

end EthInapproximability.CurrentPaper.SourceGraphPayloadMachine.Integrated
