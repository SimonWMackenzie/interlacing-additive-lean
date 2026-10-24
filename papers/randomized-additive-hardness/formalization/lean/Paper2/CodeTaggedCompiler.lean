import Paper2.GeneratorSource
import Paper2.GeneratorSerialization
import Paper2.CodeCopiesMachine
import Paper2.CodeConstructorMachine
import EthInapproximability.CurrentPaper.BitMachineEncoding

/-! One fixed physical transducer for the production tagged-code constructor. -/

namespace Paper2.TaggedCompiler

set_option maxHeartbeats 1000000
set_option maxRecDepth 8192

open Turing Turing.TM2.Stmt
open EthInapproximability.CurrentPaper.BitMachineEncoding
open Paper2.GeneratorCode Paper2.GeneratorSerialization Paper2.GeneratorSource

inductive Return where
  | third | fixed | raw
  deriving DecidableEq, Fintype

inductive CountPhase where
  | q | s | extra
  deriving DecidableEq, Fintype

inductive WorkMode where
  | fixed | raw | left
  deriving DecidableEq, Fintype

inductive Label where
  | outerInit (r : Return)
  | qScan (r : Return) | qRestore (r : Return)
  | sScan (r : Return) | sRestore (r : Return)
  | cCopy (r : Return) (p : CountPhase)
  | cRestore (r : Return) (p : CountPhase)
  | cTag (r : Return) (p : CountPhase)
  | q2Copy (r : Return) | q2Restore (r : Return)
  | outerFinish (r : Return)
  | child3Finish | fixedInit | fixedLoop | fixedTag | child2Finish
  | rawRightInit | rawOuterLoop | rawTag | rawRightDone
  | workCopy (m : WorkMode) | workRestore (m : WorkMode)
  | leftExtra | leftLoop | leftCopy | leftRestore | leftTag
  | child1Finish | branchFinish | accept | reject
  deriving DecidableEq, Fintype

abbrev Control := Option Bool

-- 0,1,2,3: preserved unary q₁, unary q₂, unary s, serialized c.
-- 4: working true-counter; 5: nested count scratch; 6: word-copy scratch;
-- 7: output.
def prepend (word : List Bool) (next : Label) :
    TM2.Stmt (fun _ : Fin 8 => Bool) Label Control :=
  word.foldl (fun stmt bit => push 7 (fun _ => bit) stmt)
    (goto (fun _ => next))

def copyWord (src : Fin 8) (copy restore : Label) :
    TM2.Stmt (fun _ : Fin 8 => Bool) Label Control :=
  pop src (fun _ b => b)
    (branch Option.isSome
      (push 6 (fun b => b.getD false) (goto (fun _ => copy)))
      (goto (fun _ => restore)))

def restoreWord (src : Fin 8) (restore next : Label) :
    TM2.Stmt (fun _ : Fin 8 => Bool) Label Control :=
  pop 6 (fun _ b => b)
    (branch Option.isSome
      (push src (fun b => b.getD false)
        (push 7 (fun b => b.getD false) (goto (fun _ => restore))))
      (goto (fun _ => next)))

def scanStmt (src : Fin 8) (copy restore : Label) :
    TM2.Stmt (fun _ : Fin 8 => Bool) Label Control :=
  pop src (fun _ b => b)
    (branch Option.isSome
      (branch (fun b => b.getD false)
        (push 5 (fun _ => true)
          (load (fun _ => none) (goto (fun _ => copy))))
        (push 5 (fun _ => false) (goto (fun _ => restore))))
      (goto (fun _ => .reject)))

def scanRestoreStmt (src : Fin 8) (restore next : Label) :
    TM2.Stmt (fun _ : Fin 8 => Bool) Label Control :=
  pop 5 (fun _ b => b)
    (branch Option.isSome
      (push src (fun b => b.getD false) (goto (fun _ => restore)))
      (goto (fun _ => next)))

def workLoopStmt (outer done : Label) :
    TM2.Stmt (fun _ : Fin 8 => Bool) Label Control :=
  pop 4 (fun _ b => b)
    (branch Option.isSome
      (load (fun _ => none) (goto (fun _ => outer)))
      (goto (fun _ => done)))

def afterOuter : Return → Label
  | .third => .child3Finish
  | .fixed => .fixedTag
  | .raw => .rawTag

def afterWork : WorkMode → Label
  | .fixed => .fixedLoop
  | .raw => .rawOuterLoop
  | .left => .leftExtra

def afterCTag (r : Return) : CountPhase → Label
  | .q => .qScan r
  | .s => .sScan r
  | .extra => .q2Copy r

def program : Label → TM2.Stmt (fun _ : Fin 8 => Bool) Label Control
  | .outerInit r => prepend (encodeCode (.emit [])) (.qScan r)
  | .qScan r => scanStmt 0 (.cCopy r .q) (.qRestore r)
  | .qRestore r => scanRestoreStmt 0 (.qRestore r) (.sScan r)
  | .sScan r => scanStmt 2 (.cCopy r .s) (.sRestore r)
  | .sRestore r => scanRestoreStmt 2 (.sRestore r) (.cCopy r .extra)
  | .cCopy r p => copyWord 3 (.cCopy r p) (.cRestore r p)
  | .cRestore r p => restoreWord 3 (.cRestore r p) (.cTag r p)
  | .cTag r p => prepend [false,true,true] (afterCTag r p)
  | .q2Copy r => copyWord 1 (.q2Copy r) (.q2Restore r)
  | .q2Restore r => restoreWord 1 (.q2Restore r) (.outerFinish r)
  | .outerFinish r => prepend
      ([false,true,true] ++ [false,false,true]) (afterOuter r)
  | .child3Finish => prepend
      ([false,true,true] ++ encodeCode (.emit [true,true])) .fixedInit
  | .fixedInit => prepend (encodeCode (.emit [])) (.workCopy .fixed)
  | .fixedLoop => workLoopStmt (.outerInit .fixed) .child2Finish
  | .fixedTag => prepend [false,true,true] .fixedLoop
  | .child2Finish => prepend
      ([false,true,true] ++ encodeCode (.emit [true,false])) .rawRightInit
  | .rawRightInit => prepend (encodeCode (.emit [])) (.workCopy .raw)
  | .rawOuterLoop => workLoopStmt (.outerInit .raw) .rawRightDone
  | .rawTag => prepend [false,true,true] .rawOuterLoop
  | .rawRightDone => prepend (encodeCode (.emit [])) (.workCopy .left)
  | .workCopy m =>
      pop 2 (fun _ b => b)
        (branch Option.isSome
          (push 5 (fun b => b.getD false) (goto (fun _ => .workCopy m)))
          (goto (fun _ => .workRestore m)))
  | .workRestore m =>
      pop 5 (fun _ b => b)
        (branch Option.isSome
          (push 2 (fun b => b.getD false)
            (branch (fun b => b.getD false)
              (push 4 (fun _ => true) (goto (fun _ => .workRestore m)))
              (goto (fun _ => .workRestore m))))
          (goto (fun _ => afterWork m)))
  | .leftExtra => push 4 (fun _ => true) (goto (fun _ => .leftLoop))
  | .leftLoop =>
      pop 4 (fun _ b => b)
        (branch Option.isSome
          (load (fun _ => none) (goto (fun _ => .leftCopy)))
          (goto (fun _ => .child1Finish)))
  | .leftCopy => copyWord 3 .leftCopy .leftRestore
  | .leftRestore => restoreWord 3 .leftRestore .leftTag
  | .leftTag => prepend [false,true,true] .leftLoop
  | .child1Finish => prepend
      ([false,true,true] ++ encodeCode (.emit [false]) ++ [false,true,true])
      .branchFinish
  | .branchFinish => prepend
      ([true,false,false] ++ unary 256 ++ unary 254 ++ unary 255) .accept
  | .accept => load (fun _ => none) halt
  | .reject => halt

def cfg (label : Option Label) (control : Control)
    (contents : Fin 8 → List Bool) :
    TM2.Cfg (fun _ : Fin 8 => Bool) Label Control :=
  ⟨label, control, contents⟩

def inputs (q₁ q₂ s : Nat) (c : Code) : Fin 8 → List Bool :=
  fun i => if i = 0 then unary q₁ else if i = 1 then unary q₂ else
    if i = 2 then unary s else if i = 3 then encodeCode c else []

def run (steps : Nat) (c : TM2.Cfg (fun _ : Fin 8 => Bool) Label Control) :=
  ((advance program)^[steps]) c

private theorem run_succ {a b : TM2.Cfg (fun _ : Fin 8 => Bool) Label Control}
    (h : TM2.step program a = some b) (n : Nat) :
    run (n + 1) a = run n b := by
  simp only [run, Function.iterate_succ_apply, advance, h, Option.getD_some]

private theorem run_add (a b : Nat)
    (c : TM2.Cfg (fun _ : Fin 8 => Bool) Label Control) :
    run (a + b) c = run b (run a c) := by
  rw [Nat.add_comm a b]
  simp only [run, Function.iterate_add_apply]

private theorem run_cons {a b : TM2.Cfg (fun _ : Fin 8 => Bool) Label Control}
    (h : TM2.step program a = some b) (n : Nat) :
    run (1 + n) a = run n b := by
  rw [run_add, run_succ h 0]
  rfl

private theorem update_twice (S : Fin 8 → List Bool) (i : Fin 8)
    (a b : List Bool) :
    Function.update (Function.update S i a) i b =
      Function.update S i b := by
  funext j
  by_cases h : j = i <;> simp [Function.update, h]

private theorem update_twice6 (S : Fin 6 → List Bool) (i : Fin 6)
    (a b : List Bool) :
    Function.update (Function.update S i a) i b =
      Function.update S i b := by
  funext j
  by_cases h : j = i <;> simp [Function.update, h]

private theorem update_comm6 (S : Fin 6 → List Bool) (i j : Fin 6)
    (hi : i ≠ j) (a b : List Bool) :
    Function.update (Function.update S i a) j b =
      Function.update (Function.update S j b) i a := by
  funext k
  by_cases hki : k = i <;> by_cases hkj : k = j <;>
    simp_all [Function.update]

private theorem update_comm (S : Fin 8 → List Bool) (i j : Fin 8)
    (hi : i ≠ j) (a b : List Bool) :
    Function.update (Function.update S i a) j b =
      Function.update (Function.update S j b) i a := by
  funext k
  by_cases hki : k = i <;> by_cases hkj : k = j <;>
    simp_all [Function.update]

private theorem stepAux_prepend (word : List Bool)
    (stmt : TM2.Stmt (fun _ : Fin 8 => Bool) Label Control)
    (v : Control) (S : Fin 8 → List Bool) :
    TM2.stepAux
      (word.foldl (fun stmt bit => push 7 (fun _ => bit) stmt) stmt) v S =
    TM2.stepAux stmt v (Function.update S 7 (word ++ S 7)) := by
  induction word generalizing stmt S with
  | nil =>
      simp [Function.update_eq_self]
  | cons bit word ih =>
      simp only [List.foldl_cons]
      rw [ih]
      simp only [TM2.stepAux, Function.update_self, update_twice,
        List.cons_append]

theorem step_prepend (label next : Label) (word : List Bool)
    (h : program label = prepend word next)
    (v : Control) (S : Fin 8 → List Bool) :
    TM2.step program (cfg (some label) v S) =
      some (cfg (some next) v
        (Function.update S 7 (word ++ S 7))) := by
  simp only [TM2.step, cfg, h, prepend]
  rw [stepAux_prepend]
  simp [TM2.stepAux]

def sourceStack (i : Fin 6) : Fin 8 := ⟨i.val, by omega⟩

def contents (words : Fin 6 → List Bool) (output scratch : List Bool) :
    Fin 8 → List Bool :=
  fun i => if h : i.val < 6 then words ⟨i.val, h⟩ else
    if i.val = 6 then scratch else output

def wc (label : Option Label) (control : Control)
    (words : Fin 6 → List Bool) (output scratch : List Bool) :
    TM2.Cfg (fun _ : Fin 8 => Bool) Label Control :=
  cfg label control (contents words output scratch)

private theorem step_copy_cons (src : Fin 6) (copy restore : Label)
    (h : program copy = copyWord (sourceStack src) copy restore)
    (bit : Bool) (v : Control) (words : Fin 6 → List Bool)
    (output scratch : List Bool) :
    TM2.step program
      (wc (some copy) v (Function.update words src (bit :: words src))
        output scratch) =
    some (wc (some copy) (some bit) words output (bit :: scratch)) := by
  fin_cases src <;>
    simp [TM2.step, TM2.stepAux, h, copyWord, wc, cfg, contents,
      sourceStack, Function.update]
    <;> try { funext i; fin_cases i <;> simp [contents, Function.update] }

private theorem step_copy_nil (src : Fin 6) (copy restore : Label)
    (h : program copy = copyWord (sourceStack src) copy restore)
    (v : Control) (words : Fin 6 → List Bool)
    (output scratch : List Bool) :
    TM2.step program
      (wc (some copy) v (Function.update words src []) output scratch) =
    some (wc (some restore) none
      (Function.update words src []) output scratch) := by
  fin_cases src <;>
    simp [TM2.step, TM2.stepAux, h, copyWord, wc, cfg, contents,
      sourceStack, Function.update]

private theorem step_restore_cons (src : Fin 6) (restore next : Label)
    (h : program restore = restoreWord (sourceStack src) restore next)
    (bit : Bool) (v : Control) (words : Fin 6 → List Bool)
    (output scratch : List Bool) :
    TM2.step program (wc (some restore) v words output (bit :: scratch)) =
    some (wc (some restore) (some bit)
      (Function.update words src (bit :: words src)) (bit :: output) scratch) := by
  fin_cases src <;>
    simp [TM2.step, TM2.stepAux, h, restoreWord, wc, cfg, contents,
      sourceStack, Function.update]
    <;> try { funext i; fin_cases i <;> simp [contents, Function.update] }

private theorem step_restore_nil (src : Fin 6) (restore next : Label)
    (h : program restore = restoreWord (sourceStack src) restore next)
    (v : Control) (words : Fin 6 → List Bool) (output : List Bool) :
    TM2.step program (wc (some restore) v words output []) =
    some (wc (some next) none words output []) := by
  simp [TM2.step, TM2.stepAux, h, restoreWord, wc, cfg, contents]

theorem run_copy (src : Fin 6) (copy restore : Label)
    (h : program copy = copyWord (sourceStack src) copy restore)
    (bits : List Bool) (v : Control) (words : Fin 6 → List Bool)
    (output scratch : List Bool) :
    run (bits.length + 1)
      (wc (some copy) v (Function.update words src bits) output scratch) =
    wc (some restore) none (Function.update words src [])
      output (bits.reverse ++ scratch) := by
  induction bits generalizing words output scratch v with
  | nil =>
      simpa only [List.length_nil, zero_add, List.reverse_nil, List.nil_append] using
        run_succ (step_copy_nil src copy restore h v words output scratch) 0
  | cons bit bits ih =>
      rw [show (bit :: bits).length + 1 = (bits.length + 1) + 1 by simp]
      have hs := step_copy_cons src copy restore h bit v
        (Function.update words src bits) output scratch
      simp only [Function.update_self, update_twice6] at hs
      rw [run_succ hs (bits.length + 1)]
      simpa only [update_twice6, List.reverse_cons,
        List.append_assoc, List.singleton_append] using
        ih (some bit) (Function.update words src bits) output (bit :: scratch)

theorem run_restore (src : Fin 6) (restore next : Label)
    (h : program restore = restoreWord (sourceStack src) restore next)
    (bits : List Bool) (v : Control) (words : Fin 6 → List Bool)
    (output : List Bool) :
    run (bits.length + 1) (wc (some restore) v words output bits) =
    wc (some next) none
      (Function.update words src (bits.reverse ++ words src))
      (bits.reverse ++ output) [] := by
  induction bits generalizing words output v with
  | nil =>
      simpa only [List.length_nil, zero_add, List.reverse_nil, List.nil_append,
        Function.update_eq_self] using
        run_succ (step_restore_nil src restore next h v words output) 0
  | cons bit bits ih =>
      rw [show (bit :: bits).length + 1 = (bits.length + 1) + 1 by simp]
      rw [run_succ (step_restore_cons src restore next h bit v
        words output bits) (bits.length + 1)]
      simpa only [Function.update_self, update_twice6,
        List.reverse_cons, List.append_assoc, List.singleton_append] using
        ih (some bit) (Function.update words src (bit :: words src)) (bit :: output)

theorem run_word_phase (src : Fin 6) (copy restore next : Label)
    (hc : program copy = copyWord (sourceStack src) copy restore)
    (hr : program restore = restoreWord (sourceStack src) restore next)
    (words : Fin 6 → List Bool) (output : List Bool) :
    run (2 * (words src).length + 2)
      (wc (some copy) none words output []) =
    wc (some next) none words (words src ++ output) [] := by
  let bits := words src
  have hcopy := run_copy src copy restore hc bits none words output []
  have hrestore := run_restore src restore next hr bits.reverse none
    (Function.update words src []) output
  calc
    run (2 * bits.length + 2) (wc (some copy) none words output []) =
        run ((bits.length + 1) + (bits.length + 1))
          (wc (some copy) none (Function.update words src bits) output []) := by
            simp only [bits, Function.update_eq_self]; congr 1; omega
    _ = run (bits.length + 1)
          (wc (some restore) none (Function.update words src []) output bits.reverse) := by
            rw [run_add, hcopy, List.append_nil]
    _ = wc (some next) none words (bits ++ output) [] := by
            simpa only [bits, List.length_reverse, List.reverse_reverse,
              Function.update_self, update_twice6,
              List.append_nil, Function.update_eq_self] using hrestore

theorem step_prepend_wc (label next : Label) (word : List Bool)
    (h : program label = prepend word next)
    (v : Control) (words : Fin 6 → List Bool)
    (output scratch : List Bool) :
    TM2.step program (wc (some label) v words output scratch) =
    some (wc (some next) v words (word ++ output) scratch) := by
  rw [show wc (some label) v words output scratch =
    cfg (some label) v (contents words output scratch) by rfl]
  rw [step_prepend label next word h]
  congr 1
  simp only [wc, cfg]
  congr 1
  funext i
  fin_cases i <;> simp [contents, Function.update]

theorem run_c_block (r : Return) (p : CountPhase)
    (words : Fin 6 → List Bool) (output : List Bool) :
    run (2 * (words 3).length + 3)
      (wc (some (.cCopy r p)) none words output []) =
    wc (some (afterCTag r p)) none words
      (([false,true,true] ++ words 3) ++ output) [] := by
  have hc := run_word_phase 3 (.cCopy r p) (.cRestore r p) (.cTag r p)
    rfl rfl words output
  have ht := step_prepend_wc (.cTag r p) (afterCTag r p)
    [false,true,true] rfl none words (words 3 ++ output) []
  calc
    run (2 * (words 3).length + 3)
        (wc (some (.cCopy r p)) none words output []) =
      run ((2 * (words 3).length + 2) + 1)
        (wc (some (.cCopy r p)) none words output []) := by congr 1
    _ = run 1 (wc (some (.cTag r p)) none words (words 3 ++ output) []) := by
      rw [run_add, hc]
    _ = wc (some (afterCTag r p)) none words
          (([false,true,true] ++ words 3) ++ output) [] := by
      rw [run_succ ht 0]
      simp [run]

def smallStack (i : Fin 3) : Fin 6 := ⟨i.val, by omega⟩

private theorem step_scan_true (src : Fin 3) (scan copy restore : Label)
    (h : program scan = scanStmt (sourceStack (smallStack src)) copy restore)
    (v : Control) (words : Fin 6 → List Bool)
    (output scratch : List Bool) :
    TM2.step program
      (wc (some scan) v
        (Function.update words (smallStack src)
          (true :: words (smallStack src))) output scratch) =
    some (wc (some copy) none
      (Function.update words 5 (true :: words 5)) output scratch) := by
  fin_cases src <;>
    simp [TM2.step, TM2.stepAux, h, scanStmt, wc, cfg, contents,
      sourceStack, smallStack, Function.update]
    <;> try { funext i; fin_cases i <;> simp [contents, Function.update] }

private theorem step_scan_false (src : Fin 3) (scan copy restore : Label)
    (h : program scan = scanStmt (sourceStack (smallStack src)) copy restore)
    (v : Control) (words : Fin 6 → List Bool)
    (output scratch : List Bool) :
    TM2.step program
      (wc (some scan) v
        (Function.update words (smallStack src) [false]) output scratch) =
    some (wc (some restore) (some false)
      (Function.update
        (Function.update words (smallStack src) []) 5
        (false :: words 5)) output scratch) := by
  fin_cases src <;>
    simp [TM2.step, TM2.stepAux, h, scanStmt, wc, cfg, contents,
      sourceStack, smallStack, Function.update]
    <;> try { funext i; fin_cases i <;> simp [contents, Function.update] }

private theorem step_scan_restore_cons (src : Fin 3) (restore next : Label)
    (h : program restore =
      scanRestoreStmt (sourceStack (smallStack src)) restore next)
    (bit : Bool) (v : Control) (words : Fin 6 → List Bool)
    (output scratch : List Bool) :
    TM2.step program
      (wc (some restore) v
        (Function.update words 5 (bit :: words 5)) output scratch) =
    some (wc (some restore) (some bit)
      (Function.update words (smallStack src)
        (bit :: words (smallStack src))) output scratch) := by
  fin_cases src <;>
    simp [TM2.step, TM2.stepAux, h, scanRestoreStmt, wc, cfg, contents,
      sourceStack, smallStack, Function.update]
    <;> try { funext i; fin_cases i <;> simp [contents, Function.update] }

private theorem step_scan_restore_nil (src : Fin 3) (restore next : Label)
    (h : program restore =
      scanRestoreStmt (sourceStack (smallStack src)) restore next)
    (v : Control) (words : Fin 6 → List Bool)
    (output scratch : List Bool) :
    TM2.step program
      (wc (some restore) v (Function.update words 5 []) output scratch) =
    some (wc (some next) none (Function.update words 5 []) output scratch) := by
  fin_cases src <;>
    simp [TM2.step, TM2.stepAux, h, scanRestoreStmt, wc, cfg, contents,
      sourceStack, smallStack, Function.update]

theorem run_scan_restore (src : Fin 3) (restore next : Label)
    (h : program restore =
      scanRestoreStmt (sourceStack (smallStack src)) restore next)
    (bits : List Bool) (v : Control) (words : Fin 6 → List Bool)
    (output scratch : List Bool) :
    run (bits.length + 1)
      (wc (some restore) v (Function.update words 5 bits) output scratch) =
    wc (some next) none
      (Function.update
        (Function.update words 5 []) (smallStack src)
        (bits.reverse ++ words (smallStack src))) output scratch := by
  induction bits generalizing words output scratch v with
  | nil =>
      have hne : smallStack src ≠ (5 : Fin 6) := by fin_cases src <;> decide
      have hv : (Function.update words 5 []) (smallStack src) =
          words (smallStack src) := by simp [Function.update, hne]
      simpa only [List.length_nil, zero_add, List.reverse_nil, List.nil_append,
        ← hv, Function.update_eq_self, run, Function.iterate_zero, id_eq] using
        run_succ (step_scan_restore_nil src restore next h v words output scratch) 0
  | cons bit bits ih =>
      rw [show (bit :: bits).length + 1 = (bits.length + 1) + 1 by simp]
      have hs := step_scan_restore_cons src restore next h bit v
        (Function.update words 5 bits) output scratch
      simp only [Function.update_self, update_twice6] at hs
      rw [run_succ hs (bits.length + 1)]
      have hne : smallStack src ≠ (5 : Fin 6) := by
        fin_cases src <;> decide
      have hi := ih (some bit)
        (Function.update words (smallStack src)
          (bit :: words (smallStack src))) output scratch
      rw [update_comm6 words (smallStack src) 5 hne
        (bit :: words (smallStack src)) bits] at hi
      rw [update_comm6 words (smallStack src) 5 hne
        (bit :: words (smallStack src)) []] at hi
      simp only [update_twice6] at hi
      simpa [Function.update, hne, List.reverse_cons,
        List.append_assoc, List.singleton_append] using hi

def block (word : List Bool) : List Bool := [false,true,true] ++ word

private theorem replicate_true_rotate (n : Nat) (xs : List Bool) :
    List.replicate n true ++ true :: xs =
      true :: (List.replicate n true ++ xs) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, ih]

private theorem update_three (src : Fin 3) (words : Fin 6 → List Bool)
    (source scan : List Bool) :
    (Function.update
      (Function.update words (smallStack src) source) 5 scan) 3 = words 3 := by
  fin_cases src <;> simp [Function.update, smallStack]

theorem run_scan_repetitions (src : Fin 3) (r : Return)
    (p : CountPhase) (scan restore : Label)
    (hs : program scan = scanStmt (sourceStack (smallStack src))
      (.cCopy r p) restore)
    (hn : afterCTag r p = scan)
    (n : Nat) (tail scanned output : List Bool)
    (words : Fin 6 → List Bool) :
    run (n * (2 * (words 3).length + 4))
      (wc (some scan) none
        (Function.update
          (Function.update words (smallStack src)
            (List.replicate n true ++ tail)) 5 scanned)
        output []) =
    wc (some scan) none
      (Function.update
        (Function.update words (smallStack src) tail) 5
        (List.replicate n true ++ scanned))
      (CodeCopiesMachine.repeatPrefix n (words 3) ++ output) [] := by
  induction n generalizing scanned output with
  | zero => simp [run, CodeCopiesMachine.repeatPrefix]
  | succ n ih =>
      let restWords : Fin 6 → List Bool :=
        Function.update
          (Function.update words (smallStack src)
            (List.replicate n true ++ tail)) 5 scanned
      have hstep := step_scan_true src scan (.cCopy r p) restore hs none restWords
        output []
      have hsrc : restWords (smallStack src) =
          List.replicate n true ++ tail := by
        simp [restWords, Function.update, smallStack]
        fin_cases src <;> simp [Function.update]
      have hscan : restWords 5 = scanned := by
        simp [restWords, Function.update]
      have hword : restWords 3 = words 3 := by
        exact update_three src words (List.replicate n true ++ tail) scanned
      have hblock := run_c_block r p
        (Function.update restWords 5 (true :: scanned)) output
      have hword' :
          (Function.update restWords 5 (true :: scanned)) 3 = words 3 := by
        simpa [Function.update] using hword
      rw [hword'] at hblock
      have hne : smallStack src ≠ (5 : Fin 6) := by
        fin_cases src <;> decide
      have hstate :
          Function.update
            (Function.update words (smallStack src)
              (true :: (List.replicate n true ++ tail))) 5 scanned =
          Function.update restWords (smallStack src)
            (true :: restWords (smallStack src)) := by
        rw [hsrc]
        simp only [restWords]
        rw [update_comm6
          (Function.update words (smallStack src)
            (List.replicate n true ++ tail)) 5 (smallStack src)
          (Ne.symm hne) scanned (true :: (List.replicate n true ++ tail))]
        rw [update_twice6]
      calc
        run ((n + 1) * (2 * (words 3).length + 4))
            (wc (some scan) none
              (Function.update
                (Function.update words (smallStack src)
                  (List.replicate (n + 1) true ++ tail)) 5 scanned)
              output []) =
          run (1 + ((2 * (words 3).length + 3) +
            n * (2 * (words 3).length + 4)))
            (wc (some scan) none
              (Function.update restWords (smallStack src)
                (true :: restWords (smallStack src))) output []) := by
              congr 1
              · simp only [Nat.succ_mul]; omega
              · simpa only [List.replicate_succ, List.cons_append] using
                  congrArg (fun S => wc (some scan) none S output []) hstate
        _ = run ((2 * (words 3).length + 3) +
            n * (2 * (words 3).length + 4))
            (wc (some (.cCopy r p)) none
              (Function.update restWords 5 (true :: scanned)) output []) := by
              rw [run_add, run_succ hstep 0]
              simp [run, hscan]
        _ = run (n * (2 * (words 3).length + 4))
            (wc (some scan) none
              (Function.update restWords 5 (true :: scanned))
              (block (words 3) ++ output) []) := by
              rw [run_add]
              simpa [hn, block, List.append_assoc] using
                congrArg (run (n * (2 * (words 3).length + 4))) hblock
        _ = wc (some scan) none
            (Function.update
              (Function.update words (smallStack src) tail) 5
                (List.replicate (n + 1) true ++ scanned))
            (CodeCopiesMachine.repeatPrefix (n + 1) (words 3) ++ output) [] := by
              have hi := ih (true :: scanned) (block (words 3) ++ output)
              simp only [restWords, update_twice6] at hi ⊢
              rw [hi]
              congr 1
              · congr 1
                simp [List.replicate_add, List.append_assoc]
              · simp only [CodeCopiesMachine.repeatPrefix, block,
                  List.append_assoc]
                change CodeCopiesMachine.repeatPrefix n (words 3) ++
                  (CodeCopiesMachine.block (words 3) ++ output) =
                  CodeCopiesMachine.block (words 3) ++
                  (CodeCopiesMachine.repeatPrefix n (words 3) ++ output)
                rw [← List.append_assoc,
                  CodeCopiesMachine.repeatPrefix_commute, List.append_assoc]

def scanClock (n wordLength : Nat) : Nat :=
  n * (2 * wordLength + 4) + n + 3

theorem run_scan_full (src : Fin 3) (r : Return)
    (p : CountPhase) (scan restore next : Label)
    (hs : program scan = scanStmt (sourceStack (smallStack src))
      (.cCopy r p) restore)
    (hn : afterCTag r p = scan)
    (hr : program restore =
      scanRestoreStmt (sourceStack (smallStack src)) restore next)
    (n : Nat) (words : Fin 6 → List Bool) (output : List Bool) :
    run (scanClock n (words 3).length)
      (wc (some scan) none
        (Function.update (Function.update words (smallStack src) (unary n)) 5 [])
        output []) =
    wc (some next) none
      (Function.update (Function.update words (smallStack src) (unary n)) 5 [])
      (CodeCopiesMachine.repeatPrefix n (words 3) ++ output) [] := by
  let base : Fin 6 → List Bool :=
    Function.update (Function.update words (smallStack src) (unary n)) 5 []
  have hne : smallStack src ≠ (5 : Fin 6) := by fin_cases src <;> decide
  have hword : base 3 = words 3 := by
    exact update_three src words (unary n) []
  have hrep := run_scan_repetitions src r p scan restore hs hn n [false] []
    output words
  have hfalse := step_scan_false src scan (.cCopy r p) restore hs none
    (Function.update
      (Function.update words (smallStack src) [false]) 5
        (List.replicate n true))
    (CodeCopiesMachine.repeatPrefix n (words 3) ++ output) []
  have hrestore := run_scan_restore src restore next hr
    (false :: List.replicate n true) (some false)
    (Function.update
      (Function.update words (smallStack src) []) 5 [])
    (CodeCopiesMachine.repeatPrefix n (words 3) ++ output) []
  have hrev : (false :: List.replicate n true).reverse = unary n := by
    simp [unary, List.reverse_cons]
  calc
    run (scanClock n (words 3).length)
        (wc (some scan) none base output []) =
      run ((n * (2 * (words 3).length + 4)) +
        (1 + ((n + 2))))
        (wc (some scan) none base output []) := by
          congr 1; simp [scanClock]; omega
    _ = run (1 + (n + 2))
        (wc (some scan) none
          (Function.update
            (Function.update words (smallStack src) [false]) 5
              (List.replicate n true))
          (CodeCopiesMachine.repeatPrefix n (words 3) ++ output) []) := by
          rw [run_add]
          simpa [base, unary] using
            congrArg (run (1 + (n + 2))) hrep
    _ = run (n + 2)
        (wc (some restore) (some false)
          (Function.update
            (Function.update words (smallStack src) []) 5
              (false :: List.replicate n true))
          (CodeCopiesMachine.repeatPrefix n (words 3) ++ output) []) := by
          rw [run_add]
          have hv :
              (Function.update
                (Function.update words (smallStack src) [false]) 5
                  (List.replicate n true)) (smallStack src) = [false] := by
            simp [Function.update, hne]
          have hs5 :
              (Function.update
                (Function.update words (smallStack src) [false]) 5
                  (List.replicate n true)) 5 = List.replicate n true := by
            simp
          have hstart :
              Function.update
                (Function.update
                  (Function.update words (smallStack src) [false]) 5
                    (List.replicate n true)) (smallStack src) [false] =
              Function.update
                (Function.update words (smallStack src) [false]) 5
                  (List.replicate n true) := by
            rw [update_comm6
              (Function.update words (smallStack src) [false]) 5
              (smallStack src) (Ne.symm hne) (List.replicate n true) [false],
              update_twice6]
          have hend :
              Function.update
                (Function.update
                  (Function.update
                    (Function.update words (smallStack src) [false]) 5
                      (List.replicate n true)) (smallStack src) []) 5
                  (false :: List.replicate n true) =
              Function.update
                (Function.update words (smallStack src) []) 5
                  (false :: List.replicate n true) := by
            rw [update_comm6
              (Function.update words (smallStack src) [false]) 5
              (smallStack src) (Ne.symm hne) (List.replicate n true) [],
              update_twice6, update_twice6]
          have hf' :
              TM2.step program
                (wc (some scan) none
                  (Function.update
                    (Function.update words (smallStack src) [false]) 5
                      (List.replicate n true))
                  (CodeCopiesMachine.repeatPrefix n (words 3) ++ output) []) =
              some (wc (some restore) (some false)
                (Function.update
                  (Function.update words (smallStack src) []) 5
                    (false :: List.replicate n true))
                (CodeCopiesMachine.repeatPrefix n (words 3) ++ output) []) := by
            simpa only [hstart, hv, hs5, hend] using hfalse
          rw [run_succ hf' 0]
          simp [run]
    _ = wc (some next) none base
        (CodeCopiesMachine.repeatPrefix n (words 3) ++ output) [] := by
          have hrest' :
              run (n + 2)
                (wc (some restore) (some false)
                  (Function.update
                    (Function.update words (smallStack src) []) 5
                      (false :: List.replicate n true))
                  (CodeCopiesMachine.repeatPrefix n (words 3) ++ output) []) =
              wc (some next) none base
                (CodeCopiesMachine.repeatPrefix n (words 3) ++ output) [] := by
            have hfinish :
                Function.update
                  (Function.update
                    (Function.update words (smallStack src) []) 5 [])
                  (smallStack src) (unary n) = base := by
              simp only [base]
              rw [update_comm6
                (Function.update words (smallStack src) []) 5
                (smallStack src) (Ne.symm hne) [] (unary n),
                update_twice6]
            have hzero :
                (Function.update
                  (Function.update words (smallStack src) []) 5 [])
                    (smallStack src) = [] := by
              simp [Function.update, hne]
            simpa only [List.length_cons, List.length_replicate,
              hrev, hzero, update_twice6, List.append_nil,
              hfinish, show n + 1 + 1 = n + 2 by omega] using hrestore
          exact hrest'

theorem repeatPrefix_add (m n : Nat) (word : List Bool) :
    CodeCopiesMachine.repeatPrefix (m + n) word =
      CodeCopiesMachine.repeatPrefix m word ++
        CodeCopiesMachine.repeatPrefix n word := by
  induction m with
  | zero => simp [CodeCopiesMachine.repeatPrefix]
  | succ m ih =>
      simp only [Nat.succ_add, CodeCopiesMachine.repeatPrefix, ih,
        List.append_assoc]

def outerClock (q₁ q₂ s : Nat) (c : Code) : Nat :=
  1 + scanClock q₁ (codeSize c) + scanClock s (codeSize c) +
    (2 * codeSize c + 3) + (2 * (unary q₂).length + 2) + 1

theorem run_outer (r : Return) (q₁ q₂ s : Nat) (c : Code)
    (words : Fin 6 → List Bool) (output : List Bool)
    (h0 : words 0 = unary q₁) (h1 : words 1 = unary q₂)
    (h2 : words 2 = unary s) (h3 : words 3 = encodeCode c)
    (h5 : words 5 = []) :
    run (outerClock q₁ q₂ s c)
      (wc (some (.outerInit r)) none words output []) =
    wc (some (afterOuter r)) none words
      (encodeCode (outerCode q₁ q₂ s c) ++ output) [] := by
  let endWord := encodeCode (.emit [])
  let initialOut := endWord ++ output
  let qOut := CodeCopiesMachine.repeatPrefix q₁ (encodeCode c) ++ initialOut
  let sOut := CodeCopiesMachine.repeatPrefix s (encodeCode c) ++ qOut
  let cOut := block (encodeCode c) ++ sOut
  let ticketOut := unary q₂ ++ cOut
  have hinit := step_prepend_wc (.outerInit r) (.qScan r) endWord
    rfl none words output []
  have hq0 := run_scan_full 0 r .q (.qScan r) (.qRestore r) (.sScan r)
    rfl rfl rfl q₁ words initialOut
  have hw0 :
      Function.update (Function.update words (smallStack 0) (unary q₁)) 5 [] =
        words := by
    funext i
    fin_cases i <;> simp [smallStack, Function.update, h0, h5]
  have hq : run (scanClock q₁ (codeSize c))
      (wc (some (.qScan r)) none words initialOut []) =
      wc (some (.sScan r)) none words qOut [] := by
    simpa [qOut, h3, encodeCode_length, hw0] using hq0
  have hs0 := run_scan_full 2 r .s (.sScan r) (.sRestore r)
    (.cCopy r .extra) rfl rfl rfl s words qOut
  have hw2 :
      Function.update (Function.update words (smallStack 2) (unary s)) 5 [] =
        words := by
    funext i
    fin_cases i <;> simp [smallStack, Function.update, h2, h5]
  have hs : run (scanClock s (codeSize c))
      (wc (some (.sScan r)) none words qOut []) =
      wc (some (.cCopy r .extra)) none words sOut [] := by
    simpa [sOut, h3, encodeCode_length, hw2] using hs0
  have hc0 := run_c_block r .extra words sOut
  have hc : run (2 * codeSize c + 3)
      (wc (some (.cCopy r .extra)) none words sOut []) =
      wc (some (.q2Copy r)) none words cOut [] := by
    simpa [cOut, h3, block, List.append_assoc, encodeCode_length] using hc0
  have ht0 := run_word_phase 1 (.q2Copy r) (.q2Restore r)
    (.outerFinish r) rfl rfl words cOut
  have ht : run (2 * (unary q₂).length + 2)
      (wc (some (.q2Copy r)) none words cOut []) =
      wc (some (.outerFinish r)) none words ticketOut [] := by
    simpa [ticketOut, h1] using ht0
  have hfinish := step_prepend_wc (.outerFinish r) (afterOuter r)
    ([false,true,true] ++ [false,false,true]) rfl none words ticketOut []
  calc
    run (outerClock q₁ q₂ s c)
        (wc (some (.outerInit r)) none words output []) =
      run (1 + (scanClock q₁ (codeSize c) +
        (scanClock s (codeSize c) + ((2 * codeSize c + 3) +
        ((2 * (unary q₂).length + 2) + 1)))))
        (wc (some (.outerInit r)) none words output []) := by
          congr 1; simp [outerClock]; omega
    _ = run (scanClock q₁ (codeSize c) +
        (scanClock s (codeSize c) + ((2 * codeSize c + 3) +
        ((2 * (unary q₂).length + 2) + 1))))
        (wc (some (.qScan r)) none words initialOut []) := by
          rw [run_add, run_succ hinit 0]
          simp [run, initialOut]
    _ = run (scanClock s (codeSize c) + ((2 * codeSize c + 3) +
        ((2 * (unary q₂).length + 2) + 1)))
        (wc (some (.sScan r)) none words qOut []) := by
          rw [run_add, hq]
    _ = run ((2 * codeSize c + 3) +
        ((2 * (unary q₂).length + 2) + 1))
        (wc (some (.cCopy r .extra)) none words sOut []) := by
          rw [run_add, hs]
    _ = run ((2 * (unary q₂).length + 2) + 1)
        (wc (some (.q2Copy r)) none words cOut []) := by
          rw [run_add, hc]
    _ = run 1 (wc (some (.outerFinish r)) none words ticketOut []) := by
          rw [run_add, ht]
    _ = wc (some (afterOuter r)) none words
          (encodeCode (outerCode q₁ q₂ s c) ++ output) [] := by
          rw [run_succ hfinish 0]
          simp only [run, Function.iterate_zero, id_eq]
          congr 1
          simp only [ticketOut, cOut, sOut, qOut, initialOut, endWord]
          change _ =
            ([false,true,true] ++ [false,false,true] ++ unary q₂ ++
              encodeCode (copies (q₁ + s + 1) c)) ++ output
          rw [CodeCopiesMachine.encode_copies]
          rw [show q₁ + s + 1 = 1 + s + q₁ by omega,
            repeatPrefix_add, repeatPrefix_add]
          simp [CodeCopiesMachine.repeatPrefix, CodeCopiesMachine.block,
            block, encodeCode, unary, List.append_assoc]

private theorem step_work_copy_cons (m : WorkMode) (bit : Bool)
    (v : Control) (words : Fin 6 → List Bool)
    (output scratch : List Bool) :
    TM2.step program
      (wc (some (.workCopy m)) v
        (Function.update words 2 (bit :: words 2)) output scratch) =
    some (wc (some (.workCopy m)) (some bit)
      (Function.update words 5 (bit :: words 5)) output scratch) := by
  simp [TM2.step, TM2.stepAux, program, wc, cfg, contents,
    Function.update]
  funext i
  fin_cases i <;> simp [contents, Function.update]

private theorem step_work_copy_nil (m : WorkMode)
    (v : Control) (words : Fin 6 → List Bool)
    (output scratch : List Bool) :
    TM2.step program
      (wc (some (.workCopy m)) v
        (Function.update words 2 []) output scratch) =
    some (wc (some (.workRestore m)) none
      (Function.update words 2 []) output scratch) := by
  simp [TM2.step, TM2.stepAux, program, wc, cfg, contents,
    Function.update]

private theorem step_work_restore_cons (m : WorkMode) (bit : Bool)
    (v : Control) (words : Fin 6 → List Bool)
    (output scratch : List Bool) :
    TM2.step program
      (wc (some (.workRestore m)) v
        (Function.update words 5 (bit :: words 5)) output scratch) =
    some (wc (some (.workRestore m)) (some bit)
      (Function.update
        (Function.update words 2 (bit :: words 2)) 4
        (if bit then true :: words 4 else words 4)) output scratch) := by
  cases bit <;>
    simp [TM2.step, TM2.stepAux, program, wc, cfg, contents,
      Function.update]
    <;> try { funext i; fin_cases i <;> simp [contents, Function.update] }

private theorem step_work_restore_nil (m : WorkMode)
    (v : Control) (words : Fin 6 → List Bool)
    (output scratch : List Bool) :
    TM2.step program
      (wc (some (.workRestore m)) v
        (Function.update words 5 []) output scratch) =
    some (wc (some (afterWork m)) none
      (Function.update words 5 []) output scratch) := by
  simp [TM2.step, TM2.stepAux, program, wc, cfg, contents,
    Function.update]

theorem run_work_copy (m : WorkMode) (bits : List Bool)
    (v : Control) (words : Fin 6 → List Bool)
    (scanned output scratch : List Bool) :
    run (bits.length + 1)
      (wc (some (.workCopy m)) v
        (Function.update (Function.update words 2 bits) 5 scanned)
        output scratch) =
    wc (some (.workRestore m)) none
      (Function.update (Function.update words 2 []) 5
        (bits.reverse ++ scanned)) output scratch := by
  induction bits generalizing words scanned output scratch v with
  | nil =>
      have hcomm :
          Function.update (Function.update words 2 []) 5 scanned =
          Function.update (Function.update words 5 scanned) 2 [] := by
        exact update_comm6 words 2 5 (by decide) [] scanned
      have hstep := run_succ (step_work_copy_nil m v
        (Function.update words 5 scanned) output scratch) 0
      simpa only [List.length_nil, zero_add, List.reverse_nil, List.nil_append,
        hcomm, run, Function.iterate_zero, id_eq] using hstep
  | cons bit bits ih =>
      rw [show (bit :: bits).length + 1 = (bits.length + 1) + 1 by simp]
      let restWords := Function.update
        (Function.update words 2 bits) 5 scanned
      have hs := step_work_copy_cons m bit v
        restWords output scratch
      have hsrc : restWords 2 = bits := by simp [restWords, Function.update]
      have hscan : restWords 5 = scanned := by simp [restWords]
      have hstart :
          Function.update (Function.update words 2 (bit :: bits)) 5 scanned =
          Function.update restWords 2 (bit :: restWords 2) := by
        rw [hsrc]
        simp only [restWords]
        rw [update_comm6 (Function.update words 2 bits) 5 2
          (by decide) scanned (bit :: bits), update_twice6]
      rw [hstart]
      rw [run_succ hs (bits.length + 1)]
      simp only [hscan, restWords, update_twice6]
      simpa only [List.reverse_cons, List.append_assoc,
        List.singleton_append] using
        ih (some bit) words (bit :: scanned) output scratch

theorem run_work_restore_true (m : WorkMode) (n : Nat)
    (v : Control) (words : Fin 6 → List Bool)
    (output scratch : List Bool) :
    run (n + 1)
      (wc (some (.workRestore m)) v
        (Function.update words 5 (List.replicate n true)) output scratch) =
    wc (some (afterWork m)) none
      (Function.update
        (Function.update
          (Function.update words 5 []) 2
          (List.replicate n true ++ words 2)) 4
        (List.replicate n true ++ words 4)) output scratch := by
  induction n generalizing words output scratch v with
  | zero =>
      have hz :
          Function.update
            (Function.update (Function.update words 5 []) 2 (words 2)) 4
              (words 4) = Function.update words 5 [] := by
        funext i
        fin_cases i <;> simp [Function.update]
      simpa [run, hz] using
        run_succ (step_work_restore_nil m v words output scratch) 0
  | succ n ih =>
      rw [show (n + 1) + 1 = (n + 1) + 1 by rfl]
      have hs := step_work_restore_cons m true v
        (Function.update words 5 (List.replicate n true)) output scratch
      have hv2 : (Function.update words 5 (List.replicate n true)) 2 =
          words 2 := by simp [Function.update]
      have hv4 : (Function.update words 5 (List.replicate n true)) 4 =
          words 4 := by simp [Function.update]
      simp only [Function.update_self, update_twice6, hv2, hv4,
        if_true] at hs
      rw [show List.replicate (n + 1) true =
        true :: List.replicate n true by rfl]
      rw [run_succ hs (n + 1)]
      let words' : Fin 6 → List Bool :=
        Function.update
          (Function.update words 2 (true :: words 2)) 4 (true :: words 4)
      have hstart :
          Function.update words' 5 (List.replicate n true) =
          Function.update
            (Function.update
              (Function.update words 5 (List.replicate n true)) 2
              (true :: words 2)) 4 (true :: words 4) := by
        funext i
        fin_cases i <;> simp [words', Function.update]
      rw [← hstart]
      have hi := ih (some true) words' output scratch
      rw [hi]
      congr 1
      funext i
      fin_cases i <;>
        simp [words', Function.update, List.replicate_succ,
          List.append_assoc, replicate_true_rotate]

def workClock (s : Nat) : Nat := 2 * s + 4

theorem run_work_clone (m : WorkMode) (s : Nat)
    (words : Fin 6 → List Bool) (output : List Bool)
    (h2 : words 2 = unary s) (h4 : words 4 = []) (h5 : words 5 = []) :
    run (workClock s)
      (wc (some (.workCopy m)) none words output []) =
    wc (some (afterWork m)) none
      (Function.update words 4 (List.replicate s true)) output [] := by
  have hcopy0 := run_work_copy m (unary s) none words [] output []
  have hstart :
      Function.update (Function.update words 2 (unary s)) 5 [] = words := by
    funext i
    fin_cases i <;> simp [Function.update, h2, h5]
  have hrev : (unary s).reverse = false :: List.replicate s true := by
    simp [unary]
  have hcopy : run (s + 2)
      (wc (some (.workCopy m)) none words output []) =
      wc (some (.workRestore m)) none
        (Function.update (Function.update words 2 []) 5
          (false :: List.replicate s true)) output [] := by
    simpa [hstart, hrev, unary_length] using hcopy0
  let base : Fin 6 → List Bool :=
    Function.update (Function.update words 2 []) 5
      (List.replicate s true)
  have hfalse0 := step_work_restore_cons m false none base output []
  have hfalseBank :
      Function.update
        (Function.update
          (Function.update
            (Function.update words 2 []) 5 (List.replicate s true)) 2
              [false]) 4 (words 4) =
      Function.update (Function.update words 2 [false]) 5
        (List.replicate s true) := by
    funext i
    fin_cases i <;> simp [Function.update]
  have hfalse :
      TM2.step program
        (wc (some (.workRestore m)) none
          (Function.update (Function.update words 2 []) 5
            (false :: List.replicate s true)) output []) =
      some (wc (some (.workRestore m)) (some false)
        (Function.update
          (Function.update words 2 [false]) 5
          (List.replicate s true)) output []) := by
    simpa [base, Function.update, hfalseBank] using hfalse0
  let middle : Fin 6 → List Bool := Function.update words 2 [false]
  have htrue0 := run_work_restore_true m s (some false) middle output []
  have htrue : run (s + 1)
      (wc (some (.workRestore m)) (some false)
        (Function.update middle 5 (List.replicate s true)) output []) =
      wc (some (afterWork m)) none
        (Function.update words 4 (List.replicate s true)) output [] := by
    have hend :
        Function.update
          (Function.update
            (Function.update middle 5 []) 2
              (List.replicate s true ++ middle 2)) 4
            (List.replicate s true ++ middle 4) =
        Function.update words 4 (List.replicate s true) := by
      funext i
      fin_cases i <;> simp [middle, Function.update, h2, h4, h5,
        unary, List.append_assoc]
    simpa [hend] using htrue0
  calc
    run (workClock s) (wc (some (.workCopy m)) none words output []) =
      run ((s + 2) + (1 + (s + 1)))
        (wc (some (.workCopy m)) none words output []) := by
          congr 1; simp [workClock]; omega
    _ = run (1 + (s + 1))
          (wc (some (.workRestore m)) none
            (Function.update (Function.update words 2 []) 5
              (false :: List.replicate s true)) output []) := by
          rw [run_add, hcopy]
    _ = run (s + 1)
          (wc (some (.workRestore m)) (some false)
            (Function.update middle 5 (List.replicate s true)) output []) := by
          rw [run_add, run_succ hfalse 0]
          simp [run, middle]
    _ = wc (some (afterWork m)) none
          (Function.update words 4 (List.replicate s true)) output [] := htrue

private theorem step_work_loop_true (loop outer done : Label)
    (h : program loop = workLoopStmt outer done)
    (v : Control) (words : Fin 6 → List Bool)
    (output scratch : List Bool) :
    TM2.step program
      (wc (some loop) v (Function.update words 4 (true :: words 4))
        output scratch) =
    some (wc (some outer) none words output scratch) := by
  simp [TM2.step, TM2.stepAux, h, workLoopStmt, wc, cfg, contents,
    Function.update]
  funext i
  fin_cases i <;> simp [contents, Function.update]

private theorem step_work_loop_nil (loop outer done : Label)
    (h : program loop = workLoopStmt outer done)
    (v : Control) (words : Fin 6 → List Bool)
    (output scratch : List Bool) :
    TM2.step program
      (wc (some loop) v (Function.update words 4 []) output scratch) =
    some (wc (some done) none (Function.update words 4 [])
      output scratch) := by
  simp [TM2.step, TM2.stepAux, h, workLoopStmt, wc, cfg, contents,
    Function.update]

theorem run_outer_repetitions (r : Return) (loop tag done : Label)
    (hloop : program loop = workLoopStmt (.outerInit r) done)
    (hret : afterOuter r = tag)
    (htag : program tag = prepend [false,true,true] loop)
    (q₁ q₂ s : Nat) (c : Code) (n : Nat)
    (words : Fin 6 → List Bool) (tail output : List Bool)
    (h0 : words 0 = unary q₁) (h1 : words 1 = unary q₂)
    (h2 : words 2 = unary s) (h3 : words 3 = encodeCode c)
    (h5 : words 5 = []) :
    run (n * (outerClock q₁ q₂ s c + 2))
      (wc (some loop) none
        (Function.update words 4 (List.replicate n true ++ tail))
        output []) =
    wc (some loop) none (Function.update words 4 tail)
      (CodeCopiesMachine.repeatPrefix n
        (encodeCode (outerCode q₁ q₂ s c)) ++ output) [] := by
  induction n generalizing output with
  | zero => simp [run, CodeCopiesMachine.repeatPrefix]
  | succ n ih =>
      let restWords := Function.update words 4 (List.replicate n true ++ tail)
      have hs := step_work_loop_true loop (.outerInit r) done hloop none
        restWords output []
      have ho := run_outer r q₁ q₂ s c restWords output
        (by simpa [restWords, Function.update] using h0)
        (by simpa [restWords, Function.update] using h1)
        (by simpa [restWords, Function.update] using h2)
        (by simpa [restWords, Function.update] using h3)
        (by simpa [restWords, Function.update] using h5)
      have ht := step_prepend_wc tag loop [false,true,true] htag none
        restWords (encodeCode (outerCode q₁ q₂ s c) ++ output) []
      calc
        run ((n + 1) * (outerClock q₁ q₂ s c + 2))
            (wc (some loop) none
              (Function.update words 4
                (List.replicate (n + 1) true ++ tail)) output []) =
          run (1 + (outerClock q₁ q₂ s c +
            (1 + n * (outerClock q₁ q₂ s c + 2))))
            (wc (some loop) none
              (Function.update restWords 4 (true :: restWords 4))
              output []) := by
            congr 1
            · simp only [Nat.succ_mul]; omega
            · simp [restWords, Function.update, List.replicate_succ,
                List.cons_append]
        _ = run (outerClock q₁ q₂ s c +
            (1 + n * (outerClock q₁ q₂ s c + 2)))
            (wc (some (.outerInit r)) none restWords output []) := by
            rw [run_add, run_succ hs 0]
            simp [run]
        _ = run (1 + n * (outerClock q₁ q₂ s c + 2))
            (wc (some tag) none restWords
              (encodeCode (outerCode q₁ q₂ s c) ++ output) []) := by
            rw [run_add, ho, hret]
        _ = run (n * (outerClock q₁ q₂ s c + 2))
            (wc (some loop) none restWords
              (block (encodeCode (outerCode q₁ q₂ s c)) ++ output) []) := by
            rw [run_add, run_succ ht 0]
            simp [run, block, List.append_assoc]
        _ = wc (some loop) none (Function.update words 4 tail)
            (CodeCopiesMachine.repeatPrefix (n + 1)
              (encodeCode (outerCode q₁ q₂ s c)) ++ output) [] := by
            have hi := ih (block (encodeCode (outerCode q₁ q₂ s c)) ++ output)
            simp only [restWords, update_twice6] at hi ⊢
            rw [hi]
            congr 1
            simp only [CodeCopiesMachine.repeatPrefix]
            simp only [List.append_assoc]
            change CodeCopiesMachine.repeatPrefix n
                (encodeCode (outerCode q₁ q₂ s c)) ++
                (CodeCopiesMachine.block
                  (encodeCode (outerCode q₁ q₂ s c)) ++ output) =
              CodeCopiesMachine.block
                (encodeCode (outerCode q₁ q₂ s c)) ++
                (CodeCopiesMachine.repeatPrefix n
                  (encodeCode (outerCode q₁ q₂ s c)) ++ output)
            rw [← List.append_assoc,
              CodeCopiesMachine.repeatPrefix_commute, List.append_assoc]

def copiesOuterClock (q₁ q₂ s : Nat) (c : Code) : Nat :=
  1 + workClock s + s * (outerClock q₁ q₂ s c + 2) + 1

theorem run_copies_outer (r : Return) (m : WorkMode)
    (init loop tag done : Label)
    (hinit : program init = prepend (encodeCode (.emit [])) (.workCopy m))
    (hm : afterWork m = loop)
    (hloop : program loop = workLoopStmt (.outerInit r) done)
    (hret : afterOuter r = tag)
    (htag : program tag = prepend [false,true,true] loop)
    (q₁ q₂ s : Nat) (c : Code)
    (words : Fin 6 → List Bool) (output : List Bool)
    (h0 : words 0 = unary q₁) (h1 : words 1 = unary q₂)
    (h2 : words 2 = unary s) (h3 : words 3 = encodeCode c)
    (h4 : words 4 = []) (h5 : words 5 = []) :
    run (copiesOuterClock q₁ q₂ s c)
      (wc (some init) none words output []) =
    wc (some done) none words
      (encodeCode (copies s (outerCode q₁ q₂ s c)) ++ output) [] := by
  let endWord := encodeCode (.emit [])
  let preOut := endWord ++ output
  let outerWord := encodeCode (outerCode q₁ q₂ s c)
  have hpre := step_prepend_wc init (.workCopy m) endWord hinit
    none words output []
  have hwork0 := run_work_clone m s words preOut h2 h4 h5
  have hwork : run (workClock s)
      (wc (some (.workCopy m)) none words preOut []) =
      wc (some loop) none
        (Function.update words 4 (List.replicate s true)) preOut [] := by
    simpa [hm] using hwork0
  have hreps0 := run_outer_repetitions r loop tag done hloop hret htag
    q₁ q₂ s c s words [] preOut h0 h1 h2 h3 h5
  have hreps : run (s * (outerClock q₁ q₂ s c + 2))
      (wc (some loop) none
        (Function.update words 4 (List.replicate s true)) preOut []) =
      wc (some loop) none (Function.update words 4 [])
        (CodeCopiesMachine.repeatPrefix s outerWord ++ preOut) [] := by
    simpa [outerWord] using hreps0
  have hdone := step_work_loop_nil loop (.outerInit r) done hloop none
    words (CodeCopiesMachine.repeatPrefix s outerWord ++ preOut) []
  calc
    run (copiesOuterClock q₁ q₂ s c)
        (wc (some init) none words output []) =
      run (1 + (workClock s +
        (s * (outerClock q₁ q₂ s c + 2) + 1)))
        (wc (some init) none words output []) := by
          congr 1; simp [copiesOuterClock]; omega
    _ = run (workClock s +
        (s * (outerClock q₁ q₂ s c + 2) + 1))
        (wc (some (.workCopy m)) none words preOut []) := by
          rw [run_add, run_succ hpre 0]
          simp [run, preOut]
    _ = run (s * (outerClock q₁ q₂ s c + 2) + 1)
        (wc (some loop) none
          (Function.update words 4 (List.replicate s true)) preOut []) := by
          rw [run_add, hwork]
    _ = run 1
        (wc (some loop) none (Function.update words 4 [])
          (CodeCopiesMachine.repeatPrefix s outerWord ++ preOut) []) := by
          rw [run_add, hreps]
    _ = wc (some done) none words
          (encodeCode (copies s (outerCode q₁ q₂ s c)) ++ output) [] := by
          rw [run_succ hdone 0]
          simp only [run, Function.iterate_zero, id_eq]
          congr 1
          · simp [Function.update_eq_self, h4]
          · simp [preOut, endWord, outerWord,
              CodeCopiesMachine.encode_copies, encodeCode, unary,
              List.append_assoc]

theorem run_left_block (words : Fin 6 → List Bool) (output : List Bool) :
    run (2 * (words 3).length + 3)
      (wc (some .leftCopy) none words output []) =
    wc (some .leftLoop) none words (block (words 3) ++ output) [] := by
  have hc := run_word_phase 3 .leftCopy .leftRestore .leftTag
    rfl rfl words output
  have ht := step_prepend_wc .leftTag .leftLoop [false,true,true] rfl
    none words (words 3 ++ output) []
  calc
    run (2 * (words 3).length + 3)
        (wc (some .leftCopy) none words output []) =
      run ((2 * (words 3).length + 2) + 1)
        (wc (some .leftCopy) none words output []) := by congr 1
    _ = run 1 (wc (some .leftTag) none words (words 3 ++ output) []) := by
      rw [run_add, hc]
    _ = wc (some .leftLoop) none words (block (words 3) ++ output) [] := by
      rw [run_succ ht 0]
      simp [run, block]

private theorem step_left_loop_true (v : Control)
    (words : Fin 6 → List Bool) (output scratch : List Bool) :
    TM2.step program
      (wc (some .leftLoop) v
        (Function.update words 4 (true :: words 4)) output scratch) =
    some (wc (some .leftCopy) none words output scratch) := by
  simp [TM2.step, TM2.stepAux, program, wc, cfg, contents,
    Function.update]
  funext i
  fin_cases i <;> simp [contents, Function.update]

private theorem step_left_loop_nil (v : Control)
    (words : Fin 6 → List Bool) (output scratch : List Bool) :
    TM2.step program
      (wc (some .leftLoop) v (Function.update words 4 []) output scratch) =
    some (wc (some .child1Finish) none
      (Function.update words 4 []) output scratch) := by
  simp [TM2.step, TM2.stepAux, program, wc, cfg, contents,
    Function.update]

theorem run_left_repetitions (n : Nat) (words : Fin 6 → List Bool)
    (tail output : List Bool) :
    run (n * (2 * (words 3).length + 4))
      (wc (some .leftLoop) none
        (Function.update words 4 (List.replicate n true ++ tail)) output []) =
    wc (some .leftLoop) none (Function.update words 4 tail)
      (CodeCopiesMachine.repeatPrefix n (words 3) ++ output) [] := by
  induction n generalizing output with
  | zero => simp [run, CodeCopiesMachine.repeatPrefix]
  | succ n ih =>
      let restWords := Function.update words 4 (List.replicate n true ++ tail)
      have hs := step_left_loop_true none restWords output []
      have hc := run_left_block restWords output
      have hword : restWords 3 = words 3 := by
        simp [restWords, Function.update]
      calc
        run ((n + 1) * (2 * (words 3).length + 4))
            (wc (some .leftLoop) none
              (Function.update words 4
                (List.replicate (n + 1) true ++ tail)) output []) =
          run (1 + ((2 * (words 3).length + 3) +
            n * (2 * (words 3).length + 4)))
            (wc (some .leftLoop) none
              (Function.update restWords 4 (true :: restWords 4))
              output []) := by
            congr 1
            · simp only [Nat.succ_mul]; omega
            · simp [restWords, Function.update, List.replicate_succ,
                List.cons_append]
        _ = run ((2 * (words 3).length + 3) +
            n * (2 * (words 3).length + 4))
            (wc (some .leftCopy) none restWords output []) := by
            rw [run_add, run_succ hs 0]
            simp [run]
        _ = run (n * (2 * (words 3).length + 4))
            (wc (some .leftLoop) none restWords
              (block (words 3) ++ output) []) := by
            rw [run_add]
            simpa [hword] using
              congrArg (run (n * (2 * (words 3).length + 4))) hc
        _ = wc (some .leftLoop) none (Function.update words 4 tail)
            (CodeCopiesMachine.repeatPrefix (n + 1) (words 3) ++ output) [] := by
            have hi := ih (block (words 3) ++ output)
            simp only [restWords, update_twice6] at hi ⊢
            rw [hi]
            congr 1
            simp only [CodeCopiesMachine.repeatPrefix, List.append_assoc]
            change CodeCopiesMachine.repeatPrefix n (words 3) ++
                (CodeCopiesMachine.block (words 3) ++ output) =
              CodeCopiesMachine.block (words 3) ++
                (CodeCopiesMachine.repeatPrefix n (words 3) ++ output)
            rw [← List.append_assoc,
              CodeCopiesMachine.repeatPrefix_commute, List.append_assoc]

private theorem step_left_extra (words : Fin 6 → List Bool)
    (output scratch : List Bool) :
    TM2.step program (wc (some .leftExtra) none words output scratch) =
    some (wc (some .leftLoop) none
      (Function.update words 4 (true :: words 4)) output scratch) := by
  simp [TM2.step, TM2.stepAux, program, wc, cfg, contents]
  funext i
  fin_cases i <;> simp [contents, Function.update]

def copiesLeftClock (s : Nat) (c : Code) : Nat :=
  1 + workClock s + 1 + (s + 1) * (2 * codeSize c + 4) + 1

theorem run_copies_left (s : Nat) (c : Code)
    (words : Fin 6 → List Bool) (output : List Bool)
    (h2 : words 2 = unary s) (h3 : words 3 = encodeCode c)
    (h4 : words 4 = []) (h5 : words 5 = []) :
    run (copiesLeftClock s c)
      (wc (some .rawRightDone) none words output []) =
    wc (some .child1Finish) none words
      (encodeCode (copies (s + 1) c) ++ output) [] := by
  let endWord := encodeCode (.emit [])
  let preOut := endWord ++ output
  have hpre := step_prepend_wc .rawRightDone (.workCopy .left) endWord
    rfl none words output []
  have hwork := run_work_clone .left s words preOut h2 h4 h5
  have hextra := step_left_extra
    (Function.update words 4 (List.replicate s true)) preOut []
  have hreps0 := run_left_repetitions (s + 1) words [] preOut
  have hreps : run ((s + 1) * (2 * codeSize c + 4))
      (wc (some .leftLoop) none
        (Function.update words 4 (true :: List.replicate s true)) preOut []) =
      wc (some .leftLoop) none (Function.update words 4 [])
        (CodeCopiesMachine.repeatPrefix (s + 1) (encodeCode c) ++ preOut) [] := by
    simpa [h3, encodeCode_length, List.replicate_succ,
      List.append_nil] using hreps0
  have hdone := step_left_loop_nil none words
    (CodeCopiesMachine.repeatPrefix (s + 1) (encodeCode c) ++ preOut) []
  calc
    run (copiesLeftClock s c)
        (wc (some .rawRightDone) none words output []) =
      run (1 + (workClock s + (1 +
        ((s + 1) * (2 * codeSize c + 4) + 1))))
        (wc (some .rawRightDone) none words output []) := by
          congr 1; simp [copiesLeftClock]; omega
    _ = run (workClock s + (1 +
        ((s + 1) * (2 * codeSize c + 4) + 1)))
        (wc (some (.workCopy .left)) none words preOut []) := by
          rw [run_add, run_succ hpre 0]
          simp [run, preOut]
    _ = run (1 + ((s + 1) * (2 * codeSize c + 4) + 1))
        (wc (some .leftExtra) none
          (Function.update words 4 (List.replicate s true)) preOut []) := by
          rw [run_add]
          simpa only [afterWork] using
            congrArg (run (1 + ((s + 1) * (2 * codeSize c + 4) + 1))) hwork
    _ = run ((s + 1) * (2 * codeSize c + 4) + 1)
        (wc (some .leftLoop) none
          (Function.update words 4 (true :: List.replicate s true)) preOut []) := by
          rw [run_add, run_succ hextra 0]
          simp [run, update_twice6, Function.update_self]
    _ = run 1 (wc (some .leftLoop) none (Function.update words 4 [])
          (CodeCopiesMachine.repeatPrefix (s + 1) (encodeCode c) ++ preOut) []) := by
          rw [run_add, hreps]
    _ = wc (some .child1Finish) none words
          (encodeCode (copies (s + 1) c) ++ output) [] := by
          rw [run_succ hdone 0]
          simp only [run, Function.iterate_zero, id_eq]
          congr 1
          · simp [h4]
          · simp [preOut, endWord, CodeCopiesMachine.encode_copies,
              encodeCode, unary, List.append_assoc]

def taggedClock (q₁ q₂ s : Nat) (c : Code) : Nat :=
  outerClock q₁ q₂ s c + 2 * copiesOuterClock q₁ q₂ s c +
    copiesLeftClock s c + 5

/-- An explicit degree-three polynomial for the complete physical run clock.
The only variable word length is the actual serialized child-code length. -/
def polynomialClock (q₁ q₂ s childLength : Nat) : Nat :=
  let outer := (q₁ + s) * (2 * childLength + 5) +
    2 * childLength + 2 * q₂ + 15
  outer + 2 * (s * (outer + 2) + 2 * s + 6) +
    ((s + 1) * (2 * childLength + 4) + 2 * s + 7) + 5

theorem taggedClock_eq_polynomial (q₁ q₂ s : Nat) (c : Code) :
    taggedClock q₁ q₂ s c =
      polynomialClock q₁ q₂ s (encodeCode c).length := by
  simp only [encodeCode_length, polynomialClock, taggedClock,
    copiesOuterClock, copiesLeftClock, outerClock, scanClock,
    workClock, unary_length]
  ring

private theorem step_accept (words : Fin 6 → List Bool)
    (output : List Bool) :
    TM2.step program (wc (some .accept) none words output []) =
    some (wc none none words output []) := by
  simp [TM2.step, TM2.stepAux, program, wc, cfg]

theorem run_tagged_words (q₁ q₂ s : Nat) (c : Code)
    (words : Fin 6 → List Bool)
    (h0 : words 0 = unary q₁) (h1 : words 1 = unary q₂)
    (h2 : words 2 = unary s) (h3 : words 3 = encodeCode c)
    (h4 : words 4 = []) (h5 : words 5 = []) :
    run (taggedClock q₁ q₂ s c)
      (wc (some (.outerInit .third)) none words [] []) =
    wc none none words (encodeCode (taggedCode q₁ q₂ s c)) [] := by
  let outerC := outerCode q₁ q₂ s c
  let fixedC := fixedTailCode q₁ q₂ s c
  let rawC := rawCode q₁ q₂ s c
  let thirdC : Code := .append (.emit [true,true]) outerC
  let secondC : Code := .append (.emit [true,false]) fixedC
  let firstC : Code := .append (.emit [false]) rawC
  let thirdOut := encodeCode thirdC
  let secondOut := encodeCode secondC ++ thirdOut
  let rawRightOut := encodeCode (copies s outerC) ++ secondOut
  let rawOut := encodeCode (copies (s + 1) c) ++ rawRightOut
  let firstOut := encodeCode firstC ++ secondOut
  let allOut := encodeCode (taggedCode q₁ q₂ s c)
  have ho := run_outer .third q₁ q₂ s c words [] h0 h1 h2 h3 h5
  have h3step0 := step_prepend_wc .child3Finish .fixedInit
    ([false,true,true] ++ encodeCode (.emit [true,true])) rfl none
    words (encodeCode outerC) []
  have h3step : TM2.step program
      (wc (some .child3Finish) none words (encodeCode outerC) []) =
      some (wc (some .fixedInit) none words thirdOut []) := by
    simpa [thirdOut, thirdC, encodeCode, List.append_assoc] using h3step0
  have hf := run_copies_outer .fixed .fixed .fixedInit .fixedLoop
    .fixedTag .child2Finish rfl rfl rfl rfl rfl
    q₁ q₂ s c words thirdOut h0 h1 h2 h3 h4 h5
  have h2step0 := step_prepend_wc .child2Finish .rawRightInit
    ([false,true,true] ++ encodeCode (.emit [true,false])) rfl none
    words (encodeCode (copies s outerC) ++ thirdOut) []
  have h2step : TM2.step program
      (wc (some .child2Finish) none words
        (encodeCode (copies s outerC) ++ thirdOut) []) =
      some (wc (some .rawRightInit) none words secondOut []) := by
    simpa [secondOut, secondC, fixedC, fixedTailCode,
      encodeCode, List.append_assoc] using h2step0
  have hr := run_copies_outer .raw .raw .rawRightInit .rawOuterLoop
    .rawTag .rawRightDone rfl rfl rfl rfl rfl
    q₁ q₂ s c words secondOut h0 h1 h2 h3 h4 h5
  have hl := run_copies_left s c words rawRightOut h2 h3 h4 h5
  have h1step0 := step_prepend_wc .child1Finish .branchFinish
    ([false,true,true] ++ encodeCode (.emit [false]) ++ [false,true,true])
    rfl none words rawOut []
  have h1step : TM2.step program
      (wc (some .child1Finish) none words rawOut []) =
      some (wc (some .branchFinish) none words firstOut []) := by
    simpa [firstOut, firstC, rawC, rawCode, rawOut, rawRightOut,
      encodeCode, List.append_assoc] using h1step0
  have hb0 := step_prepend_wc .branchFinish .accept
    ([true,false,false] ++ unary 256 ++ unary 254 ++ unary 255)
    rfl none words firstOut []
  have hb : TM2.step program
      (wc (some .branchFinish) none words firstOut []) =
      some (wc (some .accept) none words allOut []) := by
    simpa [allOut, taggedCode, thirdOut, secondOut, firstOut,
      thirdC, secondC, firstC, rawC, fixedC, outerC,
      encodeCode, List.append_assoc] using hb0
  have ha := step_accept words allOut
  calc
    run (taggedClock q₁ q₂ s c)
        (wc (some (.outerInit .third)) none words [] []) =
      run (outerClock q₁ q₂ s c +
        (1 + (copiesOuterClock q₁ q₂ s c +
        (1 + (copiesOuterClock q₁ q₂ s c +
        (copiesLeftClock s c + (1 + (1 + 1))))))))
        (wc (some (.outerInit .third)) none words [] []) := by
          congr 1; simp [taggedClock]; omega
    _ = run (1 + (copiesOuterClock q₁ q₂ s c +
        (1 + (copiesOuterClock q₁ q₂ s c +
        (copiesLeftClock s c + (1 + (1 + 1)))))))
        (wc (some .child3Finish) none words (encodeCode outerC) []) := by
          rw [run_add, ho]
          simp only [afterOuter, outerC, List.append_nil]
    _ = run (copiesOuterClock q₁ q₂ s c +
        (1 + (copiesOuterClock q₁ q₂ s c +
        (copiesLeftClock s c + (1 + (1 + 1))))))
        (wc (some .fixedInit) none words thirdOut []) := by
          exact run_cons h3step _
    _ = run (1 + (copiesOuterClock q₁ q₂ s c +
        (copiesLeftClock s c + (1 + (1 + 1)))))
        (wc (some .child2Finish) none words
          (encodeCode (copies s outerC) ++ thirdOut) []) := by
          rw [run_add, hf]
    _ = run (copiesOuterClock q₁ q₂ s c +
        (copiesLeftClock s c + (1 + (1 + 1))))
        (wc (some .rawRightInit) none words secondOut []) := by
          exact run_cons h2step _
    _ = run (copiesLeftClock s c + (1 + (1 + 1)))
        (wc (some .rawRightDone) none words rawRightOut []) := by
          rw [run_add, hr]
    _ = run (1 + (1 + 1))
        (wc (some .child1Finish) none words rawOut []) := by
          rw [run_add, hl]
    _ = run (1 + 1)
        (wc (some .branchFinish) none words firstOut []) := by
          exact run_cons h1step _
    _ = run 1 (wc (some .accept) none words allOut []) := by
          exact run_cons hb _
    _ = wc none none words allOut [] := by
          rw [run_succ ha 0]
          rfl

def sourceWords (q₁ q₂ s : Nat) (c : Code) : Fin 6 → List Bool :=
  fun i => if i = 0 then unary q₁ else if i = 1 then unary q₂ else
    if i = 2 then unary s else if i = 3 then encodeCode c else []

theorem inputs_eq_contents (q₁ q₂ s : Nat) (c : Code) :
    inputs q₁ q₂ s c = contents (sourceWords q₁ q₂ s c) [] [] := by
  funext i
  fin_cases i <;> simp [inputs, contents, sourceWords]

theorem run_tagged (q₁ q₂ s : Nat) (c : Code) :
    run (taggedClock q₁ q₂ s c)
      (cfg (some (.outerInit .third)) none (inputs q₁ q₂ s c)) =
    cfg none none
      (Function.update (inputs q₁ q₂ s c) 7
        (encodeCode (taggedCode q₁ q₂ s c))) := by
  have h := run_tagged_words q₁ q₂ s c (sourceWords q₁ q₂ s c)
    (by simp [sourceWords]) (by simp [sourceWords])
    (by simp [sourceWords]) (by simp [sourceWords])
    (by simp [sourceWords]) (by simp [sourceWords])
  rw [inputs_eq_contents]
  change run (taggedClock q₁ q₂ s c)
    (wc (some (.outerInit .third)) none (sourceWords q₁ q₂ s c) [] []) = _
  rw [h]
  apply congrArg (cfg none none)
  funext i
  fin_cases i <;> simp [contents, Function.update, inputs, sourceWords]

noncomputable def machine :=
  ofFinite (0 : Fin 8) (7 : Fin 8) (Label.outerInit .third)
    (none : Control) program

theorem machine_run_tagged (q₁ q₂ s : Nat) (c : Code) :
    machine.run (taggedClock q₁ q₂ s c)
      (renameCfg (Fintype.equivFin (Fin 8)) (Fintype.equivFin Label)
        (Fintype.equivFin Control)
        (cfg (some (.outerInit .third)) none (inputs q₁ q₂ s c))) =
      renameCfg (Fintype.equivFin (Fin 8)) (Fintype.equivFin Label)
        (Fintype.equivFin Control)
        (cfg none none
          (Function.update (inputs q₁ q₂ s c) 7
            (encodeCode (taggedCode q₁ q₂ s c)))) := by
  exact (ofFinite_run (0 : Fin 8) (7 : Fin 8)
    (Label.outerInit .third) (none : Control) program
    (cfg (some (.outerInit .third)) none (inputs q₁ q₂ s c))
    (taggedClock q₁ q₂ s c)).trans
    (congrArg (renameCfg (Fintype.equivFin (Fin 8))
      (Fintype.equivFin Label) (Fintype.equivFin Control))
      (run_tagged q₁ q₂ s c))

#print axioms run_tagged_words
#print axioms taggedClock_eq_polynomial
#print axioms run_tagged
#print axioms machine_run_tagged

end Paper2.TaggedCompiler
