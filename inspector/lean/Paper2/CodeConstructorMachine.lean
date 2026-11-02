import Paper2.GeneratorSerialization
import EthInapproximability.CurrentPaper.BitMachineEncoding

/-! Fixed-control physical assembly of first-order constructor serializations. -/

namespace Paper2.CodeConstructorMachine

open Turing Turing.TM2.Stmt
open EthInapproximability.CurrentPaper.BitMachineEncoding
open Paper2.GeneratorCode Paper2.GeneratorSerialization

inductive Label where
  | appendRightCopy | appendRightRestore | appendLeftCopy | appendLeftRestore
  | appendHeader
  | branchThirdCopy | branchThirdRestore | branchSecondCopy | branchSecondRestore
  | branchFirstCopy | branchFirstRestore | branchBCopy | branchBRestore
  | branchACopy | branchARestore | branchNCopy | branchNRestore | branchHeader
  | accept
  deriving DecidableEq, Fintype

abbrev Control := Option Bool

def sourceStack (i : Fin 6) : Fin 8 := ⟨i.val, by omega⟩

def copyStmt (src : Fin 6) (copy restore : Label) :
    TM2.Stmt (fun _ : Fin 8 => Bool) Label Control :=
  pop (sourceStack src) (fun _ b => b)
    (branch Option.isSome
      (push 7 (fun b => b.getD false) (goto (fun _ => copy)))
      (goto (fun _ => restore)))

def restoreStmt (src : Fin 6) (restore next : Label) :
    TM2.Stmt (fun _ : Fin 8 => Bool) Label Control :=
  pop 7 (fun _ b => b)
    (branch Option.isSome
      (push (sourceStack src) (fun b => b.getD false)
        (push 6 (fun b => b.getD false) (goto (fun _ => restore))))
      (goto (fun _ => next)))

def program : Label → TM2.Stmt (fun _ : Fin 8 => Bool) Label Control
  | .appendRightCopy => copyStmt 1 .appendRightCopy .appendRightRestore
  | .appendRightRestore => restoreStmt 1 .appendRightRestore .appendLeftCopy
  | .appendLeftCopy => copyStmt 0 .appendLeftCopy .appendLeftRestore
  | .appendLeftRestore => restoreStmt 0 .appendLeftRestore .appendHeader
  | .appendHeader =>
      push 6 (fun _ => true) (push 6 (fun _ => true)
        (push 6 (fun _ => false) (goto (fun _ => .accept))))
  | .branchThirdCopy => copyStmt 5 .branchThirdCopy .branchThirdRestore
  | .branchThirdRestore => restoreStmt 5 .branchThirdRestore .branchSecondCopy
  | .branchSecondCopy => copyStmt 4 .branchSecondCopy .branchSecondRestore
  | .branchSecondRestore => restoreStmt 4 .branchSecondRestore .branchFirstCopy
  | .branchFirstCopy => copyStmt 3 .branchFirstCopy .branchFirstRestore
  | .branchFirstRestore => restoreStmt 3 .branchFirstRestore .branchBCopy
  | .branchBCopy => copyStmt 2 .branchBCopy .branchBRestore
  | .branchBRestore => restoreStmt 2 .branchBRestore .branchACopy
  | .branchACopy => copyStmt 1 .branchACopy .branchARestore
  | .branchARestore => restoreStmt 1 .branchARestore .branchNCopy
  | .branchNCopy => copyStmt 0 .branchNCopy .branchNRestore
  | .branchNRestore => restoreStmt 0 .branchNRestore .branchHeader
  | .branchHeader =>
      push 6 (fun _ => false) (push 6 (fun _ => false)
        (push 6 (fun _ => true) (goto (fun _ => .accept))))
  | .accept => load (fun _ => none) halt

def contents (words : Fin 6 → List Bool) (output scratch : List Bool) :
    Fin 8 → List Bool :=
  fun i => if h : i.val < 6 then words ⟨i.val, h⟩ else
    if i.val = 6 then output else scratch

def cfg (label : Option Label) (control : Control)
    (words : Fin 6 → List Bool) (output scratch : List Bool) :
    TM2.Cfg (fun _ : Fin 8 => Bool) Label Control :=
  ⟨label, control, contents words output scratch⟩

def run (steps : Nat) (c : TM2.Cfg (fun _ : Fin 8 => Bool) Label Control) :=
  ((advance program)^[steps]) c

private theorem run_succ {c d : TM2.Cfg (fun _ : Fin 8 => Bool) Label Control}
    (h : TM2.step program c = some d) (n : Nat) :
    run (n + 1) c = run n d := by
  simp only [run, Function.iterate_succ_apply, advance, h, Option.getD_some]

private theorem run_add (a b : Nat)
    (c : TM2.Cfg (fun _ : Fin 8 => Bool) Label Control) :
    run (a + b) c = run b (run a c) := by
  rw [Nat.add_comm a b]
  simp only [run, Function.iterate_add_apply]

private theorem step_copy_cons (src : Fin 6) (copy restore : Label)
    (hprogram : program copy = copyStmt src copy restore)
    (bit : Bool) (control : Control) (words : Fin 6 → List Bool)
    (output scratch : List Bool) :
    TM2.step program
      (cfg (some copy) control (Function.update words src (bit :: words src))
        output scratch) =
    some (cfg (some copy) (some bit)
      words output (bit :: scratch)) := by
  fin_cases src <;>
    simp [TM2.step, TM2.stepAux, hprogram, copyStmt, cfg, contents,
      sourceStack, Function.update]
    <;> try { funext i; fin_cases i <;> simp [contents, Function.update] }

private theorem step_copy_nil (src : Fin 6) (copy restore : Label)
    (hprogram : program copy = copyStmt src copy restore)
    (control : Control) (words : Fin 6 → List Bool)
    (output scratch : List Bool) :
    TM2.step program
      (cfg (some copy) control (Function.update words src []) output scratch) =
    some (cfg (some restore) none
      (Function.update words src []) output scratch) := by
  fin_cases src <;>
    simp [TM2.step, TM2.stepAux, hprogram, copyStmt, cfg, contents,
      sourceStack, Function.update]

private theorem step_restore_cons (src : Fin 6) (restore next : Label)
    (hprogram : program restore = restoreStmt src restore next)
    (bit : Bool) (control : Control) (words : Fin 6 → List Bool)
    (output scratch : List Bool) :
    TM2.step program
      (cfg (some restore) control words output (bit :: scratch)) =
    some (cfg (some restore) (some bit)
      (Function.update words src (bit :: words src)) (bit :: output) scratch) := by
  fin_cases src <;>
    simp [TM2.step, TM2.stepAux, hprogram, restoreStmt, cfg, contents,
      sourceStack, Function.update]
    <;> try { funext i; fin_cases i <;> simp [contents, Function.update] }

private theorem step_restore_nil (src : Fin 6) (restore next : Label)
    (hprogram : program restore = restoreStmt src restore next)
    (control : Control) (words : Fin 6 → List Bool) (output : List Bool) :
    TM2.step program (cfg (some restore) control words output []) =
    some (cfg (some next) none words output []) := by
  simp [TM2.step, TM2.stepAux, hprogram, restoreStmt, cfg, contents]

private theorem update_twice (words : Fin 6 → List Bool) (src : Fin 6)
    (a b : List Bool) :
    Function.update (Function.update words src a) src b =
      Function.update words src b := by
  funext i
  by_cases h : i = src <;> simp [Function.update, h]

theorem run_copy (src : Fin 6) (copy restore : Label)
    (hprogram : program copy = copyStmt src copy restore)
    (bits : List Bool) (control : Control) (words : Fin 6 → List Bool)
    (output scratch : List Bool) :
    run (bits.length + 1)
      (cfg (some copy) control (Function.update words src bits) output scratch) =
    cfg (some restore) none (Function.update words src [])
      output (bits.reverse ++ scratch) := by
  induction bits generalizing words output scratch control with
  | nil =>
      simpa only [List.length_nil, zero_add, List.reverse_nil, List.nil_append] using
        run_succ (step_copy_nil src copy restore hprogram control words output scratch) 0
  | cons bit bits ih =>
      rw [show (bit :: bits).length + 1 = (bits.length + 1) + 1 by simp]
      have hstep := step_copy_cons src copy restore hprogram bit control
        (Function.update words src bits) output scratch
      simp only [Function.update_self, update_twice] at hstep
      rw [run_succ hstep (bits.length + 1)]
      simpa only [update_twice, List.reverse_cons,
        List.append_assoc, List.singleton_append] using
        ih (some bit) (Function.update words src bits) output (bit :: scratch)

theorem run_restore (src : Fin 6) (restore next : Label)
    (hprogram : program restore = restoreStmt src restore next)
    (bits : List Bool) (control : Control) (words : Fin 6 → List Bool)
    (output : List Bool) :
    run (bits.length + 1) (cfg (some restore) control words output bits) =
    cfg (some next) none
      (Function.update words src (bits.reverse ++ words src))
      (bits.reverse ++ output) [] := by
  induction bits generalizing words output control with
  | nil =>
      simpa only [List.length_nil, zero_add, List.reverse_nil, List.nil_append,
        Function.update_eq_self] using
        run_succ (step_restore_nil src restore next hprogram control words output) 0
  | cons bit bits ih =>
      rw [show (bit :: bits).length + 1 = (bits.length + 1) + 1 by simp]
      rw [run_succ (step_restore_cons src restore next hprogram bit control
        words output bits) (bits.length + 1)]
      simpa only [Function.update_self, update_twice,
        List.reverse_cons, List.append_assoc, List.singleton_append] using
        ih (some bit) (Function.update words src (bit :: words src)) (bit :: output)

theorem run_phase (src : Fin 6) (copy restore next : Label)
    (hcopy : program copy = copyStmt src copy restore)
    (hrestore : program restore = restoreStmt src restore next)
    (words : Fin 6 → List Bool) (output : List Bool) :
    run (2 * (words src).length + 2)
      (cfg (some copy) none words output []) =
    cfg (some next) none words (words src ++ output) [] := by
  let bits := words src
  have hc := run_copy src copy restore hcopy bits none words output []
  have hr := run_restore src restore next hrestore bits.reverse none
    (Function.update words src []) output
  calc
    run (2 * bits.length + 2) (cfg (some copy) none words output []) =
        run ((bits.length + 1) + (bits.length + 1))
          (cfg (some copy) none (Function.update words src bits) output []) := by
            simp only [bits, Function.update_eq_self]; congr 1; omega
    _ = run (bits.length + 1)
          (cfg (some restore) none (Function.update words src []) output bits.reverse) := by
            rw [run_add, hc, List.append_nil]
    _ = cfg (some next) none words (bits ++ output) [] := by
            simpa only [bits, List.length_reverse, List.reverse_reverse,
              Function.update_self, update_twice, List.append_nil,
              Function.update_eq_self] using hr

private theorem step_append_header (words : Fin 6 → List Bool) (output : List Bool) :
    TM2.step program (cfg (some .appendHeader) none words output []) =
    some (cfg (some .accept) none words ([false,true,true] ++ output) []) := by
  simp [TM2.step, TM2.stepAux, program, cfg, contents]
  funext i
  fin_cases i <;> simp [contents]

private theorem step_branch_header (words : Fin 6 → List Bool) (output : List Bool) :
    TM2.step program (cfg (some .branchHeader) none words output []) =
    some (cfg (some .accept) none words ([true,false,false] ++ output) []) := by
  simp [TM2.step, TM2.stepAux, program, cfg, contents]
  funext i
  fin_cases i <;> simp [contents]

private theorem step_accept (words : Fin 6 → List Bool) (output : List Bool) :
    TM2.step program (cfg (some .accept) none words output []) =
    some (cfg none none words output []) := by
  simp [TM2.step, TM2.stepAux, program, cfg]

def appendClock (left right : List Bool) : Nat :=
  2 * (left.length + right.length) + 6

theorem run_append_words (words : Fin 6 → List Bool) :
    run (appendClock (words 0) (words 1))
      (cfg (some .appendRightCopy) none words [] []) =
    cfg none none words ([false,true,true] ++ words 0 ++ words 1) [] := by
  have hr := run_phase 1 .appendRightCopy .appendRightRestore .appendLeftCopy
    rfl rfl words []
  have hl := run_phase 0 .appendLeftCopy .appendLeftRestore .appendHeader
    rfl rfl words (words 1)
  calc
    run (appendClock (words 0) (words 1))
        (cfg (some .appendRightCopy) none words [] []) =
      run ((2 * (words 1).length + 2) +
        ((2 * (words 0).length + 2) + (1 + 1)))
        (cfg (some .appendRightCopy) none words [] []) := by
          congr 1; simp [appendClock]; omega
    _ = run ((2 * (words 0).length + 2) + (1 + 1))
          (cfg (some .appendLeftCopy) none words (words 1) []) := by
            rw [run_add, hr, List.append_nil]
    _ = run (1 + 1)
          (cfg (some .appendHeader) none words (words 0 ++ words 1) []) := by
            rw [run_add, hl]
    _ = run 1
          (cfg (some .accept) none words
            ([false,true,true] ++ words 0 ++ words 1) []) := by
            rw [run_add, run_succ (step_append_header words
              (words 0 ++ words 1)) 0]
            simp only [run, Function.iterate_zero, id_eq, List.append_assoc]
    _ = cfg none none words ([false,true,true] ++ words 0 ++ words 1) [] := by
            rw [run_succ (step_accept words
              ([false,true,true] ++ words 0 ++ words 1)) 0]
            rfl

def branchClock (words : Fin 6 → List Bool) : Nat :=
  2 * ((words 0).length + (words 1).length + (words 2).length +
    (words 3).length + (words 4).length + (words 5).length) + 14

theorem run_branch_words (words : Fin 6 → List Bool) :
    run (branchClock words)
      (cfg (some .branchThirdCopy) none words [] []) =
    cfg none none words
      ([true,false,false] ++ words 0 ++ words 1 ++ words 2 ++
        words 3 ++ words 4 ++ words 5) [] := by
  have h5 := run_phase 5 .branchThirdCopy .branchThirdRestore .branchSecondCopy
    rfl rfl words []
  have h4 := run_phase 4 .branchSecondCopy .branchSecondRestore .branchFirstCopy
    rfl rfl words (words 5)
  have h3 := run_phase 3 .branchFirstCopy .branchFirstRestore .branchBCopy
    rfl rfl words (words 4 ++ words 5)
  have h2 := run_phase 2 .branchBCopy .branchBRestore .branchACopy
    rfl rfl words (words 3 ++ words 4 ++ words 5)
  have h1 := run_phase 1 .branchACopy .branchARestore .branchNCopy
    rfl rfl words (words 2 ++ words 3 ++ words 4 ++ words 5)
  have h0 := run_phase 0 .branchNCopy .branchNRestore .branchHeader
    rfl rfl words (words 1 ++ words 2 ++ words 3 ++ words 4 ++ words 5)
  calc
    run (branchClock words) (cfg (some .branchThirdCopy) none words [] []) =
      run ((2 * (words 5).length + 2) +
        ((2 * (words 4).length + 2) +
        ((2 * (words 3).length + 2) +
        ((2 * (words 2).length + 2) +
        ((2 * (words 1).length + 2) +
        ((2 * (words 0).length + 2) + (1 + 1)))))))
        (cfg (some .branchThirdCopy) none words [] []) := by
          congr 1; simp [branchClock]; omega
    _ = run ((2 * (words 4).length + 2) +
        ((2 * (words 3).length + 2) +
        ((2 * (words 2).length + 2) +
        ((2 * (words 1).length + 2) +
        ((2 * (words 0).length + 2) + (1 + 1))))))
        (cfg (some .branchSecondCopy) none words (words 5) []) := by
          rw [run_add, h5, List.append_nil]
    _ = run ((2 * (words 3).length + 2) +
        ((2 * (words 2).length + 2) +
        ((2 * (words 1).length + 2) +
        ((2 * (words 0).length + 2) + (1 + 1)))))
        (cfg (some .branchFirstCopy) none words (words 4 ++ words 5) []) := by
          rw [run_add, h4]
    _ = run ((2 * (words 2).length + 2) +
        ((2 * (words 1).length + 2) +
        ((2 * (words 0).length + 2) + (1 + 1))))
        (cfg (some .branchBCopy) none words
          (words 3 ++ words 4 ++ words 5) []) := by
          rw [run_add, h3]
          simp only [List.append_assoc]
    _ = run ((2 * (words 1).length + 2) +
        ((2 * (words 0).length + 2) + (1 + 1)))
        (cfg (some .branchACopy) none words
          (words 2 ++ words 3 ++ words 4 ++ words 5) []) := by
          rw [run_add, h2]
          simp only [List.append_assoc]
    _ = run ((2 * (words 0).length + 2) + (1 + 1))
        (cfg (some .branchNCopy) none words
          (words 1 ++ words 2 ++ words 3 ++ words 4 ++ words 5) []) := by
          rw [run_add, h1]
          simp only [List.append_assoc]
    _ = run (1 + 1)
        (cfg (some .branchHeader) none words
          (words 0 ++ words 1 ++ words 2 ++ words 3 ++ words 4 ++ words 5) []) := by
          rw [run_add, h0]
          simp only [List.append_assoc]
    _ = run 1
        (cfg (some .accept) none words
          ([true,false,false] ++ words 0 ++ words 1 ++ words 2 ++
            words 3 ++ words 4 ++ words 5) []) := by
          rw [run_add, run_succ (step_branch_header words
            (words 0 ++ words 1 ++ words 2 ++ words 3 ++ words 4 ++ words 5)) 0]
          simp only [run, Function.iterate_zero, id_eq, List.append_assoc]
    _ = cfg none none words
          ([true,false,false] ++ words 0 ++ words 1 ++ words 2 ++
            words 3 ++ words 4 ++ words 5) [] := by
          rw [run_succ (step_accept words
            ([true,false,false] ++ words 0 ++ words 1 ++ words 2 ++
              words 3 ++ words 4 ++ words 5)) 0]
          rfl

def appendInputs (left right : Code) : Fin 6 → List Bool :=
  fun i => if i = 0 then encodeCode left else
    if i = 1 then encodeCode right else []

def branchInputs (n a b : Nat) (first second third : Code) :
    Fin 6 → List Bool :=
  fun i => if i = 0 then unary n else if i = 1 then unary a else
    if i = 2 then unary b else if i = 3 then encodeCode first else
    if i = 4 then encodeCode second else encodeCode third

theorem run_append (left right : Code) :
    run (appendClock (encodeCode left) (encodeCode right))
      (cfg (some .appendRightCopy) none (appendInputs left right) [] []) =
    cfg none none (appendInputs left right) (encodeCode (.append left right)) [] := by
  simpa [appendInputs, encodeCode, List.append_assoc] using
    run_append_words (appendInputs left right)

theorem run_branch (n a b : Nat) (first second third : Code) :
    run (branchClock (branchInputs n a b first second third))
      (cfg (some .branchThirdCopy) none
        (branchInputs n a b first second third) [] []) =
    cfg none none (branchInputs n a b first second third)
      (encodeCode (.branch3 n a b first second third)) [] := by
  simpa [branchInputs, encodeCode, List.append_assoc] using
    run_branch_words (branchInputs n a b first second third)

theorem appendClock_polynomial (left right : Code) :
    appendClock (encodeCode left) (encodeCode right) ≤
      4 * (codeSize left + codeSize right + 2) := by
  rw [appendClock, encodeCode_length, encodeCode_length]
  omega

theorem branchClock_polynomial (n a b : Nat)
    (first second third : Code) :
    branchClock (branchInputs n a b first second third) ≤
      4 * (n + a + b + codeSize first + codeSize second +
        codeSize third + 5) := by
  simp [branchClock, branchInputs, unary_length, encodeCode_length]
  omega

theorem run_append_empty :
    run (appendClock (encodeCode (.emit [])) (encodeCode (.emit [])))
      (cfg (some .appendRightCopy) none
        (appendInputs (.emit []) (.emit [])) [] []) =
    cfg none none (appendInputs (.emit []) (.emit []))
      (encodeCode (.append (.emit []) (.emit []))) [] :=
  run_append (.emit []) (.emit [])

theorem run_branch_zero :
    run (branchClock (branchInputs 0 0 0 (.emit []) (.emit []) (.emit [])))
      (cfg (some .branchThirdCopy) none
        (branchInputs 0 0 0 (.emit []) (.emit []) (.emit [])) [] []) =
    cfg none none (branchInputs 0 0 0 (.emit []) (.emit []) (.emit []))
      (encodeCode (.branch3 0 0 0 (.emit []) (.emit []) (.emit []))) [] :=
  run_branch 0 0 0 (.emit []) (.emit []) (.emit [])

theorem run_append_literals (left right : List Bool) :
    run (appendClock (encodeCode (.emit left)) (encodeCode (.emit right)))
      (cfg (some .appendRightCopy) none
        (appendInputs (.emit left) (.emit right)) [] []) =
    cfg none none (appendInputs (.emit left) (.emit right))
      (encodeCode (.append (.emit left) (.emit right))) [] :=
  run_append (.emit left) (.emit right)

theorem run_branch_literals (n a b : Nat)
    (first second third : List Bool) :
    run (branchClock (branchInputs n a b
        (.emit first) (.emit second) (.emit third)))
      (cfg (some .branchThirdCopy) none
        (branchInputs n a b (.emit first) (.emit second) (.emit third)) [] []) =
    cfg none none (branchInputs n a b
        (.emit first) (.emit second) (.emit third))
      (encodeCode (.branch3 n a b
        (.emit first) (.emit second) (.emit third))) [] :=
  run_branch n a b (.emit first) (.emit second) (.emit third)

noncomputable def appendMachine :=
  ofFinite (0 : Fin 8) (6 : Fin 8) Label.appendRightCopy (none : Control) program

noncomputable def branchMachine :=
  ofFinite (0 : Fin 8) (6 : Fin 8) Label.branchThirdCopy (none : Control) program

theorem appendMachine_run (left right : Code) :
    appendMachine.run (appendClock (encodeCode left) (encodeCode right))
      (renameCfg (Fintype.equivFin (Fin 8)) (Fintype.equivFin Label)
        (Fintype.equivFin Control)
        (cfg (some .appendRightCopy) none (appendInputs left right) [] [])) =
      renameCfg (Fintype.equivFin (Fin 8)) (Fintype.equivFin Label)
        (Fintype.equivFin Control)
        (cfg none none (appendInputs left right)
          (encodeCode (.append left right)) []) := by
  exact (ofFinite_run (0 : Fin 8) (6 : Fin 8) Label.appendRightCopy
    (none : Control) program
    (cfg (some .appendRightCopy) none (appendInputs left right) [] [])
    (appendClock (encodeCode left) (encodeCode right))).trans
    (congrArg (renameCfg (Fintype.equivFin (Fin 8)) (Fintype.equivFin Label)
      (Fintype.equivFin Control)) (run_append left right))

theorem branchMachine_run (n a b : Nat) (first second third : Code) :
    branchMachine.run (branchClock (branchInputs n a b first second third))
      (renameCfg (Fintype.equivFin (Fin 8)) (Fintype.equivFin Label)
        (Fintype.equivFin Control)
        (cfg (some .branchThirdCopy) none
          (branchInputs n a b first second third) [] [])) =
      renameCfg (Fintype.equivFin (Fin 8)) (Fintype.equivFin Label)
        (Fintype.equivFin Control)
        (cfg none none (branchInputs n a b first second third)
          (encodeCode (.branch3 n a b first second third)) []) := by
  exact (ofFinite_run (0 : Fin 8) (6 : Fin 8) Label.branchThirdCopy
    (none : Control) program
    (cfg (some .branchThirdCopy) none
      (branchInputs n a b first second third) [] [])
    (branchClock (branchInputs n a b first second third))).trans
    (congrArg (renameCfg (Fintype.equivFin (Fin 8)) (Fintype.equivFin Label)
      (Fintype.equivFin Control))
      (run_branch n a b first second third))

#print axioms run_append
#print axioms run_branch
#print axioms run_append_empty
#print axioms run_branch_zero
#print axioms run_append_literals
#print axioms run_branch_literals
#print axioms appendClock_polynomial
#print axioms branchClock_polynomial
#print axioms appendMachine_run
#print axioms branchMachine_run

end Paper2.CodeConstructorMachine
