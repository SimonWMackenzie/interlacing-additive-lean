import Paper2.GeneratorSerialization
import EthInapproximability.CurrentPaper.BitMachineEncoding

/-! Physical source-preserving construction of right-nested copies syntax. -/

namespace Paper2.CodeCopiesMachine

open Turing Turing.TM2.Stmt
open EthInapproximability.CurrentPaper.BitMachineEncoding
open Paper2.GeneratorCode Paper2.GeneratorSerialization

inductive Label where
  | initialize | count | copy | restore | header | reverse | accept | reject
  deriving DecidableEq, Fintype

abbrev Control := Option Bool

def program : Label → TM2.Stmt (fun _ : Fin 5 => Bool) Label Control
  | .initialize =>
      push 2 (fun _ => false)
        (push 2 (fun _ => false)
          (push 2 (fun _ => false)
            (push 2 (fun _ => false) (goto (fun _ => .count)))))
  | .count =>
      pop 0 (fun _ b => b)
        (branch Option.isSome
          (branch (fun b => b.getD false)
            (goto (fun _ => .copy)) (goto (fun _ => .accept)))
          (goto (fun _ => .reject)))
  | .copy =>
      pop 1 (fun _ b => b)
        (branch Option.isSome
          (push 3 (fun b => b.getD false)
            (goto (fun _ => .copy)))
          (goto (fun _ => .restore)))
  | .restore =>
      pop 3 (fun _ b => b)
        (branch Option.isSome
          (push 1 (fun b => b.getD false)
            (push 2 (fun b => b.getD false) (goto (fun _ => .restore))))
          (goto (fun _ => .header)))
  | .header =>
      push 2 (fun _ => true)
        (push 2 (fun _ => true)
          (push 2 (fun _ => false) (goto (fun _ => .count))))
  | .reverse =>
      pop 2 (fun _ b => b)
        (branch Option.isSome
          (push 4 (fun b => b.getD false) (goto (fun _ => .reverse)))
          (goto (fun _ => .accept)))
  | .accept => load (fun _ => none) halt
  | .reject => halt

def contents (count source acc scratch output : List Bool) : Fin 5 → List Bool :=
  fun i => if i = 0 then count else if i = 1 then source else
    if i = 2 then acc else if i = 3 then scratch else output

def cfg (label : Option Label) (control : Control)
    (count source acc scratch output : List Bool) :
    TM2.Cfg (fun _ : Fin 5 => Bool) Label Control :=
  ⟨label, control, contents count source acc scratch output⟩

def initial (count source : List Bool) :
    TM2.Cfg (fun _ : Fin 5 => Bool) Label Control :=
  cfg (some .initialize) none count source [] [] []

def run (steps : Nat) (c : TM2.Cfg (fun _ : Fin 5 => Bool) Label Control) :=
  ((advance program)^[steps]) c

private theorem run_succ {c d : TM2.Cfg (fun _ : Fin 5 => Bool) Label Control}
    (h : TM2.step program c = some d) (n : Nat) :
    run (n + 1) c = run n d := by
  simp only [run, Function.iterate_succ_apply, advance, h, Option.getD_some]

private theorem step_initialize (count source : List Bool) :
    TM2.step program (initial count source) =
      some (cfg (some .count) none count source [false,false,false,false] [] []) := by
  simp [TM2.step, TM2.stepAux, program, initial, cfg, contents]
  funext i
  fin_cases i <;> rfl

private theorem step_count_true (count source acc : List Bool) :
    TM2.step program (cfg (some .count) none (true :: count) source acc [] []) =
      some (cfg (some .copy) (some true) count source acc [] []) := by
  simp [TM2.step, TM2.stepAux, program, cfg, contents]
  funext i
  fin_cases i <;> rfl

private theorem step_count_false (source acc : List Bool) :
    TM2.step program (cfg (some .count) none [false] source acc [] []) =
      some (cfg (some .accept) (some false) [] source acc [] []) := by
  simp [TM2.step, TM2.stepAux, program, cfg, contents]
  funext i
  fin_cases i <;> rfl

private theorem step_count_empty (source acc : List Bool) :
    TM2.step program (cfg (some .count) none [] source acc [] []) =
      some (cfg (some .reject) none [] source acc [] []) := by
  simp [TM2.step, TM2.stepAux, program, cfg, contents]

private theorem step_copy_cons (bit : Bool) (control : Control)
    (count source acc scratch : List Bool) :
    TM2.step program (cfg (some .copy) control
      count (bit :: source) acc scratch []) =
      some (cfg (some .copy) (some bit)
        count source acc (bit :: scratch) []) := by
  simp [TM2.step, TM2.stepAux, program, cfg, contents]
  funext i
  fin_cases i <;> rfl

private theorem step_copy_nil (control : Control)
    (count acc scratch : List Bool) :
    TM2.step program (cfg (some .copy) control count [] acc scratch []) =
      some (cfg (some .restore) none count [] acc scratch []) := by
  simp [TM2.step, TM2.stepAux, program, cfg, contents]

private theorem step_restore_cons (bit : Bool)
    (control : Control) (count source acc scratch : List Bool) :
    TM2.step program (cfg (some .restore) control
      count source acc (bit :: scratch) []) =
      some (cfg (some .restore) (some bit)
        count (bit :: source) (bit :: acc) scratch []) := by
  simp [TM2.step, TM2.stepAux, program, cfg, contents]
  funext i
  fin_cases i <;> rfl

private theorem step_restore_nil (control : Control)
    (count source acc : List Bool) :
    TM2.step program (cfg (some .restore) control count source acc [] []) =
      some (cfg (some .header) none count source acc [] []) := by
  simp [TM2.step, TM2.stepAux, program, cfg, contents]

private theorem step_header (count source acc : List Bool) :
    TM2.step program (cfg (some .header) none count source acc [] []) =
      some (cfg (some .count) none count source
        ([false,true,true] ++ acc) [] []) := by
  simp [TM2.step, TM2.stepAux, program, cfg, contents]
  funext i
  fin_cases i <;> rfl

private theorem step_reverse_cons (bit : Bool)
    (control : Control) (source acc output : List Bool) :
    TM2.step program (cfg (some .reverse) control
      [] source (bit :: acc) [] output) =
      some (cfg (some .reverse) (some bit)
        [] source acc [] (bit :: output)) := by
  simp [TM2.step, TM2.stepAux, program, cfg, contents]
  funext i
  fin_cases i <;> rfl

private theorem step_reverse_nil (control : Control) (source output : List Bool) :
    TM2.step program (cfg (some .reverse) control [] source [] [] output) =
      some (cfg (some .accept) none [] source [] [] output) := by
  simp [TM2.step, TM2.stepAux, program, cfg, contents]

private theorem step_accept (control : Control) (source acc : List Bool) :
    TM2.step program (cfg (some .accept) control [] source acc [] []) =
      some (cfg none none [] source acc [] []) := by
  simp [TM2.step, TM2.stepAux, program, cfg]

private theorem run_add (a b : Nat)
    (c : TM2.Cfg (fun _ : Fin 5 => Bool) Label Control) :
    run (a + b) c = run b (run a c) := by
  rw [Nat.add_comm a b]
  simp only [run, Function.iterate_add_apply]

theorem run_copy (bits count acc scratch : List Bool) (control : Control) :
    run (bits.length + 1) (cfg (some .copy) control count bits acc scratch []) =
      cfg (some .restore) none count []
        acc (bits.reverse ++ scratch) [] := by
  induction bits generalizing acc scratch control with
  | nil =>
      simpa only [List.length_nil, zero_add, List.reverse_nil, List.nil_append] using
        run_succ (step_copy_nil control count acc scratch) 0
  | cons bit bits ih =>
      rw [show (bit :: bits).length + 1 = (bits.length + 1) + 1 by simp]
      rw [run_succ (step_copy_cons bit control count bits acc scratch) (bits.length + 1)]
      simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using
        ih acc (bit :: scratch) (some bit)

theorem run_restore (scratch count source acc : List Bool) (control : Control) :
    run (scratch.length + 1)
      (cfg (some .restore) control count source acc scratch []) =
      cfg (some .header) none count
        (scratch.reverse ++ source) (scratch.reverse ++ acc) [] [] := by
  induction scratch generalizing source acc control with
  | nil =>
      simpa only [List.length_nil, zero_add, List.reverse_nil, List.nil_append] using
        run_succ (step_restore_nil control count source acc) 0
  | cons bit scratch ih =>
      rw [show (bit :: scratch).length + 1 = (scratch.length + 1) + 1 by simp]
      rw [run_succ (step_restore_cons bit control count source acc scratch)
        (scratch.length + 1)]
      simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using
        ih (bit :: source) (bit :: acc) (some bit)

theorem run_reverse (bits source output : List Bool) (control : Control) :
    run (bits.length + 1)
      (cfg (some .reverse) control [] source bits [] output) =
      cfg (some .accept) none [] source [] [] (bits.reverse ++ output) := by
  induction bits generalizing output control with
  | nil =>
      simpa only [List.length_nil, zero_add, List.reverse_nil, List.nil_append] using
        run_succ (step_reverse_nil control source output) 0
  | cons bit bits ih =>
      rw [show (bit :: bits).length + 1 = (bits.length + 1) + 1 by simp]
      rw [run_succ (step_reverse_cons bit control source bits output)
        (bits.length + 1)]
      simpa only [List.reverse_cons, List.append_assoc, List.singleton_append] using
        ih (bit :: output) (some bit)

def block (word : List Bool) : List Bool := [false,true,true] ++ word

def repeatPrefix : Nat → List Bool → List Bool
  | 0, _ => []
  | n + 1, word => block word ++ repeatPrefix n word

theorem repeatPrefix_commute (n : Nat) (word : List Bool) :
    repeatPrefix n word ++ block word = block word ++ repeatPrefix n word := by
  induction n with
  | zero => simp [repeatPrefix]
  | succ n ih => simp only [repeatPrefix, List.append_assoc, ih]

theorem run_iteration (count word acc : List Bool) :
    run (2 * word.length + 4)
      (cfg (some .count) none (true :: count) word acc [] []) =
      cfg (some .count) none count word (block word ++ acc) [] [] := by
  have hcount := step_count_true count word acc
  have hcopy := run_copy word count acc [] (some true)
  have hrestore := run_restore word.reverse count [] acc none
  have hrestore' : run (word.length + 1)
      (cfg (some .restore) none count [] acc word.reverse []) =
        cfg (some .header) none count word (word ++ acc) [] [] := by
    simpa only [List.length_reverse, List.reverse_reverse, List.append_nil,
      List.nil_append] using hrestore
  have hheader := step_header count word (word ++ acc)
  calc
    run (2 * word.length + 4)
        (cfg (some .count) none (true :: count) word acc [] []) =
      run (1 + ((word.length + 1) + ((word.length + 1) + 1)))
        (cfg (some .count) none (true :: count) word acc [] []) := by congr 1; omega
    _ = run ((word.length + 1) + ((word.length + 1) + 1))
          (cfg (some .copy) (some true) count word acc [] []) := by
            rw [run_add, run_succ hcount 0]
            rfl
    _ = run ((word.length + 1) + 1)
          (cfg (some .restore) none count [] acc word.reverse []) := by
            rw [run_add, hcopy, List.append_nil]
    _ = run 1 (cfg (some .header) none count word (word ++ acc) [] []) := by
            rw [run_add, hrestore']
    _ = cfg (some .count) none count word (block word ++ acc) [] [] := by
            rw [run_succ hheader 0]
            rfl

theorem run_repetitions (n : Nat) (tail word acc : List Bool) :
    run (n * (2 * word.length + 4))
      (cfg (some .count) none (List.replicate n true ++ tail) word acc [] []) =
      cfg (some .count) none tail word (repeatPrefix n word ++ acc) [] [] := by
  induction n generalizing acc with
  | zero => simp [run, repeatPrefix]
  | succ n ih =>
      rw [show (n + 1) * (2 * word.length + 4) =
        (2 * word.length + 4) + n * (2 * word.length + 4) by
          simp [Nat.succ_mul, Nat.add_comm]]
      rw [run_add]
      simp only [List.replicate_succ, List.cons_append]
      change run (n * (2 * word.length + 4))
        (run (2 * word.length + 4)
          (cfg (some .count) none (true :: List.replicate n true ++ tail)
            word acc [] [])) = _
      rw [show (true :: List.replicate n true) ++ tail =
        true :: (List.replicate n true ++ tail) by rfl]
      rw [run_iteration]
      rw [ih]
      simp only [repeatPrefix, List.append_assoc]
      rw [← List.append_assoc (repeatPrefix n word) (block word) acc,
        repeatPrefix_commute, List.append_assoc]

theorem encode_copies (n : Nat) (c : Code) :
    encodeCode (copies n c) =
      repeatPrefix n (encodeCode c) ++ [false,false,false,false] := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [copies, encodeCode, repeatPrefix, block, ih]
      simp only [List.append_assoc]

theorem codeSize_copies (n : Nat) (c : Code) :
    codeSize (copies n c) = 4 + n * (3 + codeSize c) := by
  induction n with
  | zero => simp [copies, codeSize]
  | succ n ih =>
      simp only [copies, codeSize, ih, Nat.succ_mul]
      omega

def clock (n : Nat) (c : Code) : Nat :=
  3 + n * (2 * codeSize c + 4)

theorem run_copies (n : Nat) (c : Code) :
    run (clock n c) (initial (unary n) (encodeCode c)) =
      cfg none none [] (encodeCode c) (encodeCode (copies n c)) [] [] := by
  let word := encodeCode c
  have hw : word.length = codeSize c := encodeCode_length c
  have hinit := step_initialize (unary n) word
  have hreps := run_repetitions n [false] word [false,false,false,false]
  have henc := encode_copies n c
  have hfalse := step_count_false word (encodeCode (copies n c))
  have haccept := step_accept (some false) word (encodeCode (copies n c))
  calc
    run (clock n c) (initial (unary n) (encodeCode c)) =
      run (1 + (n * (2 * word.length + 4) + 1 + 1))
        (initial (unary n) word) := by simp only [clock, hw]; congr 1; omega
    _ = run (n * (2 * word.length + 4) + 1 + 1)
          (cfg (some .count) none (unary n) word [false,false,false,false] [] []) := by
            rw [run_add, run_succ hinit 0]
            rfl
    _ = run (1 + 1)
          (cfg (some .count) none [false] word
            (encodeCode (copies n c)) [] []) := by
            rw [show n * (2 * word.length + 4) + 1 + 1 =
              n * (2 * word.length + 4) + (1 + 1) by omega, run_add]
            rw [show unary n = List.replicate n true ++ [false] by rfl]
            rw [hreps]
            rw [← henc]
    _ = run 1 (cfg (some .accept) (some false) [] word
          (encodeCode (copies n c)) [] []) := by
            rw [run_add, run_succ hfalse 0]
            rfl
    _ = cfg none none [] word (encodeCode (copies n c)) [] [] := by
            rw [run_succ haccept 0]
            rfl

private theorem step_reject (source acc : List Bool) :
    TM2.step program (cfg (some .reject) none [] source acc [] []) =
      some (cfg none none [] source acc [] []) := by
  simp [TM2.step, TM2.stepAux, program, cfg]

theorem run_empty_count (word : List Bool) :
    run 3 (initial [] word) =
      cfg none none [] word [false,false,false,false] [] [] := by
  rw [show (3 : Nat) = 1 + 1 + 1 by omega]
  rw [run_succ (step_initialize [] word) (1 + 1)]
  rw [run_succ (step_count_empty word [false,false,false,false]) 1]
  rw [run_succ (step_reject word [false,false,false,false]) 0]
  rfl

theorem run_zero (c : Code) :
    run (clock 0 c) (initial (unary 0) (encodeCode c)) =
      cfg none none [] (encodeCode c) (encodeCode (.emit [])) [] [] := by
  simpa only [copies] using run_copies 0 c

theorem run_emit_literal (n : Nat) (bits : List Bool) :
    run (clock n (.emit bits)) (initial (unary n) (encodeCode (.emit bits))) =
      cfg none none [] (encodeCode (.emit bits))
        (encodeCode (copies n (.emit bits))) [] [] := run_copies n (.emit bits)

theorem clock_polynomial (n : Nat) (c : Code) :
    clock n c ≤ 4 * (n + 1) * (codeSize c + 1) := by
  unfold clock
  nlinarith

theorem output_size_polynomial (n : Nat) (c : Code) :
    codeSize (copies n c) ≤ 4 * (n + 1) * (codeSize c + 1) := by
  rw [codeSize_copies]
  nlinarith

/-- Fixed finite ordinal machine. Its caller supplies the unary count in
stack 0 and the preserved serialized code in stack 1; output is stack 2. -/
noncomputable def machine :=
  ofFinite (0 : Fin 5) (2 : Fin 5) Label.initialize (none : Control) program

theorem machine_run_copies (n : Nat) (c : Code) :
    machine.run (clock n c)
      (renameCfg (Fintype.equivFin (Fin 5)) (Fintype.equivFin Label)
        (Fintype.equivFin Control) (initial (unary n) (encodeCode c))) =
      renameCfg (Fintype.equivFin (Fin 5)) (Fintype.equivFin Label)
        (Fintype.equivFin Control)
        (cfg none none [] (encodeCode c) (encodeCode (copies n c)) [] []) := by
  exact (ofFinite_run (0 : Fin 5) (2 : Fin 5) Label.initialize (none : Control)
    program (initial (unary n) (encodeCode c)) (clock n c)).trans
    (congrArg (renameCfg (Fintype.equivFin (Fin 5)) (Fintype.equivFin Label)
      (Fintype.equivFin Control)) (run_copies n c))

#print axioms run_copies
#print axioms run_empty_count
#print axioms run_zero
#print axioms run_emit_literal
#print axioms clock_polynomial
#print axioms machine_run_copies

end Paper2.CodeCopiesMachine
