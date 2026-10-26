import EthInapproximability.CurrentPaper.BitMachineEncoding
import Mathlib.Tactic

/-!
# Literal unary multiplication for matrix addresses

The machine reads `true^n ++ false :: true^m` and writes `true^(n*m)`.
Every iteration copies one unary operand onto the output and restores that
operand from scratch. All registers and instruction labels are finite;
the only unbounded data are lists of Booleans on four stacks.

This is address arithmetic for the full materializer, not a unit-cost
arithmetic assumption. Raw phase theorems permit use inside a larger
controller. Preserve inputs by the separately proved copy primitive when
needed; this multiplication machine intentionally consumes its own copies.
-/

namespace EthInapproximability.CurrentPaper.MatrixUnaryArithmetic

open Turing Turing.TM2.Stmt BitMachineEncoding

inductive Label where
  | parse | outer | scan | restore | clear
  deriving DecidableEq, Fintype

def program : Label → TM2.Stmt (fun _ : Fin 4 => Bool) Label Bool
  | .parse => pop 0 (fun _ b => b.getD false)
      (branch id (push 1 (fun _ => true) (goto (fun _ => .parse)))
        (goto (fun _ => .outer)))
  | .outer => pop 1 (fun _ b => b.isSome)
      (branch id (goto (fun _ => .scan)) (goto (fun _ => .clear)))
  | .scan => pop 0 (fun _ b => b.isSome)
      (branch id (push 2 (fun _ => true) (push 3 (fun _ => true) (goto (fun _ => .scan))))
        (goto (fun _ => .restore)))
  | .restore => pop 3 (fun _ b => b.isSome)
      (branch id (push 0 (fun _ => true) (goto (fun _ => .restore)))
        (goto (fun _ => .outer)))
  | .clear => pop 0 (fun _ b => b.isSome)
      (branch id (goto (fun _ => .clear)) (load (fun _ => false) halt))

def stackContents (q counter output scratch : List Bool) : Fin 4 → List Bool :=
  fun k => if k = 0 then q else if k = 1 then counter else if k = 2 then output else scratch

@[simp] private theorem s0 (q c o b : List Bool) : stackContents q c o b 0 = q := rfl
@[simp] private theorem s1 (q c o b : List Bool) : stackContents q c o b 1 = c := rfl
@[simp] private theorem s2 (q c o b : List Bool) : stackContents q c o b 2 = o := rfl
@[simp] private theorem s3 (q c o b : List Bool) : stackContents q c o b 3 = b := rfl

def cfg (l : Option Label) (s : Bool) (q c o b : List Bool) :
    TM2.Cfg (fun _ : Fin 4 => Bool) Label Bool := ⟨l, s, stackContents q c o b⟩

def run (n : ℕ) (c : TM2.Cfg (fun _ : Fin 4 => Bool) Label Bool) :=
  ((advance program)^[n]) c

private theorem run_succ {c d : TM2.Cfg (fun _ : Fin 4 => Bool) Label Bool}
    (h : TM2.step program c = some d) (n : ℕ) : run (n + 1) c = run n d := by
  simp only [run, Function.iterate_succ_apply, advance, h, Option.getD_some]

private theorem run_add {c d : TM2.Cfg (fun _ : Fin 4 => Bool) Label Bool}
    {m : ℕ} (h : run m c = d) (n : ℕ) : run (m + n) c = run n d := by
  rw [Nat.add_comm m n]
  simp only [run, Function.iterate_add_apply] at h ⊢
  rw [h]

private theorem parse_true (s : Bool) (q c o b : List Bool) :
    TM2.step program (cfg (some .parse) s (true :: q) c o b) =
      some (cfg (some .parse) true q (true :: c) o b) := by
  apply congrArg (fun S => some (⟨some .parse, true, S⟩ : TM2.Cfg (fun _ : Fin 4 => Bool) Label Bool))
  funext k
  fin_cases k <;> rfl

private theorem parse_false (s : Bool) (q c o b : List Bool) :
    TM2.step program (cfg (some .parse) s (false :: q) c o b) =
      some (cfg (some .outer) false q c o b) := by
  apply congrArg (fun S => some (⟨some .outer, false, S⟩ : TM2.Cfg (fun _ : Fin 4 => Bool) Label Bool))
  funext k
  fin_cases k <;> rfl

private theorem outer_cons (s : Bool) (q c o : List Bool) :
    TM2.step program (cfg (some .outer) s q (true :: c) o []) =
      some (cfg (some .scan) true q c o []) := by
  apply congrArg (fun S => some (⟨some .scan, true, S⟩ : TM2.Cfg (fun _ : Fin 4 => Bool) Label Bool))
  funext k
  fin_cases k <;> rfl

private theorem outer_nil (s : Bool) (q o : List Bool) :
    TM2.step program (cfg (some .outer) s q [] o []) =
      some (cfg (some .clear) false q [] o []) := by
  simp [TM2.step, TM2.stepAux, program, cfg]

private theorem scan_cons (s bit : Bool) (q c o b : List Bool) :
    TM2.step program (cfg (some .scan) s (bit :: q) c o b) =
      some (cfg (some .scan) true q c (true :: o) (true :: b)) := by
  apply congrArg (fun S => some (⟨some .scan, true, S⟩ : TM2.Cfg (fun _ : Fin 4 => Bool) Label Bool))
  funext k
  fin_cases k <;> rfl

private theorem scan_nil (s : Bool) (c o b : List Bool) :
    TM2.step program (cfg (some .scan) s [] c o b) =
      some (cfg (some .restore) false [] c o b) := by
  simp [TM2.step, TM2.stepAux, program, cfg]

private theorem restore_cons (s : Bool) (q c o b : List Bool) :
    TM2.step program (cfg (some .restore) s q c o (true :: b)) =
      some (cfg (some .restore) true (true :: q) c o b) := by
  apply congrArg (fun S => some (⟨some .restore, true, S⟩ : TM2.Cfg (fun _ : Fin 4 => Bool) Label Bool))
  funext k
  fin_cases k <;> rfl

private theorem restore_nil (s : Bool) (q c o : List Bool) :
    TM2.step program (cfg (some .restore) s q c o []) =
      some (cfg (some .outer) false q c o []) := by
  simp [TM2.step, TM2.stepAux, program, cfg]

private theorem clear_cons (s bit : Bool) (q o : List Bool) :
    TM2.step program (cfg (some .clear) s (bit :: q) [] o []) =
      some (cfg (some .clear) true q [] o []) := by
  apply congrArg (fun S => some (⟨some .clear, true, S⟩ : TM2.Cfg (fun _ : Fin 4 => Bool) Label Bool))
  funext k
  fin_cases k <;> rfl

private theorem clear_nil (s : Bool) (o : List Bool) :
    TM2.step program (cfg (some .clear) s [] [] o []) = some (cfg none false [] [] o []) := by
  simp [TM2.step, TM2.stepAux, program, cfg]

theorem parse_correct (n k : ℕ) (s : Bool) (q o b : List Bool) :
    run (n + 1) (cfg (some .parse) s (List.replicate n true ++ false :: q)
      (List.replicate k true) o b) =
      cfg (some .outer) false q (List.replicate (n + k) true) o b := by
  induction n generalizing k s with
  | zero => simpa using run_succ (parse_false s q (List.replicate k true) o b) 0
  | succ n ih =>
      rw [List.replicate_succ, List.cons_append, run_succ (parse_true _ _ _ _ _) _]
      simpa only [← List.replicate_succ, Nat.add_assoc, Nat.add_comm 1 k] using ih (k + 1) true

theorem scan_correct (q c : List Bool) (o b : ℕ) (s : Bool) :
    run (q.length + 1) (cfg (some .scan) s q c (List.replicate o true) (List.replicate b true)) =
      cfg (some .restore) false [] c (List.replicate (q.length + o) true)
        (List.replicate (q.length + b) true) := by
  induction q generalizing o b s with
  | nil => simpa using run_succ (scan_nil s c (List.replicate o true) (List.replicate b true)) 0
  | cons bit q ih =>
      rw [List.length_cons, run_succ (scan_cons _ _ _ _ _ _) _]
      simpa only [← List.replicate_succ, Nat.add_assoc, Nat.add_comm 1 o, Nat.add_comm 1 b] using
        ih (o + 1) (b + 1) true

theorem restore_correct (n m : ℕ) (s : Bool) (c o : List Bool) :
    run (n + 1) (cfg (some .restore) s (List.replicate m true) c o (List.replicate n true)) =
      cfg (some .outer) false (List.replicate (n + m) true) c o [] := by
  induction n generalizing m s with
  | zero => simpa using run_succ (restore_nil s (List.replicate m true) c o) 0
  | succ n ih =>
      rw [List.replicate_succ, run_succ (restore_cons _ _ _ _ _) _]
      simpa only [← List.replicate_succ, Nat.add_assoc, Nat.add_comm 1 m] using ih (m + 1) true

theorem outer_correct (n m o : ℕ) (s : Bool) :
    run (n * (2 * m + 3) + 1)
      (cfg (some .outer) s (List.replicate m true) (List.replicate n true)
        (List.replicate o true) []) =
      cfg (some .clear) false (List.replicate m true) [] (List.replicate (n * m + o) true) [] := by
  induction n generalizing o s with
  | zero => simpa using run_succ (outer_nil s (List.replicate m true) (List.replicate o true)) 0
  | succ n ih =>
      have h₁ := run_succ (outer_cons s (List.replicate m true) (List.replicate n true)
        (List.replicate o true)) 0
      have h₂ := scan_correct (List.replicate m true) (List.replicate n true) o 0 true
      simp only [List.length_replicate, List.replicate_zero, Nat.add_zero] at h₂
      have h₃ := restore_correct m 0 false (List.replicate n true) (List.replicate (m + o) true)
      simp only [List.replicate_zero, Nat.add_zero] at h₃
      have h₄ := ih (m + o) false
      have h₁₂ := (run_add h₁ (m + 1)).trans h₂
      have h₁₂₃ := (run_add h₁₂ (m + 1)).trans h₃
      have h := (run_add h₁₂₃ (n * (2 * m + 3) + 1)).trans h₄
      have ht : 1 + (m + 1) + (m + 1) + (n * (2 * m + 3) + 1) =
          (n + 1) * (2 * m + 3) + 1 := by ring
      simp only [Nat.zero_add] at h
      rw [ht] at h
      simpa only [← List.replicate_succ, Nat.add_mul, Nat.one_mul, Nat.add_assoc] using h

theorem clear_correct (q o : List Bool) (s : Bool) :
    run (q.length + 1) (cfg (some .clear) s q [] o []) = cfg none false [] [] o [] := by
  induction q generalizing s with
  | nil => exact run_succ (clear_nil s o) 0
  | cons b q ih =>
      rw [List.length_cons, run_succ (clear_cons _ _ _ _) _]
      exact ih true

def encodeInput (n m : ℕ) : List Bool := List.replicate n true ++ false :: List.replicate m true
def exactTime (n m : ℕ) : ℕ := 2 * n * m + 4 * n + m + 3

theorem run_correct (n m : ℕ) :
    run (exactTime n m) (cfg (some .parse) false (encodeInput n m) [] [] []) =
      cfg none false [] [] (List.replicate (n * m) true) [] := by
  have h₁ := parse_correct n 0 false (List.replicate m true) [] []
  have h₂ := outer_correct n m 0 false
  have h₃ := clear_correct (List.replicate m true) (List.replicate (n * m) true) false
  simp only [List.replicate_zero, Nat.add_zero] at h₁ h₂
  simp only [List.length_replicate] at h₃
  have h := (run_add ((run_add h₁ (n * (2 * m + 3) + 1)).trans h₂) (m + 1)).trans h₃
  have ht : (n + 1) + (n * (2 * m + 3) + 1) + (m + 1) = exactTime n m := by
    unfold exactTime
    ring
  simpa only [ht, encodeInput] using h

theorem exactTime_bound (n m : ℕ) : exactTime n m ≤ 2 * ((encodeInput n m).length + 1) ^ 2 := by
  simp only [exactTime, encodeInput, List.length_append, List.length_replicate, List.length_cons]
  nlinarith [sq_nonneg (n : ℤ), sq_nonneg (m : ℤ)]

noncomputable def bitMachine : BitMachine.Machine :=
  ofFinite (0 : Fin 4) 2 .parse false program

theorem bitMachine_outputs (n m : ℕ) :
    bitMachine.OutputsWithin (encodeInput n m) (List.replicate (n * m) true)
      (2 * ((encodeInput n m).length + 1) ^ 2) := by
  have hi : rawInit (0 : Fin 4) .parse false (encodeInput n m) =
      cfg (some .parse) false (encodeInput n m) [] [] [] := by
    unfold rawInit cfg
    congr 1
    funext k
    fin_cases k <;> rfl
  apply outputsWithin_of_raw_run (0 : Fin 4) 2 .parse false program
    (encodeInput n m) (List.replicate (n * m) true) (exactTime n m) _ (exactTime_bound n m)
  · change (run (exactTime n m) _).l = none
    rw [hi, run_correct]
    rfl
  · change (run (exactTime n m) _).stk 2 = _
    rw [hi, run_correct]
    rfl

end EthInapproximability.CurrentPaper.MatrixUnaryArithmetic
