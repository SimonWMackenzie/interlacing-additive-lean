import EthInapproximability.CurrentPaper.BitMachineEncoding
import Mathlib.Tactic

/-!
# Literal unary quotient and remainder for input-label decoding

Source: locked v8 `thm:paper-materialization`, integer quotient/remainder
decoding of row, column, and group labels. Both the dividend and divisor are
Boolean stacks. Division is repeated counted subtraction with restoration;
it is not an operation of finite control. The divisor is preserved exactly.
-/

namespace EthInapproximability.CurrentPaper.MatrixUnaryDivision

open Turing Turing.TM2.Stmt BitMachineEncoding

inductive Label where
  | start | copy | restore | scan | clearRemainder | clearCount | zero
  deriving DecidableEq, Fintype

def program : Label → TM2.Stmt (fun _ : Fin 6 => Bool) Label Bool
  | .start => pop 1 (fun _ b => b.isSome)
      (branch id (push 1 (fun _ => true) (goto (fun _ => .copy)))
        (goto (fun _ => .zero)))
  | .copy => pop 1 (fun _ b => b.isSome)
      (branch id (push 2 (fun _ => true) (push 5 (fun _ => true)
        (goto (fun _ => .copy)))) (goto (fun _ => .restore)))
  | .restore => pop 5 (fun _ b => b.isSome)
      (branch id (push 1 (fun _ => true) (goto (fun _ => .restore)))
        (goto (fun _ => .scan)))
  | .scan => pop 2 (fun _ b => b.isSome)
      (branch id (pop 0 (fun _ b => b.isSome)
        (branch id (push 3 (fun _ => true) (goto (fun _ => .scan)))
          (goto (fun _ => .clearCount))))
        (push 4 (fun _ => true) (goto (fun _ => .clearRemainder))))
  | .clearRemainder => pop 3 (fun _ b => b.isSome)
      (branch id (goto (fun _ => .clearRemainder)) (goto (fun _ => .copy)))
  | .clearCount => pop 2 (fun _ b => b.isSome)
      (branch id (goto (fun _ => .clearCount)) (load (fun _ => false) halt))
  | .zero => pop 0 (fun _ b => b.isSome)
      (branch id (push 3 (fun _ => true) (goto (fun _ => .zero)))
        (load (fun _ => false) halt))

abbrev Config := TM2.Cfg (fun _ : Fin 6 => Bool) Label Bool

def cfg (l : Option Label) (s : Bool) (input divisor count remainder quotient saved : List Bool) :
    Config := ⟨l, s, ![input, divisor, count, remainder, quotient, saved]⟩

def run (n : ℕ) (c : Config) := ((advance program)^[n]) c

private theorem run_succ {c d : Config} (h : TM2.step program c = some d) (n : ℕ) :
    run (n + 1) c = run n d := by
  simp only [run, Function.iterate_succ_apply, advance, h, Option.getD_some]

private theorem run_add {c d : Config} {m : ℕ} (h : run m c = d) (n : ℕ) :
    run (m + n) c = run n d := by
  rw [Nat.add_comm m n]
  simp only [run, Function.iterate_add_apply] at h ⊢
  rw [h]

private theorem copy_cons (s : Bool) (input divisor count rem quo saved : List Bool) :
    TM2.step program (cfg (some .copy) s input (true :: divisor) count rem quo saved) =
      some (cfg (some .copy) true input divisor (true :: count) rem quo (true :: saved)) := by
  apply congrArg (fun S => some (⟨some .copy, true, S⟩ : Config))
  funext k
  fin_cases k <;> rfl

private theorem copy_nil (s : Bool) (input count rem quo saved : List Bool) :
    TM2.step program (cfg (some .copy) s input [] count rem quo saved) =
      some (cfg (some .restore) false input [] count rem quo saved) := by
  apply congrArg (fun S => some (⟨some .restore, false, S⟩ : Config))
  funext k
  fin_cases k <;> rfl

private theorem restore_cons (s : Bool) (input divisor count rem quo saved : List Bool) :
    TM2.step program (cfg (some .restore) s input divisor count rem quo (true :: saved)) =
      some (cfg (some .restore) true input (true :: divisor) count rem quo saved) := by
  apply congrArg (fun S => some (⟨some .restore, true, S⟩ : Config))
  funext k
  fin_cases k <;> rfl

private theorem restore_nil (s : Bool) (input divisor count rem quo : List Bool) :
    TM2.step program (cfg (some .restore) s input divisor count rem quo []) =
      some (cfg (some .scan) false input divisor count rem quo []) := by
  apply congrArg (fun S => some (⟨some .scan, false, S⟩ : Config))
  funext k
  fin_cases k <;> rfl

theorem copy_run (n c b : ℕ) (s : Bool) (input rem quo : List Bool) :
    run (n + 1) (cfg (some .copy) s input (List.replicate n true)
      (List.replicate c true) rem quo (List.replicate b true)) =
      cfg (some .restore) false input [] (List.replicate (n + c) true)
        rem quo (List.replicate (n + b) true) := by
  induction n generalizing c b s with
  | zero => simpa using run_succ (copy_nil s input (List.replicate c true) rem quo
      (List.replicate b true)) 0
  | succ n ih =>
      rw [List.replicate_succ, run_succ (copy_cons _ _ _ _ _ _ _) _]
      simpa only [← List.replicate_succ, Nat.add_assoc, Nat.add_comm 1 c, Nat.add_comm 1 b]
        using ih (c + 1) (b + 1) true

theorem restore_run (n d : ℕ) (s : Bool) (input count rem quo : List Bool) :
    run (n + 1) (cfg (some .restore) s input (List.replicate d true) count rem quo
      (List.replicate n true)) =
      cfg (some .scan) false input (List.replicate (n + d) true) count rem quo [] := by
  induction n generalizing d s with
  | zero => simpa using run_succ (restore_nil s input (List.replicate d true) count rem quo) 0
  | succ n ih =>
      rw [List.replicate_succ, run_succ (restore_cons _ _ _ _ _ _ _) _]
      simpa only [← List.replicate_succ, Nat.add_assoc, Nat.add_comm 1 d] using ih (d + 1) true

theorem prepare_run (m : ℕ) (s : Bool) (input rem quo : List Bool) :
    run (2 * m + 2) (cfg (some .copy) s input (List.replicate m true) [] rem quo []) =
      cfg (some .scan) false input (List.replicate m true) (List.replicate m true) rem quo [] := by
  have h₁ := copy_run m 0 0 s input rem quo
  have h₂ := restore_run m 0 false input (List.replicate m true) rem quo
  simp only [Nat.add_zero, List.replicate_zero] at h₁ h₂
  simpa only [show m + 1 + (m + 1) = 2 * m + 2 by omega] using (run_add h₁ _).trans h₂

private theorem scan_cons (s : Bool) (input divisor count rem quo : List Bool) :
    TM2.step program (cfg (some .scan) s (true :: input) divisor (true :: count) rem quo []) =
      some (cfg (some .scan) true input divisor count (true :: rem) quo []) := by
  apply congrArg (fun S => some (⟨some .scan, true, S⟩ : Config))
  funext k
  fin_cases k <;> rfl

private theorem scan_empty_count (s : Bool) (input divisor rem quo : List Bool) :
    TM2.step program (cfg (some .scan) s input divisor [] rem quo []) =
      some (cfg (some .clearRemainder) false input divisor [] rem (true :: quo) []) := by
  apply congrArg (fun S => some (⟨some .clearRemainder, false, S⟩ : Config))
  funext k
  fin_cases k <;> rfl

private theorem scan_empty_input (s : Bool) (divisor count rem quo : List Bool) :
    TM2.step program (cfg (some .scan) s [] divisor (true :: count) rem quo []) =
      some (cfg (some .clearCount) false [] divisor count rem quo []) := by
  apply congrArg (fun S => some (⟨some .clearCount, false, S⟩ : Config))
  funext k
  fin_cases k <;> rfl

private theorem clearR_cons (s : Bool) (input divisor rem quo : List Bool) :
    TM2.step program (cfg (some .clearRemainder) s input divisor [] (true :: rem) quo []) =
      some (cfg (some .clearRemainder) true input divisor [] rem quo []) := by
  apply congrArg (fun S => some (⟨some .clearRemainder, true, S⟩ : Config))
  funext k
  fin_cases k <;> rfl

private theorem clearR_nil (s : Bool) (input divisor quo : List Bool) :
    TM2.step program (cfg (some .clearRemainder) s input divisor [] [] quo []) =
      some (cfg (some .copy) false input divisor [] [] quo []) := by
  apply congrArg (fun S => some (⟨some .copy, false, S⟩ : Config))
  funext k
  fin_cases k <;> rfl

theorem clearR_run (n : ℕ) (s : Bool) (input divisor quo : List Bool) :
    run (n + 1) (cfg (some .clearRemainder) s input divisor [] (List.replicate n true) quo []) =
      cfg (some .copy) false input divisor [] [] quo [] := by
  induction n generalizing s with
  | zero => exact run_succ (clearR_nil s input divisor quo) 0
  | succ n ih => rw [List.replicate_succ, run_succ (clearR_cons _ _ _ _ _) _]; exact ih true

private theorem clearC_cons (s : Bool) (divisor count rem quo : List Bool) :
    TM2.step program (cfg (some .clearCount) s [] divisor (true :: count) rem quo []) =
      some (cfg (some .clearCount) true [] divisor count rem quo []) := by
  apply congrArg (fun S => some (⟨some .clearCount, true, S⟩ : Config))
  funext k
  fin_cases k <;> rfl

private theorem clearC_nil (s : Bool) (divisor rem quo : List Bool) :
    TM2.step program (cfg (some .clearCount) s [] divisor [] rem quo []) =
      some (cfg none false [] divisor [] rem quo []) := by
  apply congrArg (fun S => some (⟨none, false, S⟩ : Config))
  funext k
  fin_cases k <;> rfl

theorem clearC_run (n : ℕ) (s : Bool) (divisor rem quo : List Bool) :
    run (n + 1) (cfg (some .clearCount) s [] divisor (List.replicate n true) rem quo []) =
      cfg none false [] divisor [] rem quo [] := by
  induction n generalizing s with
  | zero => exact run_succ (clearC_nil s divisor rem quo) 0
  | succ n ih => rw [List.replicate_succ, run_succ (clearC_cons _ _ _ _ _) _]; exact ih true

/-- A simultaneous subtraction scan preserves the unconsumed input suffix. -/
theorem scan_prefix (k c r : ℕ) (s : Bool) (input divisor quo : List Bool) :
    run k (cfg (some .scan) s (List.replicate k true ++ input) divisor
      (List.replicate (k + c) true) (List.replicate r true) quo []) =
      cfg (some .scan) (if k = 0 then s else true) input divisor
        (List.replicate c true) (List.replicate (k + r) true) quo [] := by
  induction k generalizing r s with
  | zero => simp [run]
  | succ k ih =>
      rw [List.replicate_succ, List.cons_append,
        show k + 1 + c = (k + c) + 1 by omega, List.replicate_succ,
        run_succ (scan_cons _ _ _ _ _ _) _]
      simpa only [← List.replicate_succ, Nat.add_assoc, Nat.add_comm 1 r,
        ite_self, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ↓reduceIte] using ih (r + 1) true

theorem full_block (m : ℕ) (s : Bool) (input quo : List Bool) :
    run (4 * m + 4) (cfg (some .scan) s (List.replicate m true ++ input)
      (List.replicate m true) (List.replicate m true) [] quo []) =
      cfg (some .scan) false input (List.replicate m true) (List.replicate m true)
        [] (true :: quo) [] := by
  have h₁ := scan_prefix m 0 0 s input (List.replicate m true) quo
  simp only [Nat.add_zero, List.replicate_zero] at h₁
  have h₂ := run_succ (scan_empty_count (if m = 0 then s else true) input
    (List.replicate m true) (List.replicate m true) quo) 0
  have h₃ := clearR_run m false input (List.replicate m true) (true :: quo)
  have h₄ := prepare_run m false input [] (true :: quo)
  have h := (run_add ((run_add ((run_add h₁ 1).trans h₂) (m + 1)).trans h₃)
    (2 * m + 2)).trans h₄
  simpa only [show m + 1 + (m + 1) + (2 * m + 2) = 4 * m + 4 by omega] using h

theorem partial_block (m r : ℕ) (hr : r < m) (s : Bool) (quo : List Bool) :
    run (m + 1) (cfg (some .scan) s (List.replicate r true)
      (List.replicate m true) (List.replicate m true) [] quo []) =
      cfg none false [] (List.replicate m true) [] (List.replicate r true) quo [] := by
  have h₁ := scan_prefix r (m - r) 0 s [] (List.replicate m true) quo
  simp only [List.append_nil, Nat.add_zero, List.replicate_zero,
    Nat.add_sub_of_le hr.le] at h₁
  have hcount : List.replicate (m - r) true = true :: List.replicate (m - r - 1) true := by
    conv_lhs => rw [show m - r = (m - r - 1) + 1 by omega, List.replicate_succ]
  rw [hcount] at h₁
  have h₂ := run_succ (scan_empty_input (if r = 0 then s else true)
    (List.replicate m true) (List.replicate (m - r - 1) true) (List.replicate r true) quo) 0
  have h₃ := clearC_run (m - r - 1) false (List.replicate m true) (List.replicate r true) quo
  have h := (run_add ((run_add h₁ 1).trans h₂) (m - r - 1 + 1)).trans h₃
  have ht : r + 1 + (m - r - 1 + 1) = m + 1 := by omega
  simpa only [ht] using h

/-- The quotient counts literal complete subtraction blocks; the remaining
markers are exactly the proper remainder. -/
theorem blocks_run (q m r b : ℕ) (hr : r < m) (s : Bool) :
    run (q * (4 * m + 4) + (m + 1))
      (cfg (some .scan) s (List.replicate (q * m + r) true)
        (List.replicate m true) (List.replicate m true) [] (List.replicate b true) []) =
      cfg none false [] (List.replicate m true) []
        (List.replicate r true) (List.replicate (q + b) true) [] := by
  induction q generalizing b s with
  | zero => simpa using partial_block m r hr s (List.replicate b true)
  | succ q ih =>
      have h₁ := full_block m s (List.replicate (q * m + r) true) (List.replicate b true)
      have h₂ := ih (b + 1) false
      rw [List.replicate_succ] at h₂
      have h := (run_add h₁ (q * (4 * m + 4) + (m + 1))).trans h₂
      have hi : m + (q * m + r) = (q + 1) * m + r := by ring
      have ht : 4 * m + 4 + (q * (4 * m + 4) + (m + 1)) =
          (q + 1) * (4 * m + 4) + (m + 1) := by ring
      simpa only [← List.replicate_add, hi, ht, Nat.add_assoc, Nat.add_comm 1 b] using h

private theorem start_pos (m : ℕ) (s : Bool) (input : List Bool) :
    TM2.step program (cfg (some .start) s input (List.replicate (m + 1) true) [] [] [] []) =
      some (cfg (some .copy) true input (List.replicate (m + 1) true) [] [] [] []) := by
  apply congrArg (fun S => some (⟨some .copy, true, S⟩ : Config))
  funext k
  fin_cases k <;> rfl

def exactTime (n m : ℕ) : ℕ := (n / m) * (4 * m + 4) + 3 * m + 4

theorem division_run (n m : ℕ) (hm : 0 < m) :
    run (exactTime n m) (cfg (some .start) false (List.replicate n true)
      (List.replicate m true) [] [] [] []) =
      cfg none false [] (List.replicate m true) []
        (List.replicate (n % m) true) (List.replicate (n / m) true) [] := by
  have hstart : TM2.step program (cfg (some .start) false (List.replicate n true)
      (List.replicate m true) [] [] [] []) =
      some (cfg (some .copy) true (List.replicate n true) (List.replicate m true) [] [] [] []) := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm)
    exact start_pos k false (List.replicate n true)
  have h₁ := run_succ hstart 0
  have h₂ := prepare_run m true (List.replicate n true) [] []
  have h₃ := blocks_run (n / m) m (n % m) 0 (Nat.mod_lt n hm) false
  rw [Nat.mul_comm (n / m) m, Nat.div_add_mod] at h₃
  simp only [Nat.add_zero, List.replicate_zero] at h₃
  have h := (run_add ((run_add h₁ (2 * m + 2)).trans h₂)
    ((n / m) * (4 * m + 4) + (m + 1))).trans h₃
  have ht : 1 + (2 * m + 2) + ((n / m) * (4 * m + 4) + (m + 1)) = exactTime n m := by
    unfold exactTime
    ring
  simpa only [Nat.zero_add, ht] using h

theorem exactTime_bound (n m : ℕ) : exactTime n m ≤ 8 * n + 3 * m + 4 := by
  have hmul : n / m * m ≤ n := Nat.div_mul_le_self n m
  have hdiv : n / m ≤ n := Nat.div_le_self n m
  unfold exactTime
  nlinarith

private theorem zero_cons (s : Bool) (input rem : List Bool) :
    TM2.step program (cfg (some .zero) s (true :: input) [] [] rem [] []) =
      some (cfg (some .zero) true input [] [] (true :: rem) [] []) := by
  apply congrArg (fun S => some (⟨some .zero, true, S⟩ : Config))
  funext k
  fin_cases k <;> rfl

private theorem zero_nil (s : Bool) (rem : List Bool) :
    TM2.step program (cfg (some .zero) s [] [] [] rem [] []) =
      some (cfg none false [] [] [] rem [] []) := by
  apply congrArg (fun S => some (⟨none, false, S⟩ : Config))
  funext k
  fin_cases k <;> rfl

theorem zero_run (n r : ℕ) (s : Bool) :
    run (n + 1) (cfg (some .zero) s (List.replicate n true) [] [] (List.replicate r true) [] []) =
      cfg none false [] [] [] (List.replicate (n + r) true) [] [] := by
  induction n generalizing r s with
  | zero => simpa using run_succ (zero_nil s (List.replicate r true)) 0
  | succ n ih =>
      rw [List.replicate_succ, run_succ (zero_cons _ _ _) _]
      simpa only [← List.replicate_succ, Nat.add_assoc, Nat.add_comm 1 r] using ih (r + 1) true

theorem zero_division_run (n : ℕ) :
    run (n + 2) (cfg (some .start) false (List.replicate n true) [] [] [] [] []) =
      cfg none false [] [] [] (List.replicate n true) [] [] := by
  have hs : TM2.step program (cfg (some .start) false (List.replicate n true) [] [] [] [] []) =
      some (cfg (some .zero) false (List.replicate n true) [] [] [] [] []) := by
    apply congrArg (fun S => some (⟨some .zero, false, S⟩ : Config))
    funext k
    fin_cases k <;> rfl
  rw [show n + 2 = (n + 1) + 1 by omega, run_succ hs _]
  simpa only [Nat.add_zero, List.replicate_zero] using zero_run n 0 false

def totalTime (n m : ℕ) : ℕ := if m = 0 then n + 2 else exactTime n m

/-- The fixed controller handles every pair of natural unary operands,
including division by zero with Lean's quotient-zero/remainder-input convention. -/
theorem division_total_run (n m : ℕ) :
    run (totalTime n m) (cfg (some .start) false (List.replicate n true)
      (List.replicate m true) [] [] [] []) =
      cfg none false [] (List.replicate m true) []
        (List.replicate (n % m) true) (List.replicate (n / m) true) [] := by
  by_cases hm : m = 0
  · subst m
    simpa only [totalTime, ↓reduceIte, Nat.mod_zero, Nat.div_zero, List.replicate_zero]
      using zero_division_run n
  · simpa only [totalTime, hm, ↓reduceIte] using division_run n m (Nat.pos_of_ne_zero hm)

theorem totalTime_bound (n m : ℕ) : totalTime n m ≤ 8 * n + 3 * m + 4 := by
  unfold totalTime
  split
  · omega
  · exact exactTime_bound n m

end EthInapproximability.CurrentPaper.MatrixUnaryDivision
