import EthInapproximability.CurrentPaper.BitMachineEncoding
import Mathlib.Tactic

/-!
# Preserving unary multiply-add for matrix addresses

This finite six-stack controller computes `row * width + column`. It preserves
the three input registers, clears both work registers, and prepends the unary
address to an arbitrary output suffix. The running time counts literal TM2
steps; multiplication and register preservation are not arithmetic oracles.

Source: Appendix B, `thm:paper-materialization`, local row-major decoding and
arithmetic. This is a reusable operational component, not the full materializer.
-/

namespace EthInapproximability.CurrentPaper.MatrixAddressMachine

open Turing Turing.TM2.Stmt BitMachineEncoding

inductive Label where
  | outer | scanWidth | restoreWidth | restoreRow | scanColumn | restoreColumn
  deriving DecidableEq, Fintype

def program : Label → TM2.Stmt (fun _ : Fin 6 => Bool) Label Bool
  | .outer => pop 0 (fun _ b => b.isSome)
      (branch id (push 3 (fun _ => true) (goto (fun _ => .scanWidth)))
        (goto (fun _ => .restoreRow)))
  | .scanWidth => pop 1 (fun _ b => b.isSome)
      (branch id (push 4 (fun _ => true) (push 5 (fun _ => true)
        (goto (fun _ => .scanWidth)))) (goto (fun _ => .restoreWidth)))
  | .restoreWidth => pop 4 (fun _ b => b.isSome)
      (branch id (push 1 (fun _ => true) (goto (fun _ => .restoreWidth)))
        (goto (fun _ => .outer)))
  | .restoreRow => pop 3 (fun _ b => b.isSome)
      (branch id (push 0 (fun _ => true) (goto (fun _ => .restoreRow)))
        (goto (fun _ => .scanColumn)))
  | .scanColumn => pop 2 (fun _ b => b.isSome)
      (branch id (push 4 (fun _ => true) (push 5 (fun _ => true)
        (goto (fun _ => .scanColumn)))) (goto (fun _ => .restoreColumn)))
  | .restoreColumn => pop 4 (fun _ b => b.isSome)
      (branch id (push 2 (fun _ => true) (goto (fun _ => .restoreColumn)))
        (load (fun _ => false) halt))

abbrev Config := TM2.Cfg (fun _ : Fin 6 => Bool) Label Bool

def cfg (l : Option Label) (s : Bool) (r w c rb wb out : List Bool) : Config :=
  ⟨l, s, ![r, w, c, rb, wb, out]⟩

def run (n : ℕ) (c : Config) := ((advance program)^[n]) c

private theorem run_succ {c d : Config} (h : TM2.step program c = some d) (n : ℕ) :
    run (n + 1) c = run n d := by
  simp only [run, Function.iterate_succ_apply, advance, h, Option.getD_some]

private theorem run_add {c d : Config} {m : ℕ} (h : run m c = d) (n : ℕ) :
    run (m + n) c = run n d := by
  rw [Nat.add_comm m n]
  simp only [run, Function.iterate_add_apply] at h ⊢
  rw [h]

private theorem outer_cons (s : Bool) (r w c rb out : List Bool) :
    TM2.step program (cfg (some .outer) s (true :: r) w c rb [] out) =
      some (cfg (some .scanWidth) true r w c (true :: rb) [] out) := by
  apply congrArg (fun S => some (⟨some .scanWidth, true, S⟩ : Config))
  funext k
  fin_cases k <;> rfl

private theorem outer_nil (s : Bool) (w c rb out : List Bool) :
    TM2.step program (cfg (some .outer) s [] w c rb [] out) =
      some (cfg (some .restoreRow) false [] w c rb [] out) := by
  simp [TM2.step, TM2.stepAux, program, cfg]

private theorem width_cons (s : Bool) (r w c rb wb out : List Bool) :
    TM2.step program (cfg (some .scanWidth) s r (true :: w) c rb wb out) =
      some (cfg (some .scanWidth) true r w c rb (true :: wb) (true :: out)) := by
  apply congrArg (fun S => some (⟨some .scanWidth, true, S⟩ : Config))
  funext k
  fin_cases k <;> rfl

private theorem width_nil (s : Bool) (r c rb wb out : List Bool) :
    TM2.step program (cfg (some .scanWidth) s r [] c rb wb out) =
      some (cfg (some .restoreWidth) false r [] c rb wb out) := by
  simp [TM2.step, TM2.stepAux, program, cfg]

private theorem width_restore_cons (s : Bool) (r w c rb wb out : List Bool) :
    TM2.step program (cfg (some .restoreWidth) s r w c rb (true :: wb) out) =
      some (cfg (some .restoreWidth) true r (true :: w) c rb wb out) := by
  apply congrArg (fun S => some (⟨some .restoreWidth, true, S⟩ : Config))
  funext k
  fin_cases k <;> rfl

private theorem width_restore_nil (s : Bool) (r w c rb out : List Bool) :
    TM2.step program (cfg (some .restoreWidth) s r w c rb [] out) =
      some (cfg (some .outer) false r w c rb [] out) := by
  simp [TM2.step, TM2.stepAux, program, cfg]

private theorem row_restore_cons (s : Bool) (r w c rb out : List Bool) :
    TM2.step program (cfg (some .restoreRow) s r w c (true :: rb) [] out) =
      some (cfg (some .restoreRow) true (true :: r) w c rb [] out) := by
  apply congrArg (fun S => some (⟨some .restoreRow, true, S⟩ : Config))
  funext k
  fin_cases k <;> rfl

private theorem row_restore_nil (s : Bool) (r w c out : List Bool) :
    TM2.step program (cfg (some .restoreRow) s r w c [] [] out) =
      some (cfg (some .scanColumn) false r w c [] [] out) := by
  simp [TM2.step, TM2.stepAux, program, cfg]

private theorem column_cons (s : Bool) (r w c wb out : List Bool) :
    TM2.step program (cfg (some .scanColumn) s r w (true :: c) [] wb out) =
      some (cfg (some .scanColumn) true r w c [] (true :: wb) (true :: out)) := by
  apply congrArg (fun S => some (⟨some .scanColumn, true, S⟩ : Config))
  funext k
  fin_cases k <;> rfl

private theorem column_nil (s : Bool) (r w wb out : List Bool) :
    TM2.step program (cfg (some .scanColumn) s r w [] [] wb out) =
      some (cfg (some .restoreColumn) false r w [] [] wb out) := by
  simp [TM2.step, TM2.stepAux, program, cfg]

private theorem column_restore_cons (s : Bool) (r w c wb out : List Bool) :
    TM2.step program (cfg (some .restoreColumn) s r w c [] (true :: wb) out) =
      some (cfg (some .restoreColumn) true r w (true :: c) [] wb out) := by
  apply congrArg (fun S => some (⟨some .restoreColumn, true, S⟩ : Config))
  funext k
  fin_cases k <;> rfl

private theorem column_restore_nil (s : Bool) (r w c out : List Bool) :
    TM2.step program (cfg (some .restoreColumn) s r w c [] [] out) =
      some (cfg none false r w c [] [] out) := by
  simp [TM2.step, TM2.stepAux, program, cfg]

private theorem unary_append_cons (n : ℕ) (out : List Bool) :
    List.replicate n true ++ true :: out = true :: (List.replicate n true ++ out) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [List.replicate_succ, List.cons_append, ih]

theorem width_scan (m k : ℕ) (s : Bool) (r c rb out : List Bool) :
    run (m + 1) (cfg (some .scanWidth) s r (List.replicate m true) c rb
      (List.replicate k true) out) =
      cfg (some .restoreWidth) false r [] c rb (List.replicate (m + k) true)
        (List.replicate m true ++ out) := by
  induction m generalizing k s out with
  | zero => simpa using run_succ (width_nil s r c rb (List.replicate k true) out) 0
  | succ m ih =>
      rw [List.replicate_succ, run_succ (width_cons _ _ _ _ _ _ _) _]
      simpa only [← List.replicate_succ, List.replicate_succ, List.cons_append, unary_append_cons,
        List.replicate_append_replicate, Nat.add_assoc, Nat.add_comm 1 k,
        List.replicate_succ', List.append_assoc] using ih (k + 1) true (true :: out)

theorem width_restore (m k : ℕ) (s : Bool) (r c rb out : List Bool) :
    run (m + 1) (cfg (some .restoreWidth) s r (List.replicate k true) c rb
      (List.replicate m true) out) =
      cfg (some .outer) false r (List.replicate (m + k) true) c rb [] out := by
  induction m generalizing k s with
  | zero => simpa using run_succ (width_restore_nil s r (List.replicate k true) c rb out) 0
  | succ m ih =>
      rw [List.replicate_succ, run_succ (width_restore_cons _ _ _ _ _ _ _) _]
      simpa only [← List.replicate_succ, Nat.add_assoc, Nat.add_comm 1 k] using ih (k + 1) true

theorem multiply_run (n m k : ℕ) (s : Bool) (c out : List Bool) :
    run (n * (2 * m + 3) + 1)
      (cfg (some .outer) s (List.replicate n true) (List.replicate m true) c
        (List.replicate k true) [] out) =
      cfg (some .restoreRow) false [] (List.replicate m true) c
        (List.replicate (n + k) true) [] (List.replicate (n * m) true ++ out) := by
  induction n generalizing k s out with
  | zero =>
      simpa using run_succ (outer_nil s (List.replicate m true) c (List.replicate k true) out) 0
  | succ n ih =>
      have h₁ := run_succ (outer_cons s (List.replicate n true) (List.replicate m true)
        c (List.replicate k true) out) 0
      have h₂ := width_scan m 0 true (List.replicate n true) c
        (List.replicate (k + 1) true) out
      have h₃ := width_restore m 0 false (List.replicate n true) c
        (List.replicate (k + 1) true) (List.replicate m true ++ out)
      simp only [Nat.add_zero, List.replicate_zero] at h₂ h₃
      have h₁₂ := (run_add h₁ (m + 1)).trans (by simpa only [List.replicate_succ] using h₂)
      have h₁₂₃ := (run_add h₁₂ (m + 1)).trans h₃
      have h := (run_add h₁₂₃ (n * (2 * m + 3) + 1)).trans
        (ih (k + 1) false (List.replicate m true ++ out))
      have ht : 1 + (m + 1) + (m + 1) + (n * (2 * m + 3) + 1) =
          (n + 1) * (2 * m + 3) + 1 := by ring
      simp only [Nat.zero_add] at h
      rw [ht] at h
      simpa only [← List.append_assoc, List.replicate_append_replicate,
        Nat.add_mul, Nat.one_mul, Nat.add_assoc, Nat.add_comm 1 k] using h

theorem row_restore (n k : ℕ) (s : Bool) (w c out : List Bool) :
    run (n + 1) (cfg (some .restoreRow) s (List.replicate k true) w c
      (List.replicate n true) [] out) =
      cfg (some .scanColumn) false (List.replicate (n + k) true) w c [] [] out := by
  induction n generalizing k s with
  | zero => simpa using run_succ (row_restore_nil s (List.replicate k true) w c out) 0
  | succ n ih =>
      rw [List.replicate_succ, run_succ (row_restore_cons _ _ _ _ _ _) _]
      simpa only [← List.replicate_succ, Nat.add_assoc, Nat.add_comm 1 k] using ih (k + 1) true

theorem column_scan (c k : ℕ) (s : Bool) (r w out : List Bool) :
    run (c + 1) (cfg (some .scanColumn) s r w (List.replicate c true) []
      (List.replicate k true) out) =
      cfg (some .restoreColumn) false r w [] [] (List.replicate (c + k) true)
        (List.replicate c true ++ out) := by
  induction c generalizing k s out with
  | zero => simpa using run_succ (column_nil s r w (List.replicate k true) out) 0
  | succ c ih =>
      rw [List.replicate_succ, run_succ (column_cons _ _ _ _ _ _) _]
      simpa only [← List.replicate_succ, List.replicate_succ, List.cons_append, unary_append_cons,
        List.replicate_append_replicate, Nat.add_assoc, Nat.add_comm 1 k,
        List.replicate_succ', List.append_assoc] using ih (k + 1) true (true :: out)

theorem column_restore (c k : ℕ) (s : Bool) (r w out : List Bool) :
    run (c + 1) (cfg (some .restoreColumn) s r w (List.replicate k true) []
      (List.replicate c true) out) =
      cfg none false r w (List.replicate (c + k) true) [] [] out := by
  induction c generalizing k s with
  | zero => simpa using run_succ (column_restore_nil s r w (List.replicate k true) out) 0
  | succ c ih =>
      rw [List.replicate_succ, run_succ (column_restore_cons _ _ _ _ _ _) _]
      simpa only [← List.replicate_succ, Nat.add_assoc, Nat.add_comm 1 k] using ih (k + 1) true

def exactTime (row width column : ℕ) : ℕ := 2 * row * width + 4 * row + 2 * column + 4

/-- The complete literal run preserves all inputs and the old output suffix. -/
theorem address_run (row width column : ℕ) (s : Bool) (out : List Bool) :
    run (exactTime row width column)
      (cfg (some .outer) s (List.replicate row true) (List.replicate width true)
        (List.replicate column true) [] [] out) =
      cfg none false (List.replicate row true) (List.replicate width true)
        (List.replicate column true) [] [] (List.replicate (row * width + column) true ++ out) := by
  have h₁ := multiply_run row width 0 s (List.replicate column true) out
  have h₂ := row_restore row 0 false (List.replicate width true) (List.replicate column true)
    (List.replicate (row * width) true ++ out)
  have h₃ := column_scan column 0 false (List.replicate row true) (List.replicate width true)
    (List.replicate (row * width) true ++ out)
  have h₄ := column_restore column 0 false (List.replicate row true) (List.replicate width true)
    (List.replicate column true ++ (List.replicate (row * width) true ++ out))
  simp only [Nat.add_zero, List.replicate_zero] at h₁ h₂ h₃ h₄
  have h := (run_add ((run_add ((run_add h₁ (row + 1)).trans h₂) (column + 1)).trans h₃)
    (column + 1)).trans h₄
  have ht : row * (2 * width + 3) + 1 + (row + 1) + (column + 1) + (column + 1) =
      exactTime row width column := by unfold exactTime; ring
  simpa only [ht, ← List.append_assoc, List.replicate_append_replicate,
    Nat.add_comm column (row * width)] using h

theorem exactTime_bound (row width column : ℕ) :
    exactTime row width column ≤ 4 * (row + width + column + 1) ^ 2 := by
  unfold exactTime
  nlinarith [sq_nonneg (row : ℤ), sq_nonneg (width : ℤ), sq_nonneg (column : ℤ)]

end EthInapproximability.CurrentPaper.MatrixAddressMachine
