import EthInapproximability.CurrentPaper.BitMachineEncoding
import Mathlib.Tactic

/-!
# A charged unary threshold test with conditional subtraction

Source: Appendix B, the division of row labels into four template blocks and
the final source block. This four-stack finite controller compares a unary
input `x` with a unary threshold `t`. If `x < t`, it restores `x`; otherwise
it leaves `x-t`. The threshold is always restored, both scratch stacks are
cleared, and finite control records which case occurred. Every scan and
restoration is included in the actual TM2 transition count.
-/

namespace EthInapproximability.CurrentPaper.MatrixUnaryCut

open Turing Turing.TM2.Stmt BitMachineEncoding

inductive Label where
  | scan | restoreRow | clearRow | restoreThreshold
  deriving DecidableEq, Fintype

abbrev Control := Bool × Bool
abbrev Config := TM2.Cfg (fun _ : Fin 4 => Bool) Label Control

def program : Label → TM2.Stmt (fun _ : Fin 4 => Bool) Label Control
  | .scan => pop 1 (fun s b => (s.1, b.isSome))
      (branch Prod.snd
        (push 3 (fun _ => true) (pop 0 (fun s b => (s.1, b.isSome))
          (branch Prod.snd (push 2 (fun _ => true) (goto (fun _ => .scan)))
            (load (fun _ => (false, false)) (goto (fun _ => .restoreRow))))))
        (load (fun _ => (true, false)) (goto (fun _ => .clearRow))))
  | .restoreRow => pop 2 (fun s b => (s.1, b.isSome))
      (branch Prod.snd (push 0 (fun _ => true) (goto (fun _ => .restoreRow)))
        (goto (fun _ => .restoreThreshold)))
  | .clearRow => pop 2 (fun s b => (s.1, b.isSome))
      (branch Prod.snd (goto (fun _ => .clearRow)) (goto (fun _ => .restoreThreshold)))
  | .restoreThreshold => pop 3 (fun s b => (s.1, b.isSome))
      (branch Prod.snd (push 1 (fun _ => true) (goto (fun _ => .restoreThreshold)))
        halt)

def cfg (l : Option Label) (s : Control) (x t rb tb : List Bool) : Config :=
  ⟨l, s, ![x, t, rb, tb]⟩

def run (n : ℕ) (c : Config) := ((advance program)^[n]) c

private theorem run_succ {c d : Config} (h : TM2.step program c = some d) (n : ℕ) :
    run (n + 1) c = run n d := by
  simp only [run, Function.iterate_succ_apply, advance, h, Option.getD_some]

private theorem run_add {c d : Config} {m : ℕ} (h : run m c = d) (n : ℕ) :
    run (m + n) c = run n d := by
  rw [Nat.add_comm m n]
  simp only [run, Function.iterate_add_apply] at h ⊢
  rw [h]

private theorem scan_cons (flag : Bool) (x t rb tb : List Bool) :
    TM2.step program (cfg (some .scan) (flag, true) (true :: x) (true :: t) rb tb) =
      some (cfg (some .scan) (flag, true) x t (true :: rb) (true :: tb)) := by
  apply congrArg (fun S => some (⟨some .scan, (flag, true), S⟩ : Config))
  funext k
  fin_cases k <;> rfl

private theorem scan_threshold_nil (flag : Bool) (x rb tb : List Bool) :
    TM2.step program (cfg (some .scan) (flag, true) x [] rb tb) =
      some (cfg (some .clearRow) (true, false) x [] rb tb) := by
  simp [TM2.step, TM2.stepAux, program, cfg]

private theorem scan_row_nil (flag : Bool) (t rb tb : List Bool) :
    TM2.step program (cfg (some .scan) (flag, true) [] (true :: t) rb tb) =
      some (cfg (some .restoreRow) (false, false) [] t rb (true :: tb)) := by
  apply congrArg (fun S => some (⟨some .restoreRow, (false, false), S⟩ : Config))
  funext k
  fin_cases k <;> rfl

private theorem restore_row_cons (s : Control) (x t rb tb : List Bool) :
    TM2.step program (cfg (some .restoreRow) s x t (true :: rb) tb) =
      some (cfg (some .restoreRow) (s.1, true) (true :: x) t rb tb) := by
  apply congrArg (fun S => some (⟨some .restoreRow, (s.1, true), S⟩ : Config))
  funext k
  fin_cases k <;> rfl

private theorem restore_row_nil (s : Control) (x t tb : List Bool) :
    TM2.step program (cfg (some .restoreRow) s x t [] tb) =
      some (cfg (some .restoreThreshold) (s.1, false) x t [] tb) := by
  simp [TM2.step, TM2.stepAux, program, cfg]

private theorem clear_row_cons (s : Control) (x t rb tb : List Bool) :
    TM2.step program (cfg (some .clearRow) s x t (true :: rb) tb) =
      some (cfg (some .clearRow) (s.1, true) x t rb tb) := by
  apply congrArg (fun S => some (⟨some .clearRow, (s.1, true), S⟩ : Config))
  funext k
  fin_cases k <;> rfl

private theorem clear_row_nil (s : Control) (x t tb : List Bool) :
    TM2.step program (cfg (some .clearRow) s x t [] tb) =
      some (cfg (some .restoreThreshold) (s.1, false) x t [] tb) := by
  simp [TM2.step, TM2.stepAux, program, cfg]

private theorem restore_threshold_cons (s : Control) (x t rb tb : List Bool) :
    TM2.step program (cfg (some .restoreThreshold) s x t rb (true :: tb)) =
      some (cfg (some .restoreThreshold) (s.1, true) x (true :: t) rb tb) := by
  apply congrArg (fun S => some (⟨some .restoreThreshold, (s.1, true), S⟩ : Config))
  funext k
  fin_cases k <;> rfl

private theorem restore_threshold_nil (s : Control) (x t rb : List Bool) :
    TM2.step program (cfg (some .restoreThreshold) s x t rb []) =
      some (cfg none (s.1, false) x t rb []) := by
  simp [TM2.step, TM2.stepAux, program, cfg]

private theorem replicate_push (n : ℕ) (b : Bool) (xs : List Bool) :
    List.replicate n b ++ b :: xs = b :: (List.replicate n b ++ xs) := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [List.replicate_succ, List.cons_append] using congrArg (List.cons b) ih

theorem scan_prefix (n : ℕ) (flag : Bool) (x t rb tb : List Bool) :
    run n (cfg (some .scan) (flag, true)
      (List.replicate n true ++ x) (List.replicate n true ++ t) rb tb) =
      cfg (some .scan) (flag, true) x t
        (List.replicate n true ++ rb) (List.replicate n true ++ tb) := by
  induction n generalizing rb tb with
  | zero => rfl
  | succ n ih =>
      rw [List.replicate_succ, List.cons_append, List.cons_append,
        run_succ (scan_cons _ _ _ _ _) n, ih]
      simp only [List.cons_append, replicate_push]

theorem restore_row_run (n : ℕ) (s : Control) (x t tb : List Bool) :
    run (n + 1) (cfg (some .restoreRow) s x t (List.replicate n true) tb) =
      cfg (some .restoreThreshold) (s.1, false) (List.replicate n true ++ x) t [] tb := by
  induction n generalizing s x with
  | zero => exact run_succ (restore_row_nil _ _ _ _) 0
  | succ n ih =>
      rw [List.replicate_succ, run_succ (restore_row_cons _ _ _ _ _) (n + 1), ih]
      simp only [List.cons_append, replicate_push]

theorem clear_row_run (n : ℕ) (s : Control) (x t tb : List Bool) :
    run (n + 1) (cfg (some .clearRow) s x t (List.replicate n true) tb) =
      cfg (some .restoreThreshold) (s.1, false) x t [] tb := by
  induction n generalizing s with
  | zero => exact run_succ (clear_row_nil _ _ _ _) 0
  | succ n ih =>
      rw [List.replicate_succ, run_succ (clear_row_cons _ _ _ _ _) (n + 1), ih]

theorem restore_threshold_run (n : ℕ) (s : Control) (x t rb : List Bool) :
    run (n + 1) (cfg (some .restoreThreshold) s x t rb (List.replicate n true)) =
      cfg none (s.1, false) x (List.replicate n true ++ t) rb [] := by
  induction n generalizing s t with
  | zero => exact run_succ (restore_threshold_nil _ _ _ _) 0
  | succ n ih =>
      rw [List.replicate_succ, run_succ (restore_threshold_cons _ _ _ _ _) (n + 1), ih]
      simp only [List.cons_append, replicate_push]

theorem source_run (t i : ℕ) :
    run (3 * t + 3) (cfg (some .scan) (false, true)
      (List.replicate (t + i) true) (List.replicate t true) [] []) =
      cfg none (true, false) (List.replicate i true) (List.replicate t true) [] [] := by
  have h₀ := scan_prefix t false (List.replicate i true) [] [] []
  simp only [List.append_nil, ← List.replicate_add] at h₀
  have h₁ := run_succ (scan_threshold_nil false (List.replicate i true)
    (List.replicate t true) (List.replicate t true)) 0
  have h₂ := clear_row_run t (true, false) (List.replicate i true) [] (List.replicate t true)
  have h₃ := restore_threshold_run t (true, false) (List.replicate i true) [] []
  simp only [List.append_nil] at h₃
  have h := (run_add ((run_add ((run_add h₀ 1).trans h₁) (t + 1)).trans h₂)
    (t + 1)).trans h₃
  have ht : t + 1 + (t + 1) + (t + 1) = 3 * t + 3 := by omega
  rw [ht] at h
  exact h

theorem template_run (x t : ℕ) (hxt : x < t) :
    run (3 * x + 4) (cfg (some .scan) (false, true)
      (List.replicate x true) (List.replicate t true) [] []) =
      cfg none (false, false) (List.replicate x true) (List.replicate t true) [] [] := by
  obtain ⟨u, rfl⟩ := Nat.exists_eq_add_of_le (show x + 1 ≤ t by omega)
  have h₀ := scan_prefix x false [] (true :: List.replicate u true) [] []
  have he : List.replicate x true ++ true :: List.replicate u true =
      List.replicate (x + 1 + u) true := by
    rw [← List.replicate_succ, ← List.replicate_add]
    congr 1
    omega
  simp only [List.append_nil, he] at h₀
  have h₁ := run_succ (scan_row_nil false (List.replicate u true)
    (List.replicate x true) (List.replicate x true)) 0
  have h₂ := restore_row_run x (false, false) [] (List.replicate u true)
    (true :: List.replicate x true)
  simp only [List.append_nil] at h₂
  have h₃ := restore_threshold_run (x + 1) (false, false) (List.replicate x true)
    (List.replicate u true) []
  simp only [List.replicate_succ] at h₃
  have h := (run_add ((run_add ((run_add h₀ 1).trans h₁) (x + 1)).trans h₂)
    (x + 2)).trans h₃
  simp only [← List.replicate_succ, ← List.replicate_add] at h
  have ht : x + 1 + (x + 1) + (x + 2) = 3 * x + 4 := by omega
  rw [ht] at h
  exact h

theorem cut_run (x t : ℕ) :
    ∃ k ≤ 3 * min x t + 4,
      run k (cfg (some .scan) (false, true)
        (List.replicate x true) (List.replicate t true) [] []) =
        cfg none (decide (t ≤ x), false)
          (List.replicate (if x < t then x else x - t) true)
          (List.replicate t true) [] [] := by
  by_cases h : x < t
  · refine ⟨3 * x + 4, ?_, ?_⟩
    · simp [Nat.min_eq_left (Nat.le_of_lt h)]
    · simpa [h, show ¬t ≤ x by omega] using template_run x t h
  · have ht : t ≤ x := by omega
    refine ⟨3 * t + 3, ?_, ?_⟩
    · simp only [Nat.min_eq_right ht]; omega
    · simpa [h, ht, Nat.add_sub_cancel' ht] using source_run t (x - t)

end EthInapproximability.CurrentPaper.MatrixUnaryCut
