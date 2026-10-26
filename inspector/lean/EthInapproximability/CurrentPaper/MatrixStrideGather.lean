import EthInapproximability.CurrentPaper.MatrixReadAt
import EthInapproximability.CurrentPaper.BitMachineSubroutine
import EthInapproximability.CurrentPaper.MatrixMaterialization

/-!
# Literal strided reads for matrix columns

The controller repeatedly reads the array at a unary address and adds a unary
stride. It preserves the array and stride, clears its work registers, and
prepends the collected bits in reverse order to the existing output. The
address and count are literal stack contents, not finite-control parameters.

Source: Appendix B, `thm:paper-materialization`, row-major entry evaluation.
This operational component does not assert the full materializer runtime.
-/

namespace EthInapproximability.CurrentPaper.MatrixStrideGather

open Turing Turing.TM2.Stmt BitMachineEncoding BitMachineComposition BitMachineSubroutine

inductive Admin where
  | test | scan | restore
  deriving DecidableEq, Fintype

abbrev Label := MatrixReadAt.Label ⊕ Admin
abbrev Control := MatrixReadAt.Control × Bool
abbrev Config := TM2.Cfg (fun _ : Fin 7 ⊕ Fin 3 => Bool) Label Control

def baseControl : MatrixReadAt.Control := (none, none, (false, false), (false, false))

def program : Label → TM2.Stmt (fun _ : Fin 7 ⊕ Fin 3 => Bool) Label Control
  | .inl l => liftStmt (some .scan) (MatrixReadAt.program l)
  | .inr .test => pop (.inr 0) (fun s b => (s.1, b.isSome))
      (branch Prod.snd (goto (fun _ => .inl (.inl BitMachineCopy.Label.scan))) halt)
  | .inr .scan => pop (.inr 1) (fun s b => (s.1, b.isSome))
      (branch Prod.snd
        (push (.inl 0) (fun _ => true) (push (.inr 2) (fun _ => true)
          (goto (fun _ => .inr .scan)))) (goto (fun _ => .inr .restore)))
  | .inr .restore => pop (.inr 2) (fun s b => (s.1, b.isSome))
      (branch Prod.snd (push (.inr 1) (fun _ => true) (goto (fun _ => .inr .restore)))
        (goto (fun _ => .inr .test)))

def cfg (label : Option Label) (flag : Bool)
    (index source out counter stride work : List Bool) : Config :=
  ⟨label, (baseControl, flag),
    Sum.elim (![index, [], [], source, [], out, []] : Fin 7 → List Bool)
      (![counter, stride, work] : Fin 3 → List Bool)⟩

def run (n : ℕ) (c : Config) := ((advance program)^[n]) c

private theorem run_succ {c d : Config} (h : TM2.step program c = some d) (n : ℕ) :
    run (n + 1) c = run n d := by
  simp only [run, Function.iterate_succ_apply, advance, h, Option.getD_some]

private theorem run_add {c d : Config} {m : ℕ} (h : run m c = d) (n : ℕ) :
    run (m + n) c = run n d := by
  rw [Nat.add_comm m n]
  simp only [run, Function.iterate_add_apply] at h ⊢
  rw [h]

private theorem step_test_cons (flag : Bool) (idx source out counter stride : List Bool) :
    TM2.step program (cfg (some (.inr .test)) flag idx source out (true :: counter) stride []) =
      some (cfg (some (.inl (.inl BitMachineCopy.Label.scan))) true
        idx source out counter stride []) := by
  apply congrArg (fun S => some
    (⟨some (.inl (.inl BitMachineCopy.Label.scan)), (baseControl, true), S⟩ : Config))
  funext k
  cases k with
  | inl k => fin_cases k <;> rfl
  | inr k => fin_cases k <;> rfl

private theorem step_test_nil (flag : Bool) (idx source out stride : List Bool) :
    TM2.step program (cfg (some (.inr .test)) flag idx source out [] stride []) =
      some (cfg none false idx source out [] stride []) := by
  apply congrArg (fun S => some (⟨none, (baseControl, false), S⟩ : Config))
  funext k
  cases k with
  | inl k => fin_cases k <;> rfl
  | inr k => fin_cases k <;> rfl

private theorem step_scan_cons (flag : Bool) (idx source out counter stride work : List Bool) :
    TM2.step program
        (cfg (some (.inr .scan)) flag idx source out counter (true :: stride) work) =
      some (cfg (some (.inr .scan)) true (true :: idx) source out counter
        stride (true :: work)) := by
  apply congrArg (fun S => some (⟨some (.inr .scan), (baseControl, true), S⟩ : Config))
  funext k
  cases k with
  | inl k => fin_cases k <;> rfl
  | inr k => fin_cases k <;> rfl

private theorem step_scan_nil (flag : Bool) (idx source out counter work : List Bool) :
    TM2.step program (cfg (some (.inr .scan)) flag idx source out counter [] work) =
      some (cfg (some (.inr .restore)) false idx source out counter [] work) := by
  apply congrArg (fun S => some (⟨some (.inr .restore), (baseControl, false), S⟩ : Config))
  funext k
  cases k with
  | inl k => fin_cases k <;> rfl
  | inr k => fin_cases k <;> rfl

private theorem step_restore_cons (flag : Bool)
    (idx source out counter stride work : List Bool) :
    TM2.step program
        (cfg (some (.inr .restore)) flag idx source out counter stride (true :: work)) =
      some (cfg (some (.inr .restore)) true idx source out counter (true :: stride) work) := by
  apply congrArg (fun S => some (⟨some (.inr .restore), (baseControl, true), S⟩ : Config))
  funext k
  cases k with
  | inl k => fin_cases k <;> rfl
  | inr k => fin_cases k <;> rfl

private theorem step_restore_nil (flag : Bool) (idx source out counter stride : List Bool) :
    TM2.step program (cfg (some (.inr .restore)) flag idx source out counter stride []) =
      some (cfg (some (.inr .test)) false idx source out counter stride []) := by
  apply congrArg (fun S => some (⟨some (.inr .test), (baseControl, false), S⟩ : Config))
  funext k
  cases k with
  | inl k => fin_cases k <;> rfl
  | inr k => fin_cases k <;> rfl

theorem scan_run (n i k : ℕ) (flag : Bool) (source out counter : List Bool) :
    run (n + 1) (cfg (some (.inr .scan)) flag (List.replicate i true) source out counter
      (List.replicate n true) (List.replicate k true)) =
      cfg (some (.inr .restore)) false (List.replicate (n + i) true) source out counter
        [] (List.replicate (n + k) true) := by
  induction n generalizing i k flag with
  | zero =>
      simpa using run_succ (step_scan_nil flag (List.replicate i true) source out counter
        (List.replicate k true)) 0
  | succ n ih =>
      rw [List.replicate_succ, run_succ (step_scan_cons _ _ _ _ _ _ _) _]
      simpa only [← List.replicate_succ, Nat.add_assoc, Nat.add_comm 1 i,
        Nat.add_comm 1 k] using ih (i + 1) (k + 1) true

theorem restore_run (n k : ℕ) (flag : Bool) (idx source out counter : List Bool) :
    run (n + 1) (cfg (some (.inr .restore)) flag idx source out counter
      (List.replicate k true) (List.replicate n true)) =
      cfg (some (.inr .test)) false idx source out counter (List.replicate (n + k) true) [] := by
  induction n generalizing k flag with
  | zero =>
      simpa using run_succ (step_restore_nil flag idx source out counter (List.replicate k true)) 0
  | succ n ih =>
      rw [List.replicate_succ, run_succ (step_restore_cons _ _ _ _ _ _ _) _]
      simpa only [← List.replicate_succ, Nat.add_assoc, Nat.add_comm 1 k] using ih (k + 1) true

/-- Unary address addition preserves the stride and clears its temporary copy. -/
theorem increment_run (stride start : ℕ) (flag : Bool) (source out counter : List Bool) :
    run (2 * stride + 2) (cfg (some (.inr .scan)) flag (List.replicate start true)
      source out counter (List.replicate stride true) []) =
      cfg (some (.inr .test)) false (List.replicate (start + stride) true)
        source out counter (List.replicate stride true) [] := by
  have h₁ := scan_run stride start 0 flag source out counter
  have h₂ := restore_run stride 0 false (List.replicate (stride + start) true) source out counter
  simp only [Nat.add_zero, List.replicate_zero] at h₁ h₂
  have h := (run_add h₁ (stride + 1)).trans h₂
  simpa only [show stride + 1 + (stride + 1) = 2 * stride + 2 by omega,
    Nat.add_comm stride start] using h

theorem body_run (i : ℕ) (flag : Bool) (source out counter stride : List Bool) :
    ∃ t ≤ 3 * i + 3 * source.length + 8,
      run t (cfg (some (.inl (.inl BitMachineCopy.Label.scan))) flag
        (List.replicate i true) source out counter stride []) =
        cfg (some (.inr .scan)) flag (List.replicate i true) source
          (source[i]?.getD false :: out) counter stride [] := by
  obtain ⟨k, hk, hr⟩ := MatrixReadAt.readAt_run i source out
  have hh : (((advance MatrixReadAt.program)^[k])
      (MatrixReadAt.initial (List.replicate i true) source out)).l = none := by
    change (MatrixReadAt.run k _).l = none
    rw [hr]
    rfl
  obtain ⟨t, ht, hrun⟩ := lift_outputs MatrixReadAt.program program (some .scan)
    (fun _ => rfl) flag (![counter, stride, []] : Fin 3 → List Bool)
    (MatrixReadAt.initial (List.replicate i true) source out) k hh
  refine ⟨t, ht.trans hk, ?_⟩
  change run t _ = _ at hrun
  change (((advance MatrixReadAt.program)^[k]) _) = _ at hr
  rw [hr] at hrun
  exact hrun

def word (stride : ℕ) : ℕ → ℕ → List Bool → List Bool
  | _, 0, _ => []
  | start, width + 1, source =>
      source[start]?.getD false :: word stride (start + stride) width source

@[simp] theorem word_length (stride start width : ℕ) (source : List Bool) :
    (word stride start width source).length = width := by
  induction width generalizing start with
  | zero => rfl
  | succ w ih => simp [word, ih]

theorem word_eq_ofFn (stride start width : ℕ) (source : List Bool) :
    word stride start width source =
      List.ofFn (fun j : Fin width => source[start + j.val * stride]?.getD false) := by
  induction width generalizing start with
  | zero => simp [word]
  | succ w ih =>
      rw [word, List.ofFn_succ, ih]
      simp only [Fin.val_zero, Nat.zero_mul, Nat.add_zero, Fin.val_succ]
      congr 1
      apply congrArg List.ofFn
      funext j
      rw [show start + stride + j.val * stride = start + (j.val + 1) * stride by ring]

/-- Every indexed read, counter pop, and stride scan/restore is charged.
The final address advances even after the last read, as the statement records. -/
theorem gather_run (width start stride : ℕ) (flag : Bool) (source out : List Bool) :
    ∃ t ≤ width * (3 * (start + width * stride) + 3 * source.length + 2 * stride + 12) + 1,
      run t (cfg (some (.inr .test)) flag (List.replicate start true) source out
        (List.replicate width true) (List.replicate stride true) []) =
        cfg none false (List.replicate (start + width * stride) true) source
          ((word stride start width source).reverse ++ out) [] (List.replicate stride true) [] := by
  induction width generalizing start flag out with
  | zero =>
      refine ⟨1, by simp, ?_⟩
      simpa [word] using run_succ
        (step_test_nil flag (List.replicate start true) source out (List.replicate stride true)) 0
  | succ width ih =>
      have h₁ := run_succ (step_test_cons flag (List.replicate start true) source out
        (List.replicate width true) (List.replicate stride true)) 0
      obtain ⟨tb, htb, hb⟩ := body_run start true source out (List.replicate width true)
        (List.replicate stride true)
      have h₂ := increment_run stride start true source (source[start]?.getD false :: out)
        (List.replicate width true)
      obtain ⟨tr, htr, hr⟩ := ih (start + stride) false (source[start]?.getD false :: out)
      have h₁b := (run_add h₁ tb).trans hb
      have h₁b₂ := (run_add h₁b (2 * stride + 2)).trans h₂
      have hall := (run_add h₁b₂ tr).trans hr
      have he : start + stride + width * stride = start + (width + 1) * stride := by ring
      refine ⟨1 + tb + (2 * stride + 2) + tr, ?_, ?_⟩
      · rw [he] at htr
        nlinarith
      · simpa only [List.replicate_succ, word, List.reverse_cons, List.append_assoc,
          List.singleton_append, Nat.zero_add, he] using hall

/-- A row-major table's strided word is exactly its selected column. -/
theorem word_rowMajor_column {rows cols : ℕ} (f : Fin rows → Fin cols → Bool) (c : Fin cols) :
    word cols c.val rows (MatrixMaterialization.rowMajor f) = List.ofFn (fun r => f r c) := by
  rw [word_eq_ofFn]
  apply congrArg List.ofFn
  funext r
  rw [Nat.add_comm c.val, MatrixMaterialization.rowMajor_entry]
  rfl

/-- The actual controller gathers a complete matrix column from its literal
row-major table, preserving the table and the unary row stride. -/
theorem gather_column_run {rows cols : ℕ} (f : Fin rows → Fin cols → Bool) (c : Fin cols)
    (flag : Bool) (out : List Bool) :
    ∃ t ≤ rows * (3 * (c.val + rows * cols) + 3 * (rows * cols) + 2 * cols + 12) + 1,
      run t (cfg (some (.inr .test)) flag (List.replicate c.val true)
        (MatrixMaterialization.rowMajor f) out (List.replicate rows true)
        (List.replicate cols true) []) =
        cfg none false (List.replicate (c.val + rows * cols) true)
          (MatrixMaterialization.rowMajor f) ((List.ofFn (fun r => f r c)).reverse ++ out)
          [] (List.replicate cols true) [] := by
  simpa only [MatrixMaterialization.rowMajor_length, word_rowMajor_column] using
    gather_run rows c.val cols flag (MatrixMaterialization.rowMajor f) out

end EthInapproximability.CurrentPaper.MatrixStrideGather
