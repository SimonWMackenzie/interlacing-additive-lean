import EthInapproximability.CurrentPaper.U4PostExponent
import Paper2.SquarePadding

/-!
# U17 unary side, part 1: two new small Boolean-stack programs (lane owner:a-square-1)

Private, 26 September 2026. Two fixed finite programs, every step a literal `TM2` transition,
all stack contents unary (`true`-lists):

* `UMax` (5 stacks `0 m, 1 n, 2 out, 3 tm, 4 tn`): from unary `m`, `n` writes unary `max m n` on
  `out`, restoring `m` and `n` (lockstep scan, one-sided tail, two restores);
* `ULog` (3 stacks `0 y, 1 next, 2 e`): from unary `y` (consumed) adds unary `clog₂ y` to `e`
  by repeated ceiling halving (`y ↦ ⌈y/2⌉` while `y ≥ 2`, one unit of `e` per round).

These are inputs to the unary-side stage (`ASquareSide`) that produces the writer counters
`SquarePadding.side m n = 2^clog₂(max m n)` for the admitted `Unit4Shell.SquareWriter.square_table`.
Does not close a ledger row.
-/

namespace Paper2.ASquare

open Turing Turing.TM2.Stmt
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding

abbrev rp (n : ℕ) : List Bool := List.replicate n true

theorem rp_succ (n : ℕ) : rp (n + 1) = true :: rp n := by
  simp [rp, List.replicate_succ]

/-! ## `UMax` -/

namespace UMax

inductive Label where
  | scan | afterA | onlyM | onlyN | restoreM | restoreN
  deriving DecidableEq, Fintype

def program : Label → TM2.Stmt (fun _ : Fin 5 => Bool) Label Bool
  | .scan => pop 0 (fun _ b => b.isSome)
      (branch id (push 3 (fun _ => true) (push 2 (fun _ => true) (goto (fun _ => .afterA))))
        (goto (fun _ => .onlyN)))
  | .afterA => pop 1 (fun _ b => b.isSome)
      (branch id (push 4 (fun _ => true) (goto (fun _ => .scan))) (goto (fun _ => .onlyM)))
  | .onlyM => pop 0 (fun _ b => b.isSome)
      (branch id (push 3 (fun _ => true) (push 2 (fun _ => true) (goto (fun _ => .onlyM))))
        (goto (fun _ => .restoreM)))
  | .onlyN => pop 1 (fun _ b => b.isSome)
      (branch id (push 4 (fun _ => true) (push 2 (fun _ => true) (goto (fun _ => .onlyN))))
        (goto (fun _ => .restoreM)))
  | .restoreM => pop 3 (fun _ b => b.isSome)
      (branch id (push 0 (fun _ => true) (goto (fun _ => .restoreM))) (goto (fun _ => .restoreN)))
  | .restoreN => pop 4 (fun _ b => b.isSome)
      (branch id (push 1 (fun _ => true) (goto (fun _ => .restoreN))) halt)

abbrev Config := TM2.Cfg (fun _ : Fin 5 => Bool) Label Bool

def cfg (l : Option Label) (s : Bool) (a b o p q : List Bool) : Config := ⟨l, s, ![a, b, o, p, q]⟩

def run (n : ℕ) (c : Config) : Config := ((advance program)^[n]) c

theorem run_add (t u : ℕ) (c : Config) : run (t + u) c = run u (run t c) := by
  simp only [run]
  rw [Nat.add_comm, Function.iterate_add_apply]

theorem run_one (c : Config) : run 1 c = advance program c := rfl

theorem run_seq {t u : ℕ} {c c' c'' : Config} (h1 : run t c = c') (h2 : run u c' = c'') :
    run (t + u) c = c'' := by rw [run_add, h1, h2]

macro "step_tac" l:term:max v:term:max : tactic => `(tactic| (
  apply congrArg (fun S => (⟨$l, $v, S⟩ : Config))
  funext k
  fin_cases k <;> rfl))

theorem scan_cons (s : Bool) (a b o p q : List Bool) :
    advance program (cfg (some .scan) s (true :: a) b o p q) =
      cfg (some .afterA) true a b (true :: o) (true :: p) q := by step_tac (some .afterA) true
theorem scan_nil (s : Bool) (b o p q : List Bool) :
    advance program (cfg (some .scan) s [] b o p q) = cfg (some .onlyN) false [] b o p q := by
  step_tac (some .onlyN) false
theorem afterA_cons (s : Bool) (a b o p q : List Bool) :
    advance program (cfg (some .afterA) s a (true :: b) o p q) =
      cfg (some .scan) true a b o p (true :: q) := by step_tac (some .scan) true
theorem afterA_nil (s : Bool) (a o p q : List Bool) :
    advance program (cfg (some .afterA) s a [] o p q) = cfg (some .onlyM) false a [] o p q := by
  step_tac (some .onlyM) false
theorem onlyM_cons (s : Bool) (a b o p q : List Bool) :
    advance program (cfg (some .onlyM) s (true :: a) b o p q) =
      cfg (some .onlyM) true a b (true :: o) (true :: p) q := by step_tac (some .onlyM) true
theorem onlyM_nil (s : Bool) (b o p q : List Bool) :
    advance program (cfg (some .onlyM) s [] b o p q) = cfg (some .restoreM) false [] b o p q := by
  step_tac (some .restoreM) false
theorem onlyN_cons (s : Bool) (a b o p q : List Bool) :
    advance program (cfg (some .onlyN) s a (true :: b) o p q) =
      cfg (some .onlyN) true a b (true :: o) p (true :: q) := by step_tac (some .onlyN) true
theorem onlyN_nil (s : Bool) (a o p q : List Bool) :
    advance program (cfg (some .onlyN) s a [] o p q) = cfg (some .restoreM) false a [] o p q := by
  step_tac (some .restoreM) false
theorem restoreM_cons (s : Bool) (a b o p q : List Bool) :
    advance program (cfg (some .restoreM) s a b o (true :: p) q) =
      cfg (some .restoreM) true (true :: a) b o p q := by step_tac (some .restoreM) true
theorem restoreM_nil (s : Bool) (a b o q : List Bool) :
    advance program (cfg (some .restoreM) s a b o [] q) = cfg (some .restoreN) false a b o [] q := by
  step_tac (some .restoreN) false
theorem restoreN_cons (s : Bool) (a b o p q : List Bool) :
    advance program (cfg (some .restoreN) s a b o p (true :: q)) =
      cfg (some .restoreN) true a (true :: b) o p q := by step_tac (some .restoreN) true
theorem restoreN_nil (s : Bool) (a b o p : List Bool) :
    advance program (cfg (some .restoreN) s a b o p []) = cfg none false a b o p [] := by
  step_tac none false

theorem lock_run (j a b o p q : ℕ) (s : Bool) :
    ∃ s', run (2 * j) (cfg (some .scan) s (rp (a + j)) (rp (b + j)) (rp o) (rp p) (rp q)) =
      cfg (some .scan) s' (rp a) (rp b) (rp (o + j)) (rp (p + j)) (rp (q + j)) := by
  induction j generalizing o p q s with
  | zero => exact ⟨s, by simp [run]⟩
  | succ j ih =>
      obtain ⟨s', h⟩ := ih (o + 1) (p + 1) (q + 1) true
      refine ⟨s', ?_⟩
      have e1 : run 1 (cfg (some .scan) s (rp (a + (j + 1))) (rp (b + (j + 1))) (rp o) (rp p)
          (rp q)) = cfg (some .afterA) true (rp (a + j)) (rp (b + (j + 1))) (rp (o + 1))
            (rp (p + 1)) (rp q) := scan_cons s _ _ _ _ _
      have e2 : run 1 (cfg (some .afterA) true (rp (a + j)) (rp (b + (j + 1))) (rp (o + 1))
          (rp (p + 1)) (rp q)) = cfg (some .scan) true (rp (a + j)) (rp (b + j)) (rp (o + 1))
            (rp (p + 1)) (rp (q + 1)) := afterA_cons true _ _ _ _ _
      rw [show 2 * (j + 1) = 1 + 1 + 2 * j by ring, show o + (j + 1) = o + 1 + j by ring,
        show p + (j + 1) = p + 1 + j by ring, show q + (j + 1) = q + 1 + j by ring]
      exact run_seq (run_seq e1 e2) h

theorem onlyM_run (j o p : ℕ) (b q : List Bool) (s : Bool) :
    run (j + 1) (cfg (some .onlyM) s (rp j) b (rp o) (rp p) q) =
      cfg (some .restoreM) false [] b (rp (o + j)) (rp (p + j)) q := by
  induction j generalizing o p s with
  | zero => simpa [run] using onlyM_nil s b (rp o) (rp p) q
  | succ j ih =>
      have e1 : run 1 (cfg (some .onlyM) s (rp (j + 1)) b (rp o) (rp p) q) =
          cfg (some .onlyM) true (rp j) b (rp (o + 1)) (rp (p + 1)) q := onlyM_cons s _ _ _ _ _
      rw [show j + 1 + 1 = 1 + (j + 1) by ring, show o + (j + 1) = o + 1 + j by ring,
        show p + (j + 1) = p + 1 + j by ring]
      exact run_seq e1 (ih (o + 1) (p + 1) true)

theorem onlyN_run (j o q : ℕ) (a p : List Bool) (s : Bool) :
    run (j + 1) (cfg (some .onlyN) s a (rp j) (rp o) p (rp q)) =
      cfg (some .restoreM) false a [] (rp (o + j)) p (rp (q + j)) := by
  induction j generalizing o q s with
  | zero => simpa [run] using onlyN_nil s a (rp o) p (rp q)
  | succ j ih =>
      have e1 : run 1 (cfg (some .onlyN) s a (rp (j + 1)) (rp o) p (rp q)) =
          cfg (some .onlyN) true a (rp j) (rp (o + 1)) p (rp (q + 1)) := onlyN_cons s _ _ _ _ _
      rw [show j + 1 + 1 = 1 + (j + 1) by ring, show o + (j + 1) = o + 1 + j by ring,
        show q + (j + 1) = q + 1 + j by ring]
      exact run_seq e1 (ih (o + 1) (q + 1) true)

theorem restoreM_run (j i : ℕ) (b o q : List Bool) (s : Bool) :
    run (j + 1) (cfg (some .restoreM) s (rp i) b o (rp j) q) =
      cfg (some .restoreN) false (rp (i + j)) b o [] q := by
  induction j generalizing i s with
  | zero => simpa [run] using restoreM_nil s (rp i) b o q
  | succ j ih =>
      have e1 : run 1 (cfg (some .restoreM) s (rp i) b o (rp (j + 1)) q) =
          cfg (some .restoreM) true (rp (i + 1)) b o (rp j) q := restoreM_cons s _ _ _ _ _
      rw [show j + 1 + 1 = 1 + (j + 1) by ring, show i + (j + 1) = i + 1 + j by ring]
      exact run_seq e1 (ih (i + 1) true)

theorem restoreN_run (j i : ℕ) (a o p : List Bool) (s : Bool) :
    run (j + 1) (cfg (some .restoreN) s a (rp i) o p (rp j)) =
      cfg none false a (rp (i + j)) o p [] := by
  induction j generalizing i s with
  | zero => simpa [run] using restoreN_nil s a (rp i) o p
  | succ j ih =>
      have e1 : run 1 (cfg (some .restoreN) s a (rp i) o p (rp (j + 1))) =
          cfg (some .restoreN) true a (rp (i + 1)) o p (rp j) := restoreN_cons s _ _ _ _ _
      rw [show j + 1 + 1 = 1 + (j + 1) by ring, show i + (j + 1) = i + 1 + j by ring]
      exact run_seq e1 (ih (i + 1) true)

/-- **Unary maximum.** From unary `m`, `n` (other stacks empty) the fixed program halts with `m`,
`n` restored, unary `max m n` on `out`, both temporaries empty, within `3(m+n)+6` steps. -/
theorem max_run (m n : ℕ) :
    ∃ t ≤ 3 * (m + n) + 6, ∃ v,
      run t (cfg (some .scan) false (rp m) (rp n) [] [] []) =
        cfg none v (rp m) (rp n) (rp (max m n)) [] [] := by
  by_cases hmn : m ≤ n
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hmn
    obtain ⟨s', h1⟩ := lock_run m 0 d 0 0 0 false
    simp only [Nat.zero_add, Nat.add_comm d m] at h1
    have hs : run 1 (cfg (some .scan) s' (rp 0) (rp d) (rp m) (rp m) (rp m)) =
        cfg (some .onlyN) false [] (rp d) (rp m) (rp m) (rp m) := scan_nil s' _ _ _ _
    have h2 := onlyN_run d m m [] (rp m) false
    have h3 := restoreM_run m 0 [] (rp (m + d)) (rp (m + d)) false
    have h4 := restoreN_run (m + d) 0 (rp m) (rp (m + d)) [] false
    simp only [Nat.zero_add] at h3 h4
    refine ⟨2 * m + 1 + (d + 1) + (m + 1) + (m + d + 1), by omega, false, ?_⟩
    rw [show max m (m + d) = m + d by omega]
    exact run_seq (run_seq (run_seq (run_seq h1 hs) h2) h3) h4
  · have hnm : n < m := by omega
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hnm
    obtain ⟨s', h1⟩ := lock_run n (d + 1) 0 0 0 0 false
    simp only [Nat.zero_add] at h1
    rw [show d + 1 + n = n + 1 + d by ring] at h1
    have hs1 : run 1 (cfg (some .scan) s' (rp (d + 1)) (rp 0) (rp n) (rp n) (rp n)) =
        cfg (some .afterA) true (rp d) (rp 0) (rp (n + 1)) (rp (n + 1)) (rp n) :=
      scan_cons s' _ _ _ _ _
    have hs2 : run 1 (cfg (some .afterA) true (rp d) (rp 0) (rp (n + 1)) (rp (n + 1)) (rp n)) =
        cfg (some .onlyM) false (rp d) [] (rp (n + 1)) (rp (n + 1)) (rp n) :=
      afterA_nil true _ _ _ _
    have h2 := onlyM_run d (n + 1) (n + 1) [] (rp n) false
    have h3 := restoreM_run (n + 1 + d) 0 [] (rp (n + 1 + d)) (rp n) false
    have h4 := restoreN_run n 0 (rp (n + 1 + d)) (rp (n + 1 + d)) [] false
    simp only [Nat.zero_add] at h3 h4
    refine ⟨2 * n + 1 + 1 + (d + 1) + (n + 1 + d + 1) + (n + 1), by omega, false, ?_⟩
    rw [show max (n + d + 1) n = n + 1 + d by omega, show n + d + 1 = n + 1 + d by ring]
    exact run_seq (run_seq (run_seq (run_seq (run_seq h1 hs1) hs2) h2) h3) h4

end UMax

/-! ## `ULog` -/

namespace ULog

inductive Label where
  | check | check2 | half | half2 | back
  deriving DecidableEq, Fintype

def program : Label → TM2.Stmt (fun _ : Fin 3 => Bool) Label Bool
  | .check => pop 0 (fun _ b => b.isSome) (branch id (goto (fun _ => .check2)) halt)
  | .check2 => pop 0 (fun _ b => b.isSome)
      (branch id (push 2 (fun _ => true) (push 1 (fun _ => true) (goto (fun _ => .half)))) halt)
  | .half => pop 0 (fun _ b => b.isSome)
      (branch id (push 1 (fun _ => true) (goto (fun _ => .half2))) (goto (fun _ => .back)))
  | .half2 => pop 0 (fun _ b => b.isSome)
      (branch id (goto (fun _ => .half)) (goto (fun _ => .back)))
  | .back => pop 1 (fun _ b => b.isSome)
      (branch id (push 0 (fun _ => true) (goto (fun _ => .back))) (goto (fun _ => .check)))

abbrev Config := TM2.Cfg (fun _ : Fin 3 => Bool) Label Bool

def cfg (l : Option Label) (s : Bool) (y b e : List Bool) : Config := ⟨l, s, ![y, b, e]⟩

def run (n : ℕ) (c : Config) : Config := ((advance program)^[n]) c

theorem run_add (t u : ℕ) (c : Config) : run (t + u) c = run u (run t c) := by
  simp only [run]
  rw [Nat.add_comm, Function.iterate_add_apply]

theorem run_one (c : Config) : run 1 c = advance program c := rfl

theorem run_seq {t u : ℕ} {c c' c'' : Config} (h1 : run t c = c') (h2 : run u c' = c'') :
    run (t + u) c = c'' := by rw [run_add, h1, h2]

macro "step_tac" l:term:max v:term:max : tactic => `(tactic| (
  apply congrArg (fun S => (⟨$l, $v, S⟩ : Config))
  funext k
  fin_cases k <;> rfl))

theorem check_cons (s : Bool) (y b e : List Bool) :
    advance program (cfg (some .check) s (true :: y) b e) = cfg (some .check2) true y b e := by
  step_tac (some .check2) true
theorem check_nil (s : Bool) (b e : List Bool) :
    advance program (cfg (some .check) s [] b e) = cfg none false [] b e := by step_tac none false
theorem check2_cons (s : Bool) (y b e : List Bool) :
    advance program (cfg (some .check2) s (true :: y) b e) =
      cfg (some .half) true y (true :: b) (true :: e) := by step_tac (some .half) true
theorem check2_nil (s : Bool) (b e : List Bool) :
    advance program (cfg (some .check2) s [] b e) = cfg none false [] b e := by step_tac none false
theorem half_cons (s : Bool) (y b e : List Bool) :
    advance program (cfg (some .half) s (true :: y) b e) =
      cfg (some .half2) true y (true :: b) e := by step_tac (some .half2) true
theorem half_nil (s : Bool) (b e : List Bool) :
    advance program (cfg (some .half) s [] b e) = cfg (some .back) false [] b e := by step_tac (some .back) false
theorem half2_cons (s : Bool) (y b e : List Bool) :
    advance program (cfg (some .half2) s (true :: y) b e) = cfg (some .half) true y b e := by
  step_tac (some .half) true
theorem half2_nil (s : Bool) (b e : List Bool) :
    advance program (cfg (some .half2) s [] b e) = cfg (some .back) false [] b e := by step_tac (some .back) false
theorem back_cons (s : Bool) (y b e : List Bool) :
    advance program (cfg (some .back) s y (true :: b) e) = cfg (some .back) true (true :: y) b e := by
  step_tac (some .back) true
theorem back_nil (s : Bool) (y e : List Bool) :
    advance program (cfg (some .back) s y [] e) = cfg (some .check) false y [] e := by step_tac (some .check) false

theorem half_pairs (i r b : ℕ) (e : List Bool) (s : Bool) :
    ∃ s', run (2 * i) (cfg (some .half) s (rp (r + 2 * i)) (rp b) e) =
      cfg (some .half) s' (rp r) (rp (b + i)) e := by
  induction i generalizing b s with
  | zero => exact ⟨s, by simp [run]⟩
  | succ i ih =>
      obtain ⟨s', h⟩ := ih (b + 1) true
      refine ⟨s', ?_⟩
      have e1 : run 1 (cfg (some .half) s (rp (r + 2 * i + 1 + 1)) (rp b) e) =
          cfg (some .half2) true (rp (r + 2 * i + 1)) (rp (b + 1)) e := half_cons s _ _ _
      have e2 : run 1 (cfg (some .half2) true (rp (r + 2 * i + 1)) (rp (b + 1)) e) =
          cfg (some .half) true (rp (r + 2 * i)) (rp (b + 1)) e := half2_cons true _ _ _
      rw [show r + 2 * (i + 1) = r + 2 * i + 1 + 1 by ring,
        show 2 * (i + 1) = 1 + 1 + 2 * i by ring, show b + (i + 1) = b + 1 + i by ring]
      exact run_seq (run_seq e1 e2) h

theorem back_run (j i : ℕ) (e : List Bool) (s : Bool) :
    run (j + 1) (cfg (some .back) s (rp i) (rp j) e) =
      cfg (some .check) false (rp (i + j)) [] e := by
  induction j generalizing i s with
  | zero => simpa [run] using back_nil s (rp i) e
  | succ j ih =>
      have e1 : run 1 (cfg (some .back) s (rp i) (rp (j + 1)) e) =
          cfg (some .back) true (rp (i + 1)) (rp j) e := back_cons s _ _ _
      rw [show j + 1 + 1 = 1 + (j + 1) by ring, show i + (j + 1) = i + 1 + j by ring]
      exact run_seq e1 (ih (i + 1) true)

/-- One halving round on `y ≥ 2`: `y ↦ (y+1)/2 = ⌈y/2⌉`, `e ↦ e+1`, within `3y+5` steps. -/
theorem round_run (y e : ℕ) (hy : 2 ≤ y) (s : Bool) :
    ∃ t ≤ 3 * y + 5, ∃ s',
      run t (cfg (some .check) s (rp y) [] (rp e)) =
        cfg (some .check) s' (rp ((y + 1) / 2)) [] (rp (e + 1)) := by
  obtain ⟨r, rfl⟩ : ∃ r, y = r + 2 := ⟨y - 2, by omega⟩
  have h1 : run 1 (cfg (some .check) s (rp (r + 2)) [] (rp e)) =
      cfg (some .check2) true (rp (r + 1)) [] (rp e) := check_cons s _ _ _
  have h2 : run 1 (cfg (some .check2) true (rp (r + 1)) [] (rp e)) =
      cfg (some .half) true (rp r) (rp 1) (rp (e + 1)) := check2_cons true _ _ _
  rcases Nat.even_or_odd r with ⟨i, hi⟩ | ⟨i, hi⟩
  · -- `r = 2i`: `i` pairs, then `half` on the empty stack
    subst hi
    obtain ⟨s', h3⟩ := half_pairs i 0 1 (rp (e + 1)) true
    rw [show 0 + 2 * i = i + i by ring] at h3
    have h4 : run 1 (cfg (some .half) s' (rp 0) (rp (1 + i)) (rp (e + 1))) =
        cfg (some .back) false [] (rp (1 + i)) (rp (e + 1)) := half_nil s' _ _
    have h5 := back_run (1 + i) 0 (rp (e + 1)) false
    refine ⟨1 + 1 + 2 * i + 1 + (1 + i + 1), by omega, false, ?_⟩
    rw [show (i + i + 2 + 1) / 2 = 0 + (1 + i) by omega]
    exact run_seq (run_seq (run_seq (run_seq h1 h2) h3) h4) h5
  · -- `r = 2i+1`: `i` pairs, then one single and `half2` on the empty stack
    subst hi
    obtain ⟨s', h3⟩ := half_pairs i 1 1 (rp (e + 1)) true
    rw [show 1 + 2 * i = 2 * i + 1 by ring] at h3
    have h4 : run 1 (cfg (some .half) s' (rp 1) (rp (1 + i)) (rp (e + 1))) =
        cfg (some .half2) true [] (rp (1 + i + 1)) (rp (e + 1)) := half_cons s' _ _ _
    have h5 : run 1 (cfg (some .half2) true [] (rp (1 + i + 1)) (rp (e + 1))) =
        cfg (some .back) false [] (rp (1 + i + 1)) (rp (e + 1)) := half2_nil true _ _
    have h6 := back_run (1 + i + 1) 0 (rp (e + 1)) false
    refine ⟨1 + 1 + 2 * i + 1 + 1 + (1 + i + 1 + 1), by omega, false, ?_⟩
    rw [show (2 * i + 1 + 2 + 1) / 2 = 0 + (1 + i + 1) by omega]
    exact run_seq (run_seq (run_seq (run_seq (run_seq h1 h2) h3) h4) h5) h6

/-- **Unary ceiling logarithm.** From unary `y` (consumed), the fixed program halts with
`e ↦ e + clog₂ y`, both other stacks empty, within `(3y+5)(clog₂ y + 1)` steps. -/
theorem log_run (y e : ℕ) (s : Bool) :
    ∃ t ≤ (3 * y + 5) * (Nat.clog 2 y + 1), ∃ s',
      run t (cfg (some .check) s (rp y) [] (rp e)) =
        cfg none s' [] [] (rp (e + Nat.clog 2 y)) := by
  induction y using Nat.strong_induction_on generalizing e s with
  | _ y ih =>
    by_cases hy : y < 2
    · rw [Nat.clog_of_right_le_one (by omega), Nat.add_zero]
      rcases (show y = 0 ∨ y = 1 by omega) with rfl | rfl
      · exact ⟨1, by omega, false, check_nil s [] (rp e)⟩
      · exact ⟨1 + 1, by omega, false,
          run_seq (check_cons s [] [] (rp e)) (check2_nil true [] (rp e))⟩
    · have hy : 2 ≤ y := by omega
      obtain ⟨t1, ht1, s1, h1⟩ := round_run y e hy s
      have hlt : (y + 1) / 2 < y := by omega
      obtain ⟨t2, ht2, s2, h2⟩ := ih ((y + 1) / 2) hlt (e + 1) s1
      have hclog : Nat.clog 2 y = Nat.clog 2 ((y + 1) / 2) + 1 := by
        rw [Nat.clog_of_two_le (by norm_num) hy, show y + 2 - 1 = y + 1 by omega]
      refine ⟨t1 + t2, ?_, s2, ?_⟩
      · rw [hclog]
        have hle : 3 * ((y + 1) / 2) + 5 ≤ 3 * y + 5 := by omega
        have := Nat.mul_le_mul hle (le_refl (Nat.clog 2 ((y + 1) / 2) + 1))
        nlinarith
      · rw [hclog, show e + (Nat.clog 2 ((y + 1) / 2) + 1) =
          e + 1 + Nat.clog 2 ((y + 1) / 2) by ring]
        exact run_seq h1 h2

end ULog

end Paper2.ASquare
