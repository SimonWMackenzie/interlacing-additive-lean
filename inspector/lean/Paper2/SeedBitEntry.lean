import EthInapproximability.CurrentPaper.BitMachineEncoding

/-!
# WP-SEED, part 1: the physical coordinate-bit entry program

Lane `owner:a-seed-t45-1` (private, 26 September 2026).

One fixed Boolean-stack program on six stacks (`0` = unary row index `x`, `1` = unary column
index `y`, `2` = answer, `3`/`4`/`5` = scratch `A`, `B`, `Ys`) with a finite label set and the
finite control `Option Bool × Bool`. From blank scratch it copies `x` into `A`, halves `A`
exactly `y` times (unary pair-popping, remainder discarded), reads the parity of `A`, pushes that
bit into the answer stack and restores `y`. Every step is a literal `TM2.step`; nothing is
installed. The answer is `Nat.testBit x y` (little-endian bit `y` of `x`).
-/

namespace SeedT45.BitEntry

open Turing TM2.Stmt
open EthInapproximability.CurrentPaper.BitMachineEncoding

inductive Label where
  | cpx | rsx | ylp | h1 | h2 | mv | par | ry
  deriving DecidableEq, Fintype

abbrev Ctl := Option Bool × Bool

def setP (v : Ctl) (o : Option Bool) : Ctl := (o, v.2)

def program : Label → TM2.Stmt (fun _ : Fin 6 => Bool) Label Ctl
  | .cpx => pop 0 setP (branch (fun v => v.1.isSome)
      (push 4 (fun _ => true) (goto fun _ => .cpx)) (goto fun _ => .rsx))
  | .rsx => pop 4 setP (branch (fun v => v.1.isSome)
      (push 0 (fun _ => true) (push 3 (fun _ => true) (goto fun _ => .rsx)))
      (goto fun _ => .ylp))
  | .ylp => pop 1 setP (branch (fun v => v.1.isSome)
      (push 5 (fun _ => true) (goto fun _ => .h1)) (goto fun _ => .par))
  | .h1 => pop 3 setP (branch (fun v => v.1.isSome)
      (goto fun _ => .h2) (goto fun _ => .mv))
  | .h2 => pop 3 setP (branch (fun v => v.1.isSome)
      (push 4 (fun _ => true) (goto fun _ => .h1)) (goto fun _ => .mv))
  | .mv => pop 4 setP (branch (fun v => v.1.isSome)
      (push 3 (fun _ => true) (goto fun _ => .mv)) (goto fun _ => .ylp))
  | .par => pop 3 setP (branch (fun v => v.1.isSome)
      (load (fun v => (v.1, !v.2)) (goto fun _ => .par))
      (push 2 (fun v => v.2) (goto fun _ => .ry)))
  | .ry => pop 5 setP (branch (fun v => v.1.isSome)
      (push 1 (fun _ => true) (goto fun _ => .ry)) halt)

def st (x y ans a b ys : List Bool) : Fin 6 → List Bool :=
  fun k => if k = 0 then x else if k = 1 then y else if k = 2 then ans else
    if k = 3 then a else if k = 4 then b else ys

@[simp] theorem st0 (x y ans a b ys : List Bool) : st x y ans a b ys 0 = x := rfl
@[simp] theorem st1 (x y ans a b ys : List Bool) : st x y ans a b ys 1 = y := rfl
@[simp] theorem st2 (x y ans a b ys : List Bool) : st x y ans a b ys 2 = ans := rfl
@[simp] theorem st3 (x y ans a b ys : List Bool) : st x y ans a b ys 3 = a := rfl
@[simp] theorem st4 (x y ans a b ys : List Bool) : st x y ans a b ys 4 = b := rfl
@[simp] theorem st5 (x y ans a b ys : List Bool) : st x y ans a b ys 5 = ys := rfl

abbrev Cfg := TM2.Cfg (fun _ : Fin 6 => Bool) Label Ctl

def cfg (l : Option Label) (v : Ctl) (x y ans a b ys : List Bool) : Cfg :=
  ⟨l, v, st x y ans a b ys⟩

def run (n : ℕ) (c : Cfg) : Cfg := ((advance program)^[n]) c

def u (k : ℕ) : List Bool := List.replicate k true

theorem u_succ (k : ℕ) : u (k + 1) = true :: u k := rfl

theorem run_succ {c d : Cfg} (h : TM2.step program c = some d) (n : ℕ) :
    run (n + 1) c = run n d := by
  simp only [run, Function.iterate_succ_apply, advance, h, Option.getD_some]

theorem run_add {c d : Cfg} {m : ℕ} (h : run m c = d) (n : ℕ) :
    run (m + n) c = run n d := by
  rw [Nat.add_comm m n]
  simp only [run, Function.iterate_add_apply] at h ⊢
  rw [h]

/-! ### Single steps -/

theorem s_cpx_c (v : Ctl) (k : ℕ) (y ans a b ys : List Bool) :
    TM2.step program (cfg (some .cpx) v (u (k + 1)) y ans a b ys) =
      some (cfg (some .cpx) (some true, v.2) (u k) y ans a (true :: b) ys) := by
  simp [TM2.step, TM2.stepAux, program, cfg, setP, u_succ]
  funext i; fin_cases i <;> rfl

theorem s_cpx_n (v : Ctl) (y ans a b ys : List Bool) :
    TM2.step program (cfg (some .cpx) v [] y ans a b ys) =
      some (cfg (some .rsx) (none, v.2) [] y ans a b ys) := by
  simp [TM2.step, TM2.stepAux, program, cfg, setP]

theorem s_rsx_c (v : Ctl) (k : ℕ) (x y ans a ys : List Bool) :
    TM2.step program (cfg (some .rsx) v x y ans a (u (k + 1)) ys) =
      some (cfg (some .rsx) (some true, v.2) (true :: x) y ans (true :: a) (u k) ys) := by
  simp [TM2.step, TM2.stepAux, program, cfg, setP, u_succ]
  funext i; fin_cases i <;> rfl

theorem s_rsx_n (v : Ctl) (x y ans a ys : List Bool) :
    TM2.step program (cfg (some .rsx) v x y ans a [] ys) =
      some (cfg (some .ylp) (none, v.2) x y ans a [] ys) := by
  simp [TM2.step, TM2.stepAux, program, cfg, setP]

theorem s_ylp_c (v : Ctl) (k : ℕ) (x ans a b ys : List Bool) :
    TM2.step program (cfg (some .ylp) v x (u (k + 1)) ans a b ys) =
      some (cfg (some .h1) (some true, v.2) x (u k) ans a b (true :: ys)) := by
  simp [TM2.step, TM2.stepAux, program, cfg, setP, u_succ]
  funext i; fin_cases i <;> rfl

theorem s_ylp_n (v : Ctl) (x ans a b ys : List Bool) :
    TM2.step program (cfg (some .ylp) v x [] ans a b ys) =
      some (cfg (some .par) (none, v.2) x [] ans a b ys) := by
  simp [TM2.step, TM2.stepAux, program, cfg, setP]

theorem s_h1_c (v : Ctl) (k : ℕ) (x y ans b ys : List Bool) :
    TM2.step program (cfg (some .h1) v x y ans (u (k + 1)) b ys) =
      some (cfg (some .h2) (some true, v.2) x y ans (u k) b ys) := by
  simp [TM2.step, TM2.stepAux, program, cfg, setP, u_succ]
  funext i; fin_cases i <;> rfl

theorem s_h1_n (v : Ctl) (x y ans b ys : List Bool) :
    TM2.step program (cfg (some .h1) v x y ans [] b ys) =
      some (cfg (some .mv) (none, v.2) x y ans [] b ys) := by
  simp [TM2.step, TM2.stepAux, program, cfg, setP]

theorem s_h2_c (v : Ctl) (k : ℕ) (x y ans b ys : List Bool) :
    TM2.step program (cfg (some .h2) v x y ans (u (k + 1)) b ys) =
      some (cfg (some .h1) (some true, v.2) x y ans (u k) (true :: b) ys) := by
  simp [TM2.step, TM2.stepAux, program, cfg, setP, u_succ]
  funext i; fin_cases i <;> rfl

theorem s_h2_n (v : Ctl) (x y ans b ys : List Bool) :
    TM2.step program (cfg (some .h2) v x y ans [] b ys) =
      some (cfg (some .mv) (none, v.2) x y ans [] b ys) := by
  simp [TM2.step, TM2.stepAux, program, cfg, setP]

theorem s_mv_c (v : Ctl) (k : ℕ) (x y ans a ys : List Bool) :
    TM2.step program (cfg (some .mv) v x y ans a (u (k + 1)) ys) =
      some (cfg (some .mv) (some true, v.2) x y ans (true :: a) (u k) ys) := by
  simp [TM2.step, TM2.stepAux, program, cfg, setP, u_succ]
  funext i; fin_cases i <;> rfl

theorem s_mv_n (v : Ctl) (x y ans a ys : List Bool) :
    TM2.step program (cfg (some .mv) v x y ans a [] ys) =
      some (cfg (some .ylp) (none, v.2) x y ans a [] ys) := by
  simp [TM2.step, TM2.stepAux, program, cfg, setP]

theorem s_par_c (v : Ctl) (k : ℕ) (x y ans b ys : List Bool) :
    TM2.step program (cfg (some .par) v x y ans (u (k + 1)) b ys) =
      some (cfg (some .par) (some true, !v.2) x y ans (u k) b ys) := by
  simp [TM2.step, TM2.stepAux, program, cfg, setP, u_succ]
  funext i; fin_cases i <;> rfl

theorem s_par_n (v : Ctl) (x y ans b ys : List Bool) :
    TM2.step program (cfg (some .par) v x y ans [] b ys) =
      some (cfg (some .ry) (none, v.2) x y (v.2 :: ans) [] b ys) := by
  simp [TM2.step, TM2.stepAux, program, cfg, setP]
  funext i; fin_cases i <;> rfl

theorem s_ry_c (v : Ctl) (k : ℕ) (x y ans a b : List Bool) :
    TM2.step program (cfg (some .ry) v x y ans a b (u (k + 1))) =
      some (cfg (some .ry) (some true, v.2) x (true :: y) ans a b (u k)) := by
  simp [TM2.step, TM2.stepAux, program, cfg, setP, u_succ]
  funext i; fin_cases i <;> rfl

theorem s_ry_n (v : Ctl) (x y ans a b : List Bool) :
    TM2.step program (cfg (some .ry) v x y ans a b []) =
      some (cfg none (none, v.2) x y ans a b []) := by
  simp [TM2.step, TM2.stepAux, program, cfg, setP]

/-! ### Loops -/

theorem cpx_loop (k : ℕ) : ∀ (v : Ctl) (m : ℕ) (y ans a ys : List Bool),
    run (k + 1) (cfg (some .cpx) v (u k) y ans a (u m) ys) =
      cfg (some .rsx) (none, v.2) [] y ans a (u (k + m)) ys := by
  induction k with
  | zero => intro v m y ans a ys; simpa [u] using run_succ (s_cpx_n v y ans a (u m) ys) 0
  | succ k ih =>
      intro v m y ans a ys
      rw [run_succ (s_cpx_c v k y ans a (u m) ys), ← u_succ, ih]
      rw [show k + (m + 1) = k + 1 + m by omega]

theorem rsx_loop (k : ℕ) : ∀ (v : Ctl) (x0 a : ℕ) (y ans ys : List Bool),
    run (k + 1) (cfg (some .rsx) v (u x0) y ans (u a) (u k) ys) =
      cfg (some .ylp) (none, v.2) (u (k + x0)) y ans (u (k + a)) [] ys := by
  induction k with
  | zero => intro v x0 a y ans ys; simpa [u] using run_succ (s_rsx_n v (u x0) y ans (u a) ys) 0
  | succ k ih =>
      intro v x0 a y ans ys
      rw [run_succ (s_rsx_c v k (u x0) y ans (u a) ys), ← u_succ, ← u_succ, ih]
      rw [show k + (x0 + 1) = k + 1 + x0 by omega, show k + (a + 1) = k + 1 + a by omega]

theorem halve_loop (a : ℕ) : ∀ (v : Ctl) (b : ℕ) (x y ans ys : List Bool),
    run (a + 1) (cfg (some .h1) v x y ans (u a) (u b) ys) =
      cfg (some .mv) (none, v.2) x y ans [] (u (b + a / 2)) ys := by
  induction a using Nat.strong_induction_on with
  | _ a ih =>
    intro v b x y ans ys
    match a, ih with
    | 0, _ => simpa [u] using run_succ (s_h1_n v x y ans (u b) ys) 0
    | 1, _ =>
        rw [run_succ (s_h1_c v 0 x y ans (u b) ys)]
        simpa [u] using run_succ (s_h2_n (some true, v.2) x y ans (u b) ys) 0
    | a + 2, ih =>
        rw [show a + 2 + 1 = (a + 1) + 1 + 1 by omega,
          run_succ (s_h1_c v (a + 1) x y ans (u b) ys),
          run_succ (s_h2_c (some true, v.2) a x y ans (u b) ys), ← u_succ,
          ih a (by omega) (some true, v.2) (b + 1) x y ans ys]
        rw [show b + 1 + a / 2 = b + (a + 2) / 2 by omega]

theorem mv_loop (m : ℕ) : ∀ (v : Ctl) (a : ℕ) (x y ans ys : List Bool),
    run (m + 1) (cfg (some .mv) v x y ans (u a) (u m) ys) =
      cfg (some .ylp) (none, v.2) x y ans (u (m + a)) [] ys := by
  induction m with
  | zero => intro v a x y ans ys; simpa [u] using run_succ (s_mv_n v x y ans (u a) ys) 0
  | succ m ih =>
      intro v a x y ans ys
      rw [run_succ (s_mv_c v m x y ans (u a) ys), ← u_succ, ih]
      rw [show m + (a + 1) = m + 1 + a by omega]

theorem ylp_loop (k : ℕ) : ∀ (v : Ctl) (a ms : ℕ) (x ans : List Bool),
    ∃ t ≤ k * (2 * a + 3) + 1,
      run t (cfg (some .ylp) v x (u k) ans (u a) [] (u ms)) =
        cfg (some .par) (none, v.2) x [] ans (u (a / 2 ^ k)) [] (u (k + ms)) := by
  induction k with
  | zero =>
      intro v a ms x ans
      exact ⟨1, by omega, by simpa [u] using run_succ (s_ylp_n v x ans (u a) [] (u ms)) 0⟩
  | succ k ih =>
      intro v a ms x ans
      obtain ⟨t, ht, hr⟩ := ih (none, v.2) (a / 2) (ms + 1) x ans
      have h1 : run (1 + (a + 1)) (cfg (some .ylp) v x (u (k + 1)) ans (u a) [] (u ms)) =
          cfg (some .mv) (none, v.2) x (u k) ans [] (u (a / 2)) (u (ms + 1)) := by
        rw [Nat.add_comm, run_succ (s_ylp_c v k x ans (u a) [] (u ms)), ← u_succ]
        simpa [u] using halve_loop a (some true, v.2) 0 x (u k) ans (u (ms + 1))
      have h2 : run (a / 2 + 1) (cfg (some .mv) (none, v.2) x (u k) ans [] (u (a / 2)) (u (ms + 1))) =
          cfg (some .ylp) (none, v.2) x (u k) ans (u (a / 2)) [] (u (ms + 1)) := by
        simpa using mv_loop (a / 2) (none, v.2) 0 x (u k) ans (u (ms + 1))
      refine ⟨1 + (a + 1) + (a / 2 + 1) + t, ?_, ?_⟩
      · have hk : k * (2 * (a / 2) + 3) ≤ k * (2 * a + 3) :=
          Nat.mul_le_mul_left _ (by omega)
        have : a / 2 ≤ a := Nat.div_le_self a 2
        nlinarith
      · rw [run_add (run_add h1 _) _, h2, hr]
        rw [Nat.div_div_eq_div_mul, ← pow_succ', show k + (ms + 1) = k + 1 + ms by omega]

theorem par_loop (a : ℕ) : ∀ (v : Ctl) (x y ans b ys : List Bool),
    run (a + 1) (cfg (some .par) v x y ans (u a) b ys) =
      cfg (some .ry) (none, xor v.2 (Nat.bodd a)) x y (xor v.2 (Nat.bodd a) :: ans) [] b ys := by
  induction a with
  | zero => intro v x y ans b ys; simpa [u] using run_succ (s_par_n v x y ans b ys) 0
  | succ a ih =>
      intro v x y ans b ys
      rw [run_succ (s_par_c v a x y ans b ys), ih]
      rcases v with ⟨o, p⟩
      simp only [Nat.bodd_succ]
      cases p <;> cases Nat.bodd a <;> rfl

theorem ry_loop (m : ℕ) : ∀ (v : Ctl) (k : ℕ) (x ans a b : List Bool),
    run (m + 1) (cfg (some .ry) v x (u k) ans a b (u m)) =
      cfg none (none, v.2) x (u (m + k)) ans a b [] := by
  induction m with
  | zero => intro v k x ans a b; simpa [u] using run_succ (s_ry_n v x (u k) ans a b) 0
  | succ m ih =>
      intro v k x ans a b
      rw [run_succ (s_ry_c v m x (u k) ans a b), ← u_succ, ih]
      rw [show m + (k + 1) = m + 1 + k by omega]

/-! ### The whole entry run -/

def entryTime (x y : ℕ) : ℕ := (x + 1) + (x + 1) + (y * (2 * x + 3) + 1) + (x + 1) + (y + 1)

theorem bodd_div_eq_testBit (x y : ℕ) : Nat.bodd (x / 2 ^ y) = Nat.testBit x y := by
  rw [Nat.testBit_eq_decide_div_mod_eq]
  rcases Nat.mod_two_eq_zero_or_one (x / 2 ^ y) with h | h
  · have hb : Nat.bodd (x / 2 ^ y) = false := by
      rw [Nat.mod_two_of_bodd] at h
      cases hb : Nat.bodd (x / 2 ^ y) <;> simp_all
    simp [hb, h]
  · have hb : Nat.bodd (x / 2 ^ y) = true := by
      rw [Nat.mod_two_of_bodd] at h
      cases hb : Nat.bodd (x / 2 ^ y) <;> simp_all
    simp [hb, h]

theorem entry_run (x y : ℕ) :
    ∃ t ≤ entryTime x y, ∃ v : Ctl,
      run t (cfg (some .cpx) (none, false) (u x) (u y) [] [] [] []) =
        cfg none v (u x) (u y) [Nat.testBit x y] [] [] [] := by
  have h1 : run (x + 1) (cfg (some .cpx) (none, false) (u x) (u y) [] [] [] []) =
      cfg (some .rsx) (none, false) [] (u y) [] [] (u x) [] := by
    simpa [u] using cpx_loop x (none, false) 0 (u y) [] [] []
  have h2 : run (x + 1) (cfg (some .rsx) (none, false) [] (u y) [] [] (u x) []) =
      cfg (some .ylp) (none, false) (u x) (u y) [] (u x) [] [] := by
    simpa [u] using rsx_loop x (none, false) 0 0 (u y) [] []
  obtain ⟨t3, ht3, h3'⟩ := ylp_loop y (none, false) x 0 (u x) []
  have h3 : run t3 (cfg (some .ylp) (none, false) (u x) (u y) [] (u x) [] []) =
      cfg (some .par) (none, false) (u x) [] [] (u (x / 2 ^ y)) [] (u (y + 0)) := h3'
  have h4 : run (x / 2 ^ y + 1) (cfg (some .par) (none, false) (u x) [] [] (u (x / 2 ^ y)) []
      (u (y + 0))) =
      cfg (some .ry) (none, Nat.bodd (x / 2 ^ y)) (u x) [] [Nat.bodd (x / 2 ^ y)] [] []
        (u (y + 0)) := by
    simpa using par_loop (x / 2 ^ y) (none, false) (u x) [] [] [] (u (y + 0))
  have h5 : run (y + 1) (cfg (some .ry) (none, Nat.bodd (x / 2 ^ y)) (u x) [] [Nat.bodd (x / 2 ^ y)]
      [] [] (u (y + 0))) =
      cfg none (none, Nat.bodd (x / 2 ^ y)) (u x) (u y) [Nat.bodd (x / 2 ^ y)] [] [] [] := by
    simpa [u] using ry_loop y (none, Nat.bodd (x / 2 ^ y)) 0 (u x) [Nat.bodd (x / 2 ^ y)] [] []
  refine ⟨(x + 1) + (x + 1) + t3 + (x / 2 ^ y + 1) + (y + 1), ?_,
    (none, Nat.bodd (x / 2 ^ y)), ?_⟩
  · have : x / 2 ^ y ≤ x := Nat.div_le_self _ _
    unfold entryTime; omega
  · rw [run_add (run_add (run_add (run_add h1 _) _) _) _, h2, h3, h4, h5, bodd_div_eq_testBit]

end SeedT45.BitEntry

#print axioms SeedT45.BitEntry.entry_run
