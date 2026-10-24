import Paper2.CountedLoop

/-! Unit 3, segment (1), outer-token equality: generic small programs on an
arbitrary bank (cells are parameters), each with an exact whole-bank run.

* `clr c`: clear one cell (every popped bit a charged step);
* `inc c`: push one mark (unary increment);
* `cmp x t acc`: lockstep compare-and-clear of two unary cells, pushing the
  answer bit `decide (g = h)` on `acc` (the pattern of the checked
  `ScanSelect.cmp_run`, re-proved here for generic cells);
* `fold acc eq`: pop the whole bit list of `acc`, pushing its conjunction
  (with the initial control bit) on `eq`. -/

namespace Paper2.OTOps

noncomputable section

open Turing Turing.TM2.Stmt
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding

variable {J : Type*} [DecidableEq J]

def u (n : ℕ) : List Bool := List.replicate n true

theorem u_succ (k : ℕ) : u (k + 1) = true :: u k := rfl

theorem iter_trans {α : Type*} {f : α → α} {a b c : α} {m n : ℕ}
    (h1 : f^[m] a = b) (h2 : f^[n] b = c) : f^[n + m] a = c := by
  rw [Function.iterate_add_apply, h1, h2]

/-! ### Clear -/

def clr (c : J) : Unit → TM2.Stmt (fun _ : J => Bool) Unit (Option Bool) :=
  fun _ => pop c (fun _ b => b) (branch Option.isSome (goto (fun _ => ())) halt)

theorem clr_run (c : J) : ∀ (xs : List Bool) (S : J → List Bool) (v : Option Bool),
    S c = xs →
    ((advance (clr c))^[xs.length + 1]) (⟨some (), v, S⟩ :
        TM2.Cfg (fun _ : J => Bool) Unit (Option Bool)) =
      ⟨none, none, Function.update S c []⟩
  | [], S, v, hS => by
      have hS' : Function.update S c [] = S := by rw [← hS]; exact Function.update_eq_self _ _
      simp [BitMachineEncoding.advance, TM2.step, TM2.stepAux, clr, hS, hS']
  | b :: xs, S, v, hS => by
      rw [show (b :: xs).length + 1 = (xs.length + 1) + 1 by simp, Function.iterate_add_apply]
      have e : ((advance (clr c))^[1]) (⟨some (), v, S⟩ :
          TM2.Cfg (fun _ : J => Bool) Unit (Option Bool)) =
          ⟨some (), some b, Function.update S c xs⟩ := by
        simp [BitMachineEncoding.advance, TM2.step, TM2.stepAux, clr, hS]
      rw [e, clr_run c xs (Function.update S c xs) (some b) (by simp)]
      simp

/-! ### Increment -/

def inc (c : J) : Unit → TM2.Stmt (fun _ : J => Bool) Unit (Option Bool) :=
  fun _ => push c (fun _ => true) halt

theorem inc_run (c : J) (S : J → List Bool) (v : Option Bool) :
    ((advance (inc c))^[1]) (⟨some (), v, S⟩ :
        TM2.Cfg (fun _ : J => Bool) Unit (Option Bool)) =
      ⟨none, v, Function.update S c (true :: S c)⟩ := by
  rw [Function.iterate_one]
  simp [BitMachineEncoding.advance, TM2.step, TM2.stepAux, inc]

/-! ### Compare and clear -/

inductive CL where
  | cmp | clrX | clrT
  deriving DecidableEq

abbrev CCtl := Option Bool × Option Bool

def cmp (x t acc : J) : CL → TM2.Stmt (fun _ : J => Bool) CL CCtl
  | .cmp => pop x (fun v b => (b, v.2)) (pop t (fun v b => (v.1, b))
      (branch (fun v => v.1.isSome && v.2.isSome) (goto (fun _ => .cmp))
        (branch (fun v => v.1.isNone && v.2.isNone) (push acc (fun _ => true) halt)
          (goto (fun _ => .clrX)))))
  | .clrX => pop x (fun v b => (b, v.2))
      (branch (fun v => v.1.isSome) (goto (fun _ => .clrX)) (goto (fun _ => .clrT)))
  | .clrT => pop t (fun v b => (v.1, b))
      (branch (fun v => v.2.isSome) (goto (fun _ => .clrT)) (push acc (fun _ => false) halt))

/-- Exit bank: both operands cleared, the answer bit pushed on `acc`. -/
def F (x t acc : J) (S : J → List Bool) (b : Bool) : J → List Bool :=
  Function.update (Function.update (Function.update S x []) t []) acc (b :: S acc)

section Cmp

variable (x t acc : J) (hxt : x ≠ t) (hxa : x ≠ acc) (hta : t ≠ acc)
include hxt hxa hta

theorem step_clrX_cons (S : J → List Bool) (v : CCtl) (xs : List Bool) (h : S x = true :: xs) :
    advance (cmp x t acc) (⟨some .clrX, v, S⟩ : TM2.Cfg (fun _ : J => Bool) CL CCtl) =
      ⟨some .clrX, (some true, v.2), Function.update S x xs⟩ := by
  simp [advance, TM2.step, TM2.stepAux, cmp, h]

theorem step_clrX_nil (S : J → List Bool) (v : CCtl) (h : S x = []) :
    advance (cmp x t acc) (⟨some .clrX, v, S⟩ : TM2.Cfg (fun _ : J => Bool) CL CCtl) =
      ⟨some .clrT, (none, v.2), Function.update S x []⟩ := by
  simp [advance, TM2.step, TM2.stepAux, cmp, h]

theorem step_clrT_cons (S : J → List Bool) (v : CCtl) (xs : List Bool) (h : S t = true :: xs) :
    advance (cmp x t acc) (⟨some .clrT, v, S⟩ : TM2.Cfg (fun _ : J => Bool) CL CCtl) =
      ⟨some .clrT, (v.1, some true), Function.update S t xs⟩ := by
  simp [advance, TM2.step, TM2.stepAux, cmp, h]

theorem step_clrT_nil (S : J → List Bool) (v : CCtl) (h : S t = []) :
    advance (cmp x t acc) (⟨some .clrT, v, S⟩ : TM2.Cfg (fun _ : J => Bool) CL CCtl) =
      ⟨none, (v.1, none), Function.update (Function.update S t []) acc
        (false :: S acc)⟩ := by
  simp [advance, TM2.step, TM2.stepAux, cmp, h, Function.update_apply, Ne.symm hta]

theorem clrX_run : ∀ (j : ℕ) (S : J → List Bool) (v : CCtl), S x = u j →
    (advance (cmp x t acc))^[j + 1] (⟨some .clrX, v, S⟩ : TM2.Cfg (fun _ : J => Bool) CL CCtl) =
      ⟨some .clrT, (none, v.2), Function.update S x []⟩
  | 0, S, v, h => by
      rw [Function.iterate_one]
      exact step_clrX_nil x t acc hxt hxa hta S v h
  | j + 1, S, v, h => by
      rw [Function.iterate_succ_apply, step_clrX_cons x t acc hxt hxa hta S v (u j) h,
        clrX_run j _ _ (by simp [u])]
      simp

theorem clrT_run : ∀ (j : ℕ) (S : J → List Bool) (v : CCtl), S t = u j →
    (advance (cmp x t acc))^[j + 1] (⟨some .clrT, v, S⟩ : TM2.Cfg (fun _ : J => Bool) CL CCtl) =
      ⟨none, (v.1, none), Function.update (Function.update S t []) acc (false :: S acc)⟩
  | 0, S, v, h => by
      rw [Function.iterate_one]
      exact step_clrT_nil x t acc hxt hxa hta S v h
  | j + 1, S, v, h => by
      rw [Function.iterate_succ_apply, step_clrT_cons x t acc hxt hxa hta S v (u j) h,
        clrT_run j _ _ (by simp [u])]
      simp [Function.update_apply, Ne.symm hta]

theorem cmp_run : ∀ (g h : ℕ) (S : J → List Bool) (v : CCtl), S x = u g → S t = u h →
    ∃ n ≤ g + h + 3, ∃ c,
      (advance (cmp x t acc))^[n] (⟨some .cmp, v, S⟩ : TM2.Cfg (fun _ : J => Bool) CL CCtl) =
        ⟨none, c, F x t acc S (decide (g = h))⟩
  | 0, 0, S, v, hg, hi => by
      refine ⟨1, by omega, (none, none), ?_⟩
      rw [Function.iterate_one]
      have hg' : S x = [] := hg
      have hi' : S t = [] := hi
      have e1 : Function.update S x [] = S := by rw [← hg']; exact Function.update_eq_self _ _
      have e2 : Function.update S t [] = S := by rw [← hi']; exact Function.update_eq_self _ _
      simp [advance, TM2.step, TM2.stepAux, cmp, F, hg', hi', Function.update_apply,
        Ne.symm hxt, e1, e2]
      funext y
      simp only [Function.update_apply]
      by_cases h1 : y = acc <;> by_cases h2 : y = t <;> by_cases h3 : y = x <;> simp_all
  | 0, j + 1, S, v, hg, hi => by
      have hg' : S x = [] := hg
      have hs : advance (cmp x t acc) (⟨some .cmp, v, S⟩ : TM2.Cfg (fun _ : J => Bool) CL CCtl) =
          ⟨some .clrX, (none, some true),
            Function.update (Function.update S x []) t (u j)⟩ := by
        rw [u_succ] at hi
        simp [advance, TM2.step, TM2.stepAux, cmp, hg', hi, Function.update_apply, Ne.symm hxt]
      have h1 := clrX_run x t acc hxt hxa hta 0
        (Function.update (Function.update S x []) t (u j)) (none, some true)
        (by simp [u, Function.update_apply, hxt])
      have h2 := clrT_run x t acc hxt hxa hta j
        (Function.update (Function.update (Function.update S x []) t (u j)) x [])
        ((none : Option Bool), (some true : Option Bool)) (by simp [u, Function.update_apply, Ne.symm hxt])
      refine ⟨(j + 1) + ((0 + 1) + 1), by omega, ((none : Option Bool), (none : Option Bool)), ?_⟩
      refine iter_trans (iter_trans (by rw [Function.iterate_one]; exact hs) h1) (h2.trans ?_)
      congr 1
      funext y
      simp only [F, Function.update_apply]
      by_cases h1 : y = acc <;> by_cases h2 : y = t <;> by_cases h3 : y = x <;> simp_all
  | g + 1, 0, S, v, hg, hi => by
      have hi' : S t = [] := hi
      have hs : advance (cmp x t acc) (⟨some .cmp, v, S⟩ : TM2.Cfg (fun _ : J => Bool) CL CCtl) =
          ⟨some .clrX, (some true, none),
            Function.update (Function.update S x (u g)) t []⟩ := by
        rw [u_succ] at hg
        simp [advance, TM2.step, TM2.stepAux, cmp, hg, hi', Function.update_apply, Ne.symm hxt]
      have h1 := clrX_run x t acc hxt hxa hta g
        (Function.update (Function.update S x (u g)) t []) (some true, none)
        (by simp [u, Function.update_apply, hxt])
      have h2 := clrT_run x t acc hxt hxa hta 0
        (Function.update (Function.update (Function.update S x (u g)) t []) x [])
        ((none : Option Bool), (none : Option Bool)) (by simp [u, Function.update_apply, Ne.symm hxt])
      refine ⟨(0 + 1) + ((g + 1) + 1), by omega, ((none : Option Bool), (none : Option Bool)), ?_⟩
      refine iter_trans (iter_trans (by rw [Function.iterate_one]; exact hs) h1) (h2.trans ?_)
      congr 1
      funext y
      simp only [F, Function.update_apply]
      by_cases h1 : y = acc <;> by_cases h2 : y = t <;> by_cases h3 : y = x <;> simp_all
  | g + 1, j + 1, S, v, hg, hi => by
      have hs : advance (cmp x t acc) (⟨some .cmp, v, S⟩ : TM2.Cfg (fun _ : J => Bool) CL CCtl) =
          ⟨some .cmp, (some true, some true),
            Function.update (Function.update S x (u g)) t (u j)⟩ := by
        rw [u_succ] at hg hi
        simp [advance, TM2.step, TM2.stepAux, cmp, hg, hi, Function.update_apply, Ne.symm hxt]
      obtain ⟨n, hn, c, hr⟩ := cmp_run g j (Function.update (Function.update S x (u g)) t (u j))
        (some true, some true) (by simp [u, Function.update_apply, hxt]) (by simp [u])
      refine ⟨n + 1, by omega, c, ?_⟩
      refine iter_trans (by rw [Function.iterate_one]; exact hs) (hr.trans ?_)
      congr 1
      funext y
      simp only [F, Function.update_apply]
      by_cases h1 : y = acc <;> by_cases h2 : y = t <;> by_cases h3 : y = x <;> simp_all

end Cmp

/-! ### Fold (conjunction of a bit list) -/

abbrev FCtl := Bool × Option Bool

def fold (acc eq : J) : Unit → TM2.Stmt (fun _ : J => Bool) Unit FCtl :=
  fun _ => pop acc (fun v b => (v.1, b))
    (branch (fun v => v.2.isSome) (load (fun v => (v.1 && v.2.getD true, none))
      (goto (fun _ => ()))) (push eq (fun v => v.1) halt))

theorem fold_run (acc eq : J) (hne : acc ≠ eq) : ∀ (L : List Bool) (S : J → List Bool) (b : Bool)
    (o : Option Bool), S acc = L →
    ((advance (fold acc eq))^[L.length + 1]) (⟨some (), (b, o), S⟩ :
        TM2.Cfg (fun _ : J => Bool) Unit FCtl) =
      ⟨none, (b && L.all id, none),
        Function.update (Function.update S acc []) eq ((b && L.all id) :: S eq)⟩
  | [], S, b, o, hS => by
      rw [show ([] : List Bool).length + 1 = 1 from rfl, Function.iterate_one]
      have hS' : Function.update S acc [] = S := by rw [← hS]; exact Function.update_eq_self _ _
      simp [BitMachineEncoding.advance, TM2.step, TM2.stepAux, fold, hS, hS']
  | c :: L, S, b, o, hS => by
      rw [show (c :: L).length + 1 = (L.length + 1) + 1 by simp, Function.iterate_add_apply]
      have e : ((advance (fold acc eq))^[1]) (⟨some (), (b, o), S⟩ :
          TM2.Cfg (fun _ : J => Bool) Unit FCtl) =
          ⟨some (), (b && c, none), Function.update S acc L⟩ := by
        rw [Function.iterate_one]
        simp [BitMachineEncoding.advance, TM2.step, TM2.stepAux, fold, hS]
      rw [e, fold_run acc eq hne L (Function.update S acc L) (b && c) none (by simp)]
      have hb : (b && c && L.all id) = (b && (c :: L).all id) := by
        simp [List.all_cons, Bool.and_assoc]
      rw [hb, Function.update_idem, Function.update_of_ne (Ne.symm hne)]

#print axioms clr_run
#print axioms inc_run
#print axioms cmp_run
#print axioms fold_run

end

end Paper2.OTOps
