import EthInapproximability.CurrentPaper.BitMachineRawSequence
import EthInapproximability.CurrentPaper.BitMachineIteration
import EthInapproximability.CurrentPaper.BitMachineStackRun
import Paper2.CountedLoop
import EthInapproximability.CurrentPaper.EncodedCommunication

/-!
# WP-U18a (ii), machine half, part 1: generic literal phases on one physical bank

Lane `owner:a-median-1` (private, 27 September 2026). Paper A, lock v12, I:117-125.

Small fixed TM2 programs over an arbitrary finite stack bank `K`, each with an EXACT run lemma
(exact step count, exact final bank as `Function.update`s of the start bank):
`mv` (move, reversing), `cp2` (move to two targets), `takeS` (unary-counted transfer),
`fieldScan` (move one `field`-encoded word), `countMove` (move while counting blocks of `n+1`),
`pushN` (one transition pushing `m` marks), `tally`, `final`, and a bundled phase algebra
(`Phase`, `Phase.seq` via the production `BitMachineRawSequence.program`, `Phase.loop` via the
admitted `Paper2.CountedLoop.loop`). The clean call of an arbitrary machine is the production
`BitMachineIteration.program` with fuel `[true]`, embedded by `BitMachineStackRun`.
Every transition is charged; nothing is inserted into a bank.
-/

set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

namespace Paper2.MedianOwner.Phases

open Turing Turing.TM2.Stmt
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding

variable {K : Type} [DecidableEq K]

abbrev Stmt (K L V : Type) := TM2.Stmt (fun _ : K => Bool) L V
abbrev Cfg (K L V : Type) := TM2.Cfg (fun _ : K => Bool) L V

/-! ## Move -/

/-- Move every cell of `src` onto `dst` (reversing), then halt. -/
def mv (src dst : K) : Unit → Stmt K Unit (Option Bool)
  | _ => pop src (fun _ b => b) (branch (fun v => v.isSome)
      (push dst (fun v => v.getD false) (goto (fun _ => ()))) halt)

theorem mv_run (src dst : K) (h : src ≠ dst) : ∀ (xs : List Bool) (S : K → List Bool)
    (v : Option Bool), S src = xs →
    ((advance (mv src dst))^[xs.length + 1]) (⟨some (), v, S⟩ : Cfg K Unit (Option Bool)) =
      ⟨none, none, Function.update (Function.update S src []) dst (xs.reverse ++ S dst)⟩
  | [], S, v, hS => by
    simp only [List.length_nil, zero_add, Function.iterate_one]
    simp [advance, TM2.step, TM2.stepAux, mv, hS, Function.update_apply, Ne.symm h]
  | b :: xs, S, v, hS => by
    rw [List.length_cons, Function.iterate_succ_apply]
    have hstep : advance (mv src dst) (⟨some (), v, S⟩ : Cfg K Unit (Option Bool)) =
        ⟨some (), some b, Function.update (Function.update S src xs) dst (b :: S dst)⟩ := by
      simp [advance, TM2.step, TM2.stepAux, mv, hS, Function.update_apply, Ne.symm h]
    rw [hstep, mv_run src dst h xs _ _ (by simp [Function.update_apply, h])]
    congr 1
    funext k
    by_cases hk : k = dst
    · subst hk; simp [Function.update_apply, Ne.symm h]
    · by_cases hk' : k = src
      · subst hk'; simp [Function.update_apply, hk]
      · simp [Function.update_apply, hk, hk']

theorem rep_cons (n : ℕ) (l : List Bool) :
    List.replicate n true ++ true :: l = true :: (List.replicate n true ++ l) := by
  rw [← List.singleton_append, ← List.append_assoc, ← List.replicate_succ', List.replicate_succ,
    List.cons_append]

/-! ## Move to two targets -/

/-- Move every cell of `src` onto both `d1` and `d2` (each reversed), then halt. -/
def cp2 (src d1 d2 : K) : Unit → Stmt K Unit (Option Bool)
  | _ => pop src (fun _ b => b) (branch (fun v => v.isSome)
      (push d1 (fun v => v.getD false) (push d2 (fun v => v.getD false)
        (goto (fun _ => ())))) halt)

theorem cp2_run (src d1 d2 : K) (h1 : src ≠ d1) (h2 : src ≠ d2) (h12 : d1 ≠ d2) :
    ∀ (xs : List Bool) (S : K → List Bool) (v : Option Bool), S src = xs →
    ((advance (cp2 src d1 d2))^[xs.length + 1]) (⟨some (), v, S⟩ : Cfg K Unit (Option Bool)) =
      ⟨none, none, Function.update (Function.update (Function.update S src []) d1
        (xs.reverse ++ S d1)) d2 (xs.reverse ++ S d2)⟩
  | [], S, v, hS => by
    simp only [List.length_nil, zero_add, Function.iterate_one]
    simp [advance, TM2.step, TM2.stepAux, cp2, hS]
    funext k
    simp only [Function.update_apply]
    split_ifs <;> simp_all
  | b :: xs, S, v, hS => by
    rw [List.length_cons, Function.iterate_succ_apply]
    have hstep : advance (cp2 src d1 d2) (⟨some (), v, S⟩ : Cfg K Unit (Option Bool)) =
        ⟨some (), some b, Function.update (Function.update (Function.update S src xs) d1
          (b :: S d1)) d2 (b :: S d2)⟩ := by
      simp [advance, TM2.step, TM2.stepAux, cp2, hS, Function.update_apply, Ne.symm h1,
        Ne.symm h2, Ne.symm h12]
    rw [hstep, cp2_run src d1 d2 h1 h2 h12 xs _ _ (by simp [Function.update_apply, h1, h2])]
    congr 1
    funext k
    simp only [Function.update_apply]
    split_ifs <;> simp_all

/-! ## Unary-counted transfer -/

/-- For every mark popped from `sc`: push a mark onto `sc2`, pop one cell of `tr` and push it
onto `dst`. -/
def takeS (sc sc2 tr dst : K) : Unit → Stmt K Unit (Option Bool)
  | _ => pop sc (fun _ b => b) (branch (fun v => v.isSome)
      (push sc2 (fun _ => true) (pop tr (fun _ b => b) (push dst (fun v => v.getD false)
        (goto (fun _ => ()))))) halt)

theorem takeS_run (sc sc2 tr dst : K) (h1 : sc ≠ sc2) (h2 : sc ≠ tr) (h3 : sc ≠ dst)
    (h4 : sc2 ≠ tr) (h5 : sc2 ≠ dst) (h6 : tr ≠ dst) (rest : List Bool) :
    ∀ (ys : List Bool) (S : K → List Bool) (v : Option Bool),
    S sc = List.replicate ys.length true → S tr = ys ++ rest →
    ((advance (takeS sc sc2 tr dst))^[ys.length + 1])
        (⟨some (), v, S⟩ : Cfg K Unit (Option Bool)) =
      ⟨none, none, Function.update (Function.update (Function.update (Function.update S sc [])
        sc2 (List.replicate ys.length true ++ S sc2)) tr rest) dst (ys.reverse ++ S dst)⟩
  | [], S, v, hS, hT => by
    simp only [List.length_nil, zero_add, Function.iterate_one, List.replicate_zero] at hS ⊢
    simp [advance, TM2.step, TM2.stepAux, takeS, hS, Function.update_apply]
    funext k
    simp only [Function.update_apply]
    split_ifs <;> simp_all
  | b :: ys, S, v, hS, hT => by
    rw [List.length_cons, Function.iterate_succ_apply]
    rw [List.length_cons, List.replicate_succ] at hS
    have hstep : advance (takeS sc sc2 tr dst) (⟨some (), v, S⟩ : Cfg K Unit (Option Bool)) =
        ⟨some (), some b, Function.update (Function.update (Function.update
          (Function.update S sc (List.replicate ys.length true)) sc2 (true :: S sc2))
          tr (ys ++ rest)) dst (b :: S dst)⟩ := by
      simp [advance, TM2.step, TM2.stepAux, takeS, hS, hT, Function.update_apply, Ne.symm h1,
        Ne.symm h2, Ne.symm h3, Ne.symm h4, Ne.symm h5, Ne.symm h6, h1, h2, h3, h4, h5, h6]
    rw [hstep, takeS_run sc sc2 tr dst h1 h2 h3 h4 h5 h6 rest ys _ _
      (by simp [Function.update_apply, h1, h2, h3]) (by simp [Function.update_apply, h4, h6, h2])]
    congr 1
    funext k
    simp only [Function.update_apply, List.length_cons, List.replicate_succ, List.reverse_cons,
      List.append_assoc, List.cons_append, List.nil_append, List.singleton_append]
    split_ifs <;> simp_all [rep_cons, List.replicate_succ]

/-! ## Moving one `field`-encoded word -/

open EthInapproximability.CurrentPaper.EncodedCommunication (field) in
/-- Move the leading `field`-encoded word of `src` onto `dst` (reversed); stop after its
terminator. -/
def fieldScan (src dst : K) : Unit → Stmt K Unit (Option Bool)
  | _ => pop src (fun _ b => b) (branch (fun v => v == some true)
      (push dst (fun _ => true) (pop src (fun _ b => b) (push dst (fun v => v.getD false)
        (goto (fun _ => ())))))
      (push dst (fun _ => false) halt))

open EthInapproximability.CurrentPaper.EncodedCommunication (field) in
theorem fieldScan_run (src dst : K) (h : src ≠ dst) (rest : List Bool) :
    ∀ (w : List Bool) (S : K → List Bool) (v : Option Bool), S src = field w ++ rest →
    ((advance (fieldScan src dst))^[w.length + 1])
        (⟨some (), v, S⟩ : Cfg K Unit (Option Bool)) =
      ⟨none, some false, Function.update (Function.update S src rest) dst
        ((field w).reverse ++ S dst)⟩
  | [], S, v, hS => by
    simp only [List.length_nil, zero_add, Function.iterate_one]
    simp [advance, TM2.step, TM2.stepAux, fieldScan, hS, field, Function.update_apply, Ne.symm h]
  | b :: w, S, v, hS => by
    rw [List.length_cons, Function.iterate_succ_apply]
    have hstep : advance (fieldScan src dst) (⟨some (), v, S⟩ : Cfg K Unit (Option Bool)) =
        ⟨some (), some b, Function.update (Function.update S src (field w ++ rest)) dst
          (b :: true :: S dst)⟩ := by
      simp [advance, TM2.step, TM2.stepAux, fieldScan, hS, field, Function.update_apply, h,
        Ne.symm h]
      funext k
      simp only [Function.update_apply]
      split_ifs <;> simp_all
    rw [hstep, fieldScan_run src dst h rest w _ _ (by simp [Function.update_apply, h])]
    congr 1
    funext k
    simp only [Function.update_apply]
    split_ifs <;> simp_all [field]

/-! ## Moving while counting blocks of `n+1` -/

/-- Move `src` onto `dst` (reversed) and push one mark onto `mark` after every `n+1` cells. -/
def countMove (n : ℕ) (src dst mark : K) : Unit → Stmt K Unit (Option Bool × Fin (n + 1))
  | _ => pop src (fun v b => (b, v.2)) (branch (fun v => v.1.isSome)
      (push dst (fun v => v.1.getD false) (branch (fun v => decide (v.2.val = n))
        (push mark (fun _ => true) (load (fun v => (v.1, 0)) (goto (fun _ => ()))))
        (load (fun v => (v.1, v.2 + 1)) (goto (fun _ => ()))))) halt)

theorem countMove_run (n : ℕ) (src dst mark : K) (h1 : src ≠ dst) (h2 : src ≠ mark)
    (h3 : dst ≠ mark) :
    ∀ (xs : List Bool) (S : K → List Bool) (b : Option Bool) (j : Fin (n + 1)), S src = xs →
    ∃ c, ((advance (countMove n src dst mark))^[xs.length + 1])
        (⟨some (), (b, j), S⟩ : Cfg K Unit (Option Bool × Fin (n + 1))) =
      ⟨none, c, Function.update (Function.update (Function.update S src []) dst
        (xs.reverse ++ S dst)) mark
        (List.replicate ((j.val + xs.length) / (n + 1)) true ++ S mark)⟩
  | [], S, b, j, hS => by
    refine ⟨(none, j), ?_⟩
    simp only [List.length_nil, zero_add, Function.iterate_one, add_zero]
    have hj : j.val / (n + 1) = 0 := Nat.div_eq_of_lt j.isLt
    simp [advance, TM2.step, TM2.stepAux, countMove, hS, hj]
    funext k
    simp only [Function.update_apply]
    split_ifs <;> simp_all
  | x :: xs, S, b, j, hS => by
    rw [List.length_cons, Function.iterate_succ_apply]
    by_cases hj : j.val = n
    · have hstep : advance (countMove n src dst mark)
          (⟨some (), (b, j), S⟩ : Cfg K Unit (Option Bool × Fin (n + 1))) =
          ⟨some (), (some x, 0), Function.update (Function.update (Function.update S src xs)
            dst (x :: S dst)) mark (true :: S mark)⟩ := by
        simp [advance, TM2.step, TM2.stepAux, countMove, hS, hj, Function.update_apply,
          Ne.symm h1, Ne.symm h2, Ne.symm h3, h3]
      obtain ⟨c, hc⟩ := countMove_run n src dst mark h1 h2 h3 xs
        (Function.update (Function.update (Function.update S src xs)
            dst (x :: S dst)) mark (true :: S mark)) (some x) 0
        (by simp [Function.update_apply, h1, h2])
      refine ⟨c, ?_⟩
      rw [hstep, hc]
      congr 1
      have hdiv : (j.val + (xs.length + 1)) / (n + 1) = xs.length / (n + 1) + 1 := by
        rw [hj, show n + (xs.length + 1) = xs.length + (n + 1) by omega, Nat.add_div_right _
          (by omega)]
      funext k
      simp only [Function.update_apply, hdiv, Fin.val_zero, zero_add]
      split_ifs <;> simp_all [rep_cons, List.replicate_succ]
    · have hlt : j.val < n := lt_of_le_of_ne (Nat.lt_succ_iff.mp j.isLt) hj
      have hstep : advance (countMove n src dst mark)
          (⟨some (), (b, j), S⟩ : Cfg K Unit (Option Bool × Fin (n + 1))) =
          ⟨some (), (some x, j + 1), Function.update (Function.update S src xs)
            dst (x :: S dst)⟩ := by
        simp [advance, TM2.step, TM2.stepAux, countMove, hS, hj, Function.update_apply,
          Ne.symm h1]
      obtain ⟨c, hc⟩ := countMove_run n src dst mark h1 h2 h3 xs
        (Function.update (Function.update S src xs) dst (x :: S dst)) (some x) (j + 1)
        (by simp [Function.update_apply, h1])
      refine ⟨c, ?_⟩
      rw [hstep, hc]
      congr 1
      have hv : (j + 1 : Fin (n + 1)).val = j.val + 1 := by
        rw [Fin.val_add_one_of_lt]
        exact Fin.lt_def.mpr (by simp; omega)
      have hdiv : (j.val + (xs.length + 1)) / (n + 1) = ((j + 1 : Fin (n + 1)).val +
          xs.length) / (n + 1) := by rw [hv]; congr 1; omega
      funext k
      simp only [Function.update_apply, hdiv]
      split_ifs <;> simp_all

/-! ## One transition pushing `m` marks -/

/-- `m` pushes of `true` onto `k`, then halt: ONE transition. -/
def pushes {V : Type} (k : K) : ℕ → Stmt K Unit V
  | 0 => halt
  | m + 1 => push k (fun _ => true) (pushes k m)

theorem pushes_stepAux {V : Type} (k : K) : ∀ (m : ℕ) (v : V) (S : K → List Bool),
    TM2.stepAux (pushes k m) v S = ⟨none, v, Function.update S k (List.replicate m true ++ S k)⟩
  | 0, v, S => by simp [pushes, TM2.stepAux]
  | m + 1, v, S => by
    simp only [pushes, TM2.stepAux]
    rw [pushes_stepAux k m]
    simp [List.replicate_succ']

def pushN (k : K) (m : ℕ) : Unit → Stmt K Unit (Option Bool) := fun _ => pushes k m

theorem pushN_run (k : K) (m : ℕ) (S : K → List Bool) (v : Option Bool) :
    ((advance (pushN k m))^[1]) (⟨some (), v, S⟩ : Cfg K Unit (Option Bool)) =
      ⟨none, v, Function.update S k (List.replicate m true ++ S k)⟩ := by
  simp only [Function.iterate_one, advance, TM2.step, Option.getD_some, pushN]
  exact pushes_stepAux k m v S

/-! ## Tally and final majority -/

/-- Pop one cell of `src`; if it is `true`, push a mark onto `cnt`. -/
def tally (src cnt : K) : Unit → Stmt K Unit (Option Bool)
  | _ => pop src (fun _ b => b) (branch (fun v => v == some true)
      (push cnt (fun _ => true) halt) halt)

theorem tally_run (src cnt : K) (h : src ≠ cnt) (b : Bool) (S : K → List Bool) (v : Option Bool)
    (hS : S src = [b]) :
    ((advance (tally src cnt))^[1]) (⟨some (), v, S⟩ : Cfg K Unit (Option Bool)) =
      ⟨none, some b, Function.update (Function.update S src [])
        cnt (List.replicate (if b then 1 else 0) true ++ S cnt)⟩ := by
  cases b <;>
  simp [Function.iterate_one, advance, TM2.step, TM2.stepAux, tally, hS, Function.update_apply,
    Ne.symm h]

/-- Count the marks of `cnt` (saturating at `n+1`) and print `decide (n+1 < 2*count)` on
`outp`. -/
def final (n : ℕ) (cnt outp : K) : Unit → Stmt K Unit (Option Bool × Fin (n + 2))
  | _ => pop cnt (fun v b => (b, v.2)) (branch (fun v => v.1.isSome)
      (load (fun v => (v.1, if v.2.val < n + 1 then v.2 + 1 else v.2)) (goto (fun _ => ())))
      (push outp (fun v => decide (n + 1 < 2 * v.2.val)) halt))

theorem final_run (n : ℕ) (cnt outp : K) (h : cnt ≠ outp) :
    ∀ (c : ℕ) (S : K → List Bool) (b : Option Bool) (j : Fin (n + 2)),
    S cnt = List.replicate c true → j.val + c ≤ n + 1 →
    ∃ v, ((advance (final n cnt outp))^[c + 1])
        (⟨some (), (b, j), S⟩ : Cfg K Unit (Option Bool × Fin (n + 2))) =
      ⟨none, v, Function.update (Function.update S cnt [])
        outp (decide (n + 1 < 2 * (j.val + c)) :: S outp)⟩
  | 0, S, b, j, hS, _ => by
    refine ⟨(none, j), ?_⟩
    simp only [List.replicate_zero] at hS
    simp [Function.iterate_one, advance, TM2.step, TM2.stepAux, final, hS,
      Function.update_apply, Ne.symm h]
  | c + 1, S, b, j, hS, hc => by
    rw [Function.iterate_succ_apply]
    have hlt : j.val < n + 1 := by omega
    have hle : j.val ≤ n := by omega
    have hstep : advance (final n cnt outp)
        (⟨some (), (b, j), S⟩ : Cfg K Unit (Option Bool × Fin (n + 2))) =
        ⟨some (), (some true, j + 1), Function.update S cnt (List.replicate c true)⟩ := by
      simp [advance, TM2.step, TM2.stepAux, final, hS, hlt, hle, List.replicate_succ]
    have hv : (j + 1 : Fin (n + 2)).val = j.val + 1 := by
      rw [Fin.val_add_one_of_lt]
      exact Fin.lt_def.mpr (by simp; omega)
    obtain ⟨v, hv'⟩ := final_run n cnt outp h c (Function.update S cnt (List.replicate c true))
      (some true) (j + 1) (by simp) (by rw [hv]; omega)
    refine ⟨v, ?_⟩
    rw [hstep, hv', hv]
    have he : j.val + 1 + c = j.val + (c + 1) := by omega
    rw [he]
    congr 1
    funext k
    simp only [Function.update_apply]
    split_ifs <;> simp_all

end Paper2.MedianOwner.Phases
