import Paper2.NPLoops
import Paper2.A4PolyIn
import EthInapproximability.CurrentPaper.BitMachineStackEmbedding
import EthInapproximability.CurrentPaper.ComplexityReductionClosure

/-!
# WP-NP (lane `owner:a-np-1`, private, 26 September 2026): one fixed machine for
# `code ↦ pair (f x) (take (c·(|f x|+1)^d) t)` on EVERY word

For every `BitMachine.Machine` `M` and fixed `c d : ℕ` there is ONE fixed finite machine
`machine M c d`. On an arbitrary input word `code` (no well-formedness is assumed) it runs:

1. `parse`: the admitted `parseStmt` consumes a (possibly truncated) self-delimiting field
   from `main`; payload `x = (parseAll code).1` goes to `temp` (reversed) and `main` keeps
   `t = (parseAll code).2`. On `code = pair x t` this is exactly `(x, t)` (`parseAll_pair`).
2. `load`: `temp` is moved onto `M`'s input stack: literally `M.init x`.
3. `M` runs in place (admitted `BitMachineStackEmbedding`), halting into phase 4.
4. `move`: `M`'s output `y` goes to `temp` (reversed).
5. `initU`: push `c` cells on `u` and `d` cells on the level stack `lv` (one statement).
6. `mulCheck/mulOuter/mulInner/mulExtra/mulBack/mulCollect`: `d` times, `u := u·(|y|+1)` in
   unary (each cell of `u` walks once through `temp`, which is restored).
   Afterwards `u` holds exactly `B = c·(|y|+1)^d` cells.
7. `cut`: move `take B t` from `main` to `out` (one cell of `u` per bit).
8. `clear`: pop the rest `drop B t` of `main` (onto the scratch stack `y2`).
9. `restore`: move `out` back to `main` (now `main = take B t`).
10. `emit0/emit`: `main := field y ++ take B t = pair y (take B t)`. `done` halts.

Every bit is produced by a literal transition; no input is inserted.
**No ledger row is closed.**
-/

namespace NPOwner1.Trunc

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding
open Paper2.Unit4Shell.Loops
open NPOwner1

inductive NL
  | parse | load | move | initU | mulCheck | mulOuter | mulInner | mulExtra | mulBack
  | mulCollect | cut | clear | restore | emit0 | emit | done
  deriving DecidableEq, Fintype

variable (M : BitMachine.Machine) (c d : ℕ)

abbrev Stack := Fin 7 ⊕ Fin M.stackCount
abbrev Label := NL ⊕ Fin M.labelCount
abbrev Control := Option Bool × Fin M.controlCount

def mainS : Stack M := .inl 0
def tempS : Stack M := .inl 1
def y2S : Stack M := .inl 2
def uS : Stack M := .inl 3
def u2S : Stack M := .inl 4
def outS : Stack M := .inl 5
def lvS : Stack M := .inl 6

def mStack : Fin M.stackCount ↪ Stack M := ⟨Sum.inr, Sum.inr_injective⟩

def embedC (v : Fin M.controlCount) : Control M := (none, v)

def program : Label M → TM2.Stmt (fun _ : Stack M => Bool) (Label M) (Control M)
  | .inl .parse => parseStmt (mainS M) (tempS M) (.inl .parse) (.inl .load)
  | .inl .load => moveStmt (tempS M) (.inr M.input) (.inl .load) (.inr M.start)
  | .inl .move => moveStmt (.inr M.output) (tempS M) (.inl .move) (.inl .initU)
  | .inl .initU => pushTrues (uS M) c (pushTrues (lvS M) d (.goto fun _ => .inl .mulCheck))
  | .inl .mulCheck => popBranchStmt (lvS M) (.inl .mulOuter) (.inl .cut)
  | .inl .mulOuter => popBranchStmt (uS M) (.inl .mulInner) (.inl .mulCollect)
  | .inl .mulInner => moveCountStmt (tempS M) (y2S M) (u2S M) (.inl .mulInner) (.inl .mulExtra)
  | .inl .mulExtra => pushTrues (u2S M) 1 (.goto fun _ => .inl .mulBack)
  | .inl .mulBack => moveStmt (y2S M) (tempS M) (.inl .mulBack) (.inl .mulOuter)
  | .inl .mulCollect => moveStmt (u2S M) (uS M) (.inl .mulCollect) (.inl .mulCheck)
  | .inl .cut => cutStmt (uS M) (mainS M) (outS M) (.inl .cut) (.inl .clear)
  | .inl .clear => moveStmt (mainS M) (y2S M) (.inl .clear) (.inl .restore)
  | .inl .restore => moveStmt (outS M) (mainS M) (.inl .restore) (.inl .emit0)
  | .inl .emit0 => pushFalseStmt (mainS M) (.inl .emit)
  | .inl .emit => emitStmt (tempS M) (mainS M) (.inl .emit) (.inl .done)
  | .inl .done => .halt
  | .inr l => BitMachineStackEmbedding.stmt (mStack M) Sum.inr (embedC M) Prod.snd
      (some (.inl .move)) (M.program l)

/-- THE fixed machine for `M`, `c`, `d`. -/
noncomputable def machine : BitMachine.Machine :=
  ofFinite (mainS M) (mainS M) (.inl .parse) ((none, M.initial) : Control M) (program M c d)

theorem machine_program_eq (l : Fin M.labelCount) :
    program M c d (.inr l) = BitMachineStackEmbedding.stmt (mStack M) Sum.inr (embedC M)
      Prod.snd (some (.inl .move)) (M.program l) := rfl

/-- The literal output word on every input word. -/
def result (f : List Bool → List Bool) (code : List Bool) : List Bool :=
  EncodedComplexity.pair (f (parseAll code).1)
    ((parseAll code).2.take (c * ((f (parseAll code).1).length + 1) ^ d))

theorem result_pair (f : List Bool → List Bool) (x t : List Bool) :
    result c d f (EncodedComplexity.pair x t) =
      EncodedComplexity.pair (f x) (t.take (c * ((f x).length + 1) ^ d)) := by
  simp [result, parseAll_pair]

/-! ## The stack record -/

/-- All stacks: the seven own stacks and the stacks `R` of `M`. -/
def St (main temp y2 u u2 out lv : List Bool) (R : Fin M.stackCount → List Bool) :
    Stack M → List Bool
  | .inl i => ![main, temp, y2, u, u2, out, lv] i
  | .inr j => R j

section St

variable {M}
variable (main temp y2 u u2 out lv x : List Bool) (R : Fin M.stackCount → List Bool)

@[simp] theorem st_main : St M main temp y2 u u2 out lv R (mainS M) = main := rfl
@[simp] theorem st_temp : St M main temp y2 u u2 out lv R (tempS M) = temp := rfl
@[simp] theorem st_y2 : St M main temp y2 u u2 out lv R (y2S M) = y2 := rfl
@[simp] theorem st_u : St M main temp y2 u u2 out lv R (uS M) = u := rfl
@[simp] theorem st_u2 : St M main temp y2 u u2 out lv R (u2S M) = u2 := rfl
@[simp] theorem st_out : St M main temp y2 u u2 out lv R (outS M) = out := rfl
@[simp] theorem st_lv : St M main temp y2 u u2 out lv R (lvS M) = lv := rfl
@[simp] theorem st_R (j : Fin M.stackCount) : St M main temp y2 u u2 out lv R (.inr j) = R j :=
  rfl

@[simp] theorem up_main : Function.update (St M main temp y2 u u2 out lv R) (mainS M) x =
    St M x temp y2 u u2 out lv R := by
  funext k; rcases k with i | j
  · fin_cases i <;> rfl
  · rfl
@[simp] theorem up_temp : Function.update (St M main temp y2 u u2 out lv R) (tempS M) x =
    St M main x y2 u u2 out lv R := by
  funext k; rcases k with i | j
  · fin_cases i <;> rfl
  · rfl
@[simp] theorem up_y2 : Function.update (St M main temp y2 u u2 out lv R) (y2S M) x =
    St M main temp x u u2 out lv R := by
  funext k; rcases k with i | j
  · fin_cases i <;> rfl
  · rfl
@[simp] theorem up_u : Function.update (St M main temp y2 u u2 out lv R) (uS M) x =
    St M main temp y2 x u2 out lv R := by
  funext k; rcases k with i | j
  · fin_cases i <;> rfl
  · rfl
@[simp] theorem up_u2 : Function.update (St M main temp y2 u u2 out lv R) (u2S M) x =
    St M main temp y2 u x out lv R := by
  funext k; rcases k with i | j
  · fin_cases i <;> rfl
  · rfl
@[simp] theorem up_out : Function.update (St M main temp y2 u u2 out lv R) (outS M) x =
    St M main temp y2 u u2 x lv R := by
  funext k; rcases k with i | j
  · fin_cases i <;> rfl
  · rfl
@[simp] theorem up_lv : Function.update (St M main temp y2 u u2 out lv R) (lvS M) x =
    St M main temp y2 u u2 out x R := by
  funext k; rcases k with i | j
  · fin_cases i <;> rfl
  · rfl
@[simp] theorem up_R (j : Fin M.stackCount) :
    Function.update (St M main temp y2 u u2 out lv R) (.inr j) x =
    St M main temp y2 u u2 out lv (Function.update R j x) := by
  funext k; rcases k with i | l
  · rfl
  · simp only [Function.update_apply, St, Sum.inr.injEq]

end St

theorem ne_main_temp : mainS M ≠ tempS M := by simp [mainS, tempS]
theorem ne_temp_y2 : tempS M ≠ y2S M := by simp [tempS, y2S]
theorem ne_temp_u2 : tempS M ≠ u2S M := by simp [tempS, u2S]
theorem ne_y2_u2 : y2S M ≠ u2S M := by simp [y2S, u2S]
theorem ne_u_main : uS M ≠ mainS M := by simp [uS, mainS]
theorem ne_u_out : uS M ≠ outS M := by simp [uS, outS]
theorem ne_main_out : mainS M ≠ outS M := by simp [mainS, outS]
theorem ne_main_y2 : mainS M ≠ y2S M := by simp [mainS, y2S]
theorem ne_u2_u : u2S M ≠ uS M := by simp [u2S, uS]

/-! ## The arithmetic phases -/

theorem it1 {α : Type*} {f : α → α} {a b : α} (h : f a = b) : f^[1] a = b := h

theorem initU_step (v : Control M) (main temp y2 u u2 out lv : List Bool)
    (R : Fin M.stackCount → List Bool) :
    advance (program M c d) ⟨some (.inl .initU), v, St M main temp y2 u u2 out lv R⟩ =
      ⟨some (.inl .mulCheck), v, St M main temp y2 (List.replicate c true ++ u) u2 out
        (List.replicate d true ++ lv) R⟩ := by
  simp only [advance, TM2.step, program, Option.getD_some]
  rw [stepAux_pushTrues, stepAux_pushTrues]
  simp [TM2.stepAux]

theorem extra_step (v : Control M) (main temp y2 u u2 out lv : List Bool)
    (R : Fin M.stackCount → List Bool) :
    advance (program M c d) ⟨some (.inl .mulExtra), v, St M main temp y2 u u2 out lv R⟩ =
      ⟨some (.inl .mulBack), v, St M main temp y2 u (true :: u2) out lv R⟩ := by
  simp only [advance, TM2.step, program, Option.getD_some]
  rw [stepAux_pushTrues]
  simp [TM2.stepAux]

theorem outer_loop (t ys out lv : List Bool) (R : Fin M.stackCount → List Bool)
    (w : Fin M.controlCount) :
    ∀ (n : ℕ) (u2 : List Bool) (o : Option Bool),
      (advance (program M c d))^[n * (2 * ys.length + 4) + 1]
          ⟨some (.inl .mulOuter), (o, w), St M t ys [] (List.replicate n true) u2 out lv R⟩ =
        ⟨some (.inl .mulCollect), (none, w),
          St M t ys [] [] (List.replicate (n * (ys.length + 1)) true ++ u2) out lv R⟩ := by
  intro n
  induction n with
  | zero =>
      intro u2 o
      simp only [zero_mul, zero_add, Function.iterate_one, List.replicate_zero, List.nil_append]
      exact popBranch_nil (program M c d) (uS M) (.inl .mulOuter) (.inl .mulInner)
        (.inl .mulCollect) rfl _ o w rfl
  | succ n ih =>
      intro u2 o
      have ea := popBranch_cons (program M c d) (uS M) (.inl .mulOuter) (.inl .mulInner)
        (.inl .mulCollect) rfl true (List.replicate n true)
        (St M t ys [] (List.replicate (n + 1) true) u2 out lv R) o w rfl
      rw [up_u] at ea
      have eb := moveCount_loop (program M c d) (tempS M) (y2S M) (u2S M) (.inl .mulInner)
        (.inl .mulExtra) (ne_temp_y2 M) (ne_temp_u2 M) (ne_y2_u2 M) rfl ys
        (St M t ys [] (List.replicate n true) u2 out lv R) (some true) w rfl
      simp only [st_y2, st_u2, List.append_nil, up_y2, up_u2, up_temp] at eb
      have ec := extra_step M c d (none, w) t [] ys.reverse (List.replicate n true)
        (List.replicate ys.length true ++ u2) out lv R
      have ed := move_loop (program M c d) (y2S M) (tempS M) (.inl .mulBack) (.inl .mulOuter)
        (ne_temp_y2 M).symm rfl ys.reverse
        (St M t [] ys.reverse (List.replicate n true) (true :: (List.replicate ys.length true ++ u2))
          out lv R) none w rfl
      simp only [st_temp, List.reverse_reverse, List.append_nil, up_temp, up_y2,
        List.length_reverse] at ed
      have ee := ih (true :: (List.replicate ys.length true ++ u2)) none
      have r1 := iter_chain (it1 ea) eb
      have r2 := iter_chain r1 (it1 ec)
      have r3 := iter_chain r2 ed
      have r4 := iter_chain r3 ee
      have hcount : (n + 1) * (2 * ys.length + 4) + 1 =
          1 + (ys.length + 1) + 1 + (ys.length + 1) + (n * (2 * ys.length + 4) + 1) := by ring
      rw [hcount, r4]
      have hl : List.replicate (n * (ys.length + 1)) true ++
            (true :: (List.replicate ys.length true ++ u2)) =
          List.replicate ((n + 1) * (ys.length + 1)) true ++ u2 := by
        rw [show (n + 1) * (ys.length + 1) = n * (ys.length + 1) + (1 + ys.length) by ring,
          List.replicate_add, List.replicate_add, List.append_assoc, List.append_assoc]
        rfl
      rw [hl]

/-- The exact number of transitions of the level loop. -/
def levelTime (m : ℕ) : ℕ → ℕ → ℕ
  | 0, _ => 1
  | k + 1, n => 1 + (n * (2 * m + 4) + 1) + (n * (m + 1) + 1) + levelTime m k (n * (m + 1))

theorem levels (t ys out : List Bool) (R : Fin M.stackCount → List Bool)
    (w : Fin M.controlCount) :
    ∀ (k n : ℕ) (o : Option Bool),
      (advance (program M c d))^[levelTime ys.length k n]
          ⟨some (.inl .mulCheck), (o, w),
            St M t ys [] (List.replicate n true) [] out (List.replicate k true) R⟩ =
        ⟨some (.inl .cut), (none, w),
          St M t ys [] (List.replicate (n * (ys.length + 1) ^ k) true) [] out [] R⟩ := by
  intro k
  induction k with
  | zero =>
      intro n o
      simp only [levelTime, Function.iterate_one, pow_zero, mul_one, List.replicate_zero]
      exact popBranch_nil (program M c d) (lvS M) (.inl .mulCheck) (.inl .mulOuter)
        (.inl .cut) rfl _ o w rfl
  | succ k ih =>
      intro n o
      have ea := popBranch_cons (program M c d) (lvS M) (.inl .mulCheck) (.inl .mulOuter)
        (.inl .cut) rfl true (List.replicate k true)
        (St M t ys [] (List.replicate n true) [] out (List.replicate (k + 1) true) R) o w rfl
      rw [up_lv] at ea
      have eb := outer_loop M c d t ys out (List.replicate k true) R w n [] (some true)
      rw [List.append_nil] at eb
      have ec := move_loop (program M c d) (u2S M) (uS M) (.inl .mulCollect) (.inl .mulCheck)
        (ne_u2_u M) rfl (List.replicate (n * (ys.length + 1)) true)
        (St M t ys [] [] (List.replicate (n * (ys.length + 1)) true) out
          (List.replicate k true) R) none w rfl
      simp only [st_u, List.append_nil, up_u, up_u2, List.reverse_replicate,
        List.length_replicate] at ec
      have ed := ih (n * (ys.length + 1)) none
      have r1 := iter_chain (it1 ea) eb
      have r2 := iter_chain r1 ec
      have r3 := iter_chain r2 ed
      simp only [levelTime]
      rw [show 1 + (n * (2 * ys.length + 4) + 1) + (n * (ys.length + 1) + 1) +
          levelTime ys.length k (n * (ys.length + 1)) =
          1 + (n * (2 * ys.length + 4) + 1) + (n * (ys.length + 1) + 1) +
          levelTime ys.length k (n * (ys.length + 1)) from rfl, r3]
      rw [show n * (ys.length + 1) * (ys.length + 1) ^ k = n * (ys.length + 1) ^ (k + 1) by
        ring]

theorem levelTime_le (m : ℕ) : ∀ k n : ℕ,
    levelTime m k n ≤ (k + 1) * (3 + n * (m + 1) ^ k * (3 * m + 6)) := by
  intro k
  induction k with
  | zero => intro n; simp [levelTime]; omega
  | succ k ih =>
      intro n
      have h := ih (n * (m + 1))
      simp only [levelTime]
      have hp : 1 ≤ (m + 1) ^ (k + 1) := Nat.one_le_pow _ _ (by omega)
      have e1 : n * (m + 1) * (m + 1) ^ k = n * (m + 1) ^ (k + 1) := by ring
      rw [e1] at h
      have h2 : n * (2 * m + 4) + n * (m + 1) ≤ n * (m + 1) ^ (k + 1) * (3 * m + 6) := by
        have : n * (2 * m + 4) + n * (m + 1) ≤ n * 1 * (3 * m + 6) := by nlinarith
        calc n * (2 * m + 4) + n * (m + 1) ≤ n * 1 * (3 * m + 6) := this
          _ ≤ n * (m + 1) ^ (k + 1) * (3 * m + 6) := by gcongr
      nlinarith

end NPOwner1.Trunc
