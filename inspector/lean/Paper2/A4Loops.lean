import EthInapproximability.CurrentPaper.BitMachineEncoding
import EthInapproximability.CurrentPaper.EncodedCommunication

/-!
# Unit 4 (Paper A) glue: generic Boolean-stack loops (owner lane `owner:a-unit4-shell-3`)

Private, 26 September 2026. Fixed finite statements over an arbitrary stack type `K`,
label type `Λ` and control `Option Bool × W` (the `Option Bool` slot holds the last popped
bit; `W` is untouched), with exact iterated-step lemmas:

* `moveStmt a b`: pop every bit of stack `a` onto stack `b` (reversing); `|a| + 1` steps.
* `parseStmt a b`: consume one self-delimiting `EncodedCommunication.field xs` from the top of
  `a`, pushing its payload onto `b` (reversed); `|xs| + 1` steps; the rest of `a` is kept.
* `emitStmt a b`: pop every bit `x` of `a` and push `x`, then `true`, onto `b`; `|a| + 1` steps.
* `pushFalseStmt`, `unaryFieldStmt k` (push `field (1^k)` in ONE step of `2k + 1` pushes; `k`
  is a fixed parameter of the statement) and `.halt`.

Every step is one `TM2.step` of the literal statement; nothing is inserted into a stack.
**No ledger row is closed.**
-/

namespace Paper2.Unit4Shell.Loops

open Turing
open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.BitMachineEncoding

variable {K Λ W : Type*} [DecidableEq K]

/-- Record the last popped bit. -/
def setBit (v : Option Bool × W) (o : Option Bool) : Option Bool × W := (o, v.2)

def moveStmt (a b : K) (here next : Λ) : TM2.Stmt (fun _ : K => Bool) Λ (Option Bool × W) :=
  .pop a setBit (.branch (fun v => v.1.isSome)
    (.push b (fun v => v.1.getD false) (.goto fun _ => here))
    (.goto fun _ => next))

def parseStmt (a b : K) (here next : Λ) : TM2.Stmt (fun _ : K => Bool) Λ (Option Bool × W) :=
  .pop a setBit (.branch (fun v => v.1.getD false)
    (.pop a setBit (.push b (fun v => v.1.getD false) (.goto fun _ => here)))
    (.goto fun _ => next))

def emitStmt (a b : K) (here next : Λ) : TM2.Stmt (fun _ : K => Bool) Λ (Option Bool × W) :=
  .pop a setBit (.branch (fun v => v.1.isSome)
    (.push b (fun v => v.1.getD false) (.push b (fun _ => true) (.goto fun _ => here)))
    (.goto fun _ => next))

def pushFalseStmt (b : K) (next : Λ) : TM2.Stmt (fun _ : K => Bool) Λ (Option Bool × W) :=
  .push b (fun _ => false) (.goto fun _ => next)

def pushTrues (b : K) : ℕ → TM2.Stmt (fun _ : K => Bool) Λ (Option Bool × W) →
    TM2.Stmt (fun _ : K => Bool) Λ (Option Bool × W)
  | 0, q => q
  | n + 1, q => .push b (fun _ => true) (pushTrues b n q)

def unaryFieldStmt (b : K) (k : ℕ) (next : Λ) :
    TM2.Stmt (fun _ : K => Bool) Λ (Option Bool × W) :=
  .push b (fun _ => false) (pushTrues b (2 * k) (.goto fun _ => next))

/-- The folded emission. -/
def emitFold (acc : List Bool) (x : Bool) : List Bool := true :: x :: acc

theorem iter_chain {α : Type*} {f : α → α} {a b c : α} {m n : ℕ}
    (h1 : f^[m] a = b) (h2 : f^[n] b = c) : f^[m + n] a = c := by
  rw [Nat.add_comm, Function.iterate_add_apply, h1, h2]

variable (P : Λ → TM2.Stmt (fun _ : K => Bool) Λ (Option Bool × W))

theorem move_loop (a b : K) (here next : Λ) (hab : a ≠ b)
    (hP : P here = moveStmt a b here next) :
    ∀ (xs : List Bool) (S : K → List Bool) (o : Option Bool) (w : W), S a = xs →
      (advance P)^[xs.length + 1] ⟨some here, (o, w), S⟩ =
        ⟨some next, (none, w),
          Function.update (Function.update S b (xs.reverse ++ S b)) a []⟩ := by
  intro xs
  induction xs with
  | nil =>
      intro S o w hS
      simp only [List.length_nil, zero_add, Function.iterate_one, List.reverse_nil,
        List.nil_append, Function.update_eq_self]
      simp [advance, TM2.step, TM2.stepAux, hP, moveStmt, setBit, hS]
  | cons x xs ih =>
      intro S o w hS
      have h1 : advance P ⟨some here, (o, w), S⟩ =
          ⟨some here, (some x, w),
            Function.update (Function.update S a xs) b (x :: S b)⟩ := by
        simp [advance, TM2.step, TM2.stepAux, hP, moveStmt, setBit, hS,
          Function.update_of_ne hab.symm]
      rw [List.length_cons, Function.iterate_succ_apply, h1,
        ih _ _ _ (by rw [Function.update_of_ne hab, Function.update_self])]
      rw [Function.update_self, Function.update_idem, Function.update_comm hab,
        Function.update_idem]
      simp

theorem parse_loop (a b : K) (here next : Λ) (hab : a ≠ b)
    (hP : P here = parseStmt a b here next) :
    ∀ (xs rest : List Bool) (S : K → List Bool) (o : Option Bool) (w : W),
      S a = EncodedCommunication.field xs ++ rest →
      (advance P)^[xs.length + 1] ⟨some here, (o, w), S⟩ =
        ⟨some next, (some false, w),
          Function.update (Function.update S b (xs.reverse ++ S b)) a rest⟩ := by
  intro xs
  induction xs with
  | nil =>
      intro rest S o w hS
      simp only [List.length_nil, zero_add, Function.iterate_one, List.reverse_nil,
        List.nil_append, Function.update_eq_self]
      simp [EncodedCommunication.field] at hS
      simp [advance, TM2.step, TM2.stepAux, hP, parseStmt, setBit, hS]
  | cons x xs ih =>
      intro rest S o w hS
      simp only [EncodedCommunication.field, List.cons_append] at hS
      have h1 : advance P ⟨some here, (o, w), S⟩ =
          ⟨some here, (some x, w),
            Function.update (Function.update S a (EncodedCommunication.field xs ++ rest)) b
              (x :: S b)⟩ := by
        simp [advance, TM2.step, TM2.stepAux, hP, parseStmt, setBit, hS,
          Function.update_of_ne hab.symm]
      rw [List.length_cons, Function.iterate_succ_apply, h1,
        ih _ _ _ _ (by rw [Function.update_of_ne hab, Function.update_self])]
      rw [Function.update_self, Function.update_idem, Function.update_comm hab,
        Function.update_idem]
      simp

theorem emit_loop (a b : K) (here next : Λ) (hab : a ≠ b)
    (hP : P here = emitStmt a b here next) :
    ∀ (rs : List Bool) (S : K → List Bool) (o : Option Bool) (w : W), S a = rs →
      (advance P)^[rs.length + 1] ⟨some here, (o, w), S⟩ =
        ⟨some next, (none, w),
          Function.update (Function.update S b (rs.foldl emitFold (S b))) a []⟩ := by
  intro rs
  induction rs with
  | nil =>
      intro S o w hS
      simp only [List.length_nil, zero_add, Function.iterate_one, List.foldl_nil,
        Function.update_eq_self]
      simp [advance, TM2.step, TM2.stepAux, hP, emitStmt, setBit, hS]
  | cons x rs ih =>
      intro S o w hS
      have h1 : advance P ⟨some here, (o, w), S⟩ =
          ⟨some here, (some x, w),
            Function.update (Function.update S a rs) b (emitFold (S b) x)⟩ := by
        simp [advance, TM2.step, TM2.stepAux, hP, emitStmt, setBit, hS, emitFold,
          Function.update_of_ne hab.symm, Function.update_idem]
      rw [List.length_cons, Function.iterate_succ_apply, h1,
        ih _ _ _ (by rw [Function.update_of_ne hab, Function.update_self])]
      rw [Function.update_self, Function.update_idem, Function.update_comm hab,
        Function.update_idem]
      simp

theorem pushFalse_step (b : K) (here next : Λ) (hP : P here = pushFalseStmt b next)
    (v : Option Bool × W) (S : K → List Bool) :
    advance P ⟨some here, v, S⟩ = ⟨some next, v, Function.update S b (false :: S b)⟩ := by
  simp [advance, TM2.step, TM2.stepAux, hP, pushFalseStmt]

theorem stepAux_pushTrues (b : K) :
    ∀ (n : ℕ) (q : TM2.Stmt (fun _ : K => Bool) Λ (Option Bool × W))
      (v : Option Bool × W) (S : K → List Bool),
      TM2.stepAux (pushTrues b n q) v S =
        TM2.stepAux q v (Function.update S b (List.replicate n true ++ S b)) := by
  intro n
  induction n with
  | zero => intro q v S; simp [pushTrues]
  | succ n ih =>
      intro q v S
      simp only [pushTrues, TM2.stepAux]
      rw [ih, Function.update_self, Function.update_idem]
      congr 2
      rw [List.replicate_succ']
      simp

theorem field_replicate (k : ℕ) :
    EncodedCommunication.field (List.replicate k true) =
      List.replicate (2 * k) true ++ [false] := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [List.replicate_succ, EncodedCommunication.field, ih,
        show 2 * (k + 1) = 2 * k + 1 + 1 by ring, List.replicate_succ, List.replicate_succ]
      simp

theorem unaryField_step (b : K) (k : ℕ) (here next : Λ)
    (hP : P here = unaryFieldStmt b k next) (v : Option Bool × W) (S : K → List Bool) :
    advance P ⟨some here, v, S⟩ =
      ⟨some next, v, Function.update S b
        (EncodedCommunication.field (List.replicate k true) ++ S b)⟩ := by
  simp only [advance, TM2.step, hP, unaryFieldStmt, TM2.stepAux, Option.getD_some]
  rw [stepAux_pushTrues, Function.update_self, Function.update_idem, field_replicate]
  simp [TM2.stepAux]

theorem halt_step (here : Λ) (hP : P here = .halt) (v : Option Bool × W)
    (S : K → List Bool) : advance P ⟨some here, v, S⟩ = ⟨none, v, S⟩ := by
  simp [advance, TM2.step, TM2.stepAux, hP]

/-- Emitting the reversed payload on top of `false :: t` writes exactly `field ys ++ t`. -/
theorem emit_reverse_field (ys t : List Bool) :
    ys.reverse.foldl emitFold (false :: t) = EncodedCommunication.field ys ++ t := by
  rw [List.foldl_reverse]
  induction ys with
  | nil => rfl
  | cons y ys ih => rw [List.foldr_cons, ih]; rfl

end Paper2.Unit4Shell.Loops
