import Mathlib.Computability.TuringMachine.Computable
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

/-!
# Finite Boolean-stack machines for the computational conclusions

Source: v8 `06-eth.tex`, the fixed deterministic bit-machine convention, and
`B-effectivity-details.tex`, the runtime part of truth-table materialisation.

All stacks have Boolean alphabet; labels and internal control are finite.
In particular no unbounded natural number or callable function is internal
unit-cost memory. One transition is Mathlib's `TM2.step`; its finite statement
has a fixed number of primitive stack operations. These definitions specify
the actual operational target, not a certificate for an arbitrary cost formula.
-/

namespace EthInapproximability.CurrentPaper.BitMachine

open Turing

structure Machine where
  stackCount : ℕ
  labelCount : ℕ
  controlCount : ℕ
  input : Fin stackCount
  output : Fin stackCount
  start : Fin labelCount
  initial : Fin controlCount
  program : Fin labelCount →
    TM2.Stmt (fun _ : Fin stackCount => Bool) (Fin labelCount) (Fin controlCount)

abbrev Machine.Config (M : Machine) :=
  TM2.Cfg (fun _ : Fin M.stackCount => Bool) (Fin M.labelCount) (Fin M.controlCount)

def Machine.init (M : Machine) (bits : List Bool) : M.Config :=
  ⟨some M.start, M.initial, fun k => if k = M.input then bits else []⟩

def Machine.step (M : Machine) (c : M.Config) : M.Config :=
  (TM2.step M.program c).getD c

def Machine.run (M : Machine) (fuel : ℕ) (c : M.Config) : M.Config :=
  (M.step^[fuel]) c

def Machine.OutputsWithin (M : Machine) (input output : List Bool) (time : ℕ) : Prop :=
  ∃ t ≤ time, (M.run t (M.init input)).l = none ∧
    (M.run t (M.init input)).stk M.output = output

def Machine.ComputesWithin (M : Machine) (f : List Bool → List Bool)
    (time : ℕ → ℕ) : Prop :=
  ∀ input, M.OutputsWithin input (f input) (time input.length)

def Polytime (f : List Bool → List Bool) : Prop :=
  ∃ M : Machine, ∃ c d : ℕ, M.ComputesWithin f (fun n => c * (n + 1) ^ d)

@[simp] theorem run_zero (M : Machine) (c : M.Config) : M.run 0 c = c := rfl

theorem run_succ (M : Machine) (n : ℕ) (c : M.Config) :
    M.run (n + 1) c = M.step (M.run n c) := by
  exact Function.iterate_succ_apply' _ _ _

theorem step_halted (M : Machine) (c : M.Config) (h : c.l = none) :
    M.step c = c := by
  cases c with
  | mk l v s => cases l <;> simp_all [Machine.step, TM2.step]

theorem run_halted (M : Machine) (c : M.Config) (h : c.l = none) (n : ℕ) :
    M.run n c = c := by
  induction n with
  | zero => rfl
  | succ n ih => rw [run_succ, ih, step_halted M c h]

theorem run_add (M : Machine) (m n : ℕ) (c : M.Config) :
    M.run (m + n) c = M.run n (M.run m c) := by
  induction n with
  | zero => simp
  | succ n ih => rw [Nat.add_succ, run_succ, ih, run_succ]

theorem outputsWithin_mono (M : Machine) {input output : List Bool} {t u : ℕ}
    (h : M.OutputsWithin input output t) (htu : t ≤ u) :
    M.OutputsWithin input output u := by
  obtain ⟨k, hk, hhalt, hout⟩ := h
  exact ⟨k, hk.trans htu, hhalt, hout⟩

theorem outputsWithin_at_bound (M : Machine) {input output : List Bool} {t : ℕ}
    (h : M.OutputsWithin input output t) :
    (M.run t (M.init input)).l = none ∧
      (M.run t (M.init input)).stk M.output = output := by
  obtain ⟨k, hk, hhalt, hout⟩ := h
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hk
  rw [run_add, run_halted M _ hhalt]
  exact ⟨hhalt, hout⟩

theorem outputsWithin_unique (M : Machine) {input out₁ out₂ : List Bool} {t u : ℕ}
    (h₁ : M.OutputsWithin input out₁ t) (h₂ : M.OutputsWithin input out₂ u) :
    out₁ = out₂ := by
  have h₁' := outputsWithin_at_bound M (outputsWithin_mono M h₁ (Nat.le_max_left t u))
  have h₂' := outputsWithin_at_bound M (outputsWithin_mono M h₂ (Nat.le_max_right t u))
  exact h₁'.2.symm.trans h₂'.2

/-- A syntactic upper bound for the number of pushes in one statement. -/
def pushBound {K Λ σ : Type*} : TM2.Stmt (fun _ : K => Bool) Λ σ → ℕ
  | .push _ _ q => pushBound q + 1
  | .peek _ _ q => pushBound q
  | .pop _ _ q => pushBound q
  | .load _ q => pushBound q
  | .branch _ q₁ q₂ => max (pushBound q₁) (pushBound q₂)
  | .goto _ => 0
  | .halt => 0

theorem stepAux_length {K Λ σ : Type*} [DecidableEq K]
    (q : TM2.Stmt (fun _ : K => Bool) Λ σ) (v : σ)
    (S : K → List Bool) (k : K) :
    ((TM2.stepAux q v S).stk k).length ≤ (S k).length + pushBound q := by
  induction q generalizing v S with
  | push j f q ih =>
      have h := ih v (Function.update S j (f v :: S j))
      simp only [TM2.stepAux, pushBound]
      have hu : ((Function.update S j (f v :: S j)) k).length ≤ (S k).length + 1 := by
        by_cases hk : k = j
        · subst k; simp
        · simp [hk]
      exact h.trans (by have := Nat.add_le_add_right hu (pushBound q); omega)
  | peek j f q ih => exact ih _ _
  | pop j f q ih =>
      have h := ih (f v (S j).head?) (Function.update S j (S j).tail)
      simp only [TM2.stepAux, pushBound]
      exact h.trans (Nat.add_le_add_right (by
        by_cases hk : k = j
        · subst k; simp
        · simp [hk]) _)
  | load f q ih => exact ih _ _
  | branch f q₁ q₂ ih₁ ih₂ =>
      cases h : f v with
      | false =>
          simpa [TM2.stepAux, h, pushBound] using
            (ih₂ v S).trans (Nat.add_le_add_left (Nat.le_max_right _ _) _)
      | true =>
          simpa [TM2.stepAux, h, pushBound] using
            (ih₁ v S).trans (Nat.add_le_add_left (Nat.le_max_left _ _) _)
  | goto f => simp [TM2.stepAux, pushBound]
  | halt => simp [TM2.stepAux, pushBound]

/-- A fixed program-dependent bound, independent of the input. -/
def Machine.pushBound (M : Machine) : ℕ :=
  ∑ l : Fin M.labelCount, BitMachine.pushBound (M.program l)

theorem step_length (M : Machine) (c : M.Config) (k : Fin M.stackCount) :
    ((M.step c).stk k).length ≤ (c.stk k).length + M.pushBound := by
  cases c with
  | mk l v S =>
      cases l with
      | none => simp [Machine.step, TM2.step]
      | some l =>
          have h := stepAux_length (M.program l) v S k
          have hb : BitMachine.pushBound (M.program l) ≤ M.pushBound := by
            unfold Machine.pushBound
            exact Finset.single_le_sum (f := fun j => BitMachine.pushBound (M.program j))
              (fun _ _ => Nat.zero_le _) (Finset.mem_univ l)
          exact h.trans (Nat.add_le_add_left hb _)

theorem run_length (M : Machine) (c : M.Config) (k : Fin M.stackCount) (n : ℕ) :
    ((M.run n c).stk k).length ≤ (c.stk k).length + n * M.pushBound := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [run_succ]
      have h := (step_length M (M.run n c) k).trans (Nat.add_le_add_right ih _)
      simpa [Nat.succ_mul, Nat.add_assoc] using h

theorem output_length_bound (M : Machine) {input output : List Bool} {t : ℕ}
    (h : M.OutputsWithin input output t) :
    output.length ≤ input.length + t * M.pushBound := by
  have hr := run_length M (M.init input) M.output t
  rw [(outputsWithin_at_bound M h).2] at hr
  have hi : ((M.init input).stk M.output).length ≤ input.length := by
    simp only [Machine.init]
    split <;> simp
  exact hr.trans (Nat.add_le_add_right hi _)

end EthInapproximability.CurrentPaper.BitMachine
