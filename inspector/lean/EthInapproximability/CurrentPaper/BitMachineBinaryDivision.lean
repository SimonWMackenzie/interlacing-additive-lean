import EthInapproximability.CurrentPaper.BitMachineBinarySubtract
import EthInapproximability.CurrentPaper.BitMachineBankWrapper
import Mathlib.Tactic

/-!
# Binary long division on seven Boolean stacks

Source: frozen v8 `B-effectivity-details.tex`, `lem:paper-explicit-balanced-family`.
This is a literal fixed finite-program implementation of restoring binary long
division. The dividend is visited MSB first on bank 0, the divisor is LSB first
on bank 1, the running remainder is LSB first on bank 2, and the quotient is
accumulated LSB first on bank 3. Banks 4--6 are scratch. One outer iteration
shifts the remainder by prepending the next bit, simultaneously scans the two
operands with a one-bit borrow, then restores the divisor and either the old
remainder or the difference. No numerical value is a control state or bank
length; every bank has Boolean alphabet and the control type is finite.

The raw program is deliberately exposed so a caller can embed it in a larger
machine. The complete run and quadratic transition bound are proved below.
Framing two operands into a single input stack, and composing this primitive
with prime-field Horner evaluation, are separate implementation steps.
-/

namespace EthInapproximability.CurrentPaper.BitMachineBinaryDivision

open Turing Turing.TM2.Stmt BitMachineEncoding
open BitMachineBinarySubtract

inductive Label where
  | outer | scan | clearOld | clearDiff | restoreOld | restoreDiff | restoreDiv
  deriving DecidableEq, Fintype

structure Control where
  borrow : Bool
  a : Option Bool
  b : Option Bool
  qBit : Bool
  deriving DecidableEq, Fintype

def initial : Control := ⟨false, none, none, false⟩

def program : Label → TM2.Stmt (fun _ : Fin 7 => Bool) Label Control
  | .outer =>
      pop 0 (fun _ a => ⟨false, a, none, false⟩)
        (branch (fun s => s.a.isSome)
          (push 2 (fun s => s.a.getD false)
            (load (fun _ => initial) (goto (fun _ => .scan))))
          (load (fun _ => initial) halt))
  | .scan =>
      pop 2 (fun s a => ⟨s.borrow, a, none, s.qBit⟩)
        (pop 1 (fun s b => ⟨s.borrow, s.a, b, s.qBit⟩)
          (branch (fun s => s.a.isSome || s.b.isSome)
            (branch (fun s => s.a.isSome)
              (push 4 (fun s => s.a.getD false)
                (branch (fun s => s.b.isSome)
                  (push 5 (fun s => s.b.getD false)
                    (push 6 (fun s => outBit (s.a.getD false) (s.b.getD false)
                      s.borrow)
                      (load (fun s => ⟨nextBorrow (s.a.getD false)
                        (s.b.getD false) s.borrow, none, none, false⟩)
                        (goto (fun _ => .scan)))))
                  (push 6 (fun s => outBit (s.a.getD false) false s.borrow)
                    (load (fun s => ⟨nextBorrow (s.a.getD false) false s.borrow,
                      none, none, false⟩) (goto (fun _ => .scan))))))
              (push 5 (fun s => s.b.getD false)
                (push 6 (fun s => outBit false (s.b.getD false) s.borrow)
                  (load (fun s => ⟨nextBorrow false (s.b.getD false) s.borrow,
                    none, none, false⟩) (goto (fun _ => .scan))))))
            (branch (fun s => s.borrow)
              (load (fun s => ⟨s.borrow, none, none, false⟩)
                (goto (fun _ => .clearDiff)))
              (load (fun s => ⟨s.borrow, none, none, true⟩)
                (goto (fun _ => .clearOld))))))
  | .clearOld =>
      pop 4 (fun s a => ⟨s.borrow, a, none, s.qBit⟩)
        (branch (fun s => s.a.isSome)
          (goto (fun _ => .clearOld))
          (goto (fun _ => .restoreDiff)))
  | .clearDiff =>
      pop 6 (fun s a => ⟨s.borrow, a, none, s.qBit⟩)
        (branch (fun s => s.a.isSome)
          (goto (fun _ => .clearDiff))
          (goto (fun _ => .restoreOld)))
  | .restoreOld =>
      pop 4 (fun s a => ⟨s.borrow, a, none, s.qBit⟩)
        (branch (fun s => s.a.isSome)
          (push 2 (fun s => s.a.getD false) (goto (fun _ => .restoreOld)))
          (goto (fun _ => .restoreDiv)))
  | .restoreDiff =>
      pop 6 (fun s a => ⟨s.borrow, a, none, s.qBit⟩)
        (branch (fun s => s.a.isSome)
          (push 2 (fun s => s.a.getD false) (goto (fun _ => .restoreDiff)))
          (goto (fun _ => .restoreDiv)))
  | .restoreDiv =>
      pop 5 (fun s b => ⟨s.borrow, none, b, s.qBit⟩)
        (branch (fun s => s.b.isSome)
          (push 1 (fun s => s.b.getD false) (goto (fun _ => .restoreDiv)))
          (push 3 (fun s => s.qBit)
            (load (fun _ => initial) (goto (fun _ => .outer)))))

def bank (input divisor remainder quotient old saved diff : List Bool) :
    Fin 7 → List Bool :=
  fun k => if k = 0 then input else if k = 1 then divisor else if k = 2 then remainder
    else if k = 3 then quotient else if k = 4 then old else if k = 5 then saved else diff

abbrev Config := TM2.Cfg (fun _ : Fin 7 => Bool) Label Control

def cfg (l : Option Label) (s : Control)
    (input divisor remainder quotient old saved diff : List Bool) : Config :=
  ⟨l, s, bank input divisor remainder quotient old saved diff⟩

def run (t : ℕ) (c : Config) : Config := ((advance program)^[t]) c

/-- LSB-first unsigned subtraction with zero extension. Its second component
is the final borrow. The recursive equations mirror the physical scan. -/
def subAny : List Bool → List Bool → Bool → List Bool × Bool
  | [], [], borrow => ([], borrow)
  | a :: as, [], borrow =>
      let tail := subAny as [] (nextBorrow a false borrow)
      (outBit a false borrow :: tail.1, tail.2)
  | [], b :: bs, borrow =>
      let tail := subAny [] bs (nextBorrow false b borrow)
      (outBit false b borrow :: tail.1, tail.2)
  | a :: as, b :: bs, borrow =>
      let tail := subAny as bs (nextBorrow a b borrow)
      (outBit a b borrow :: tail.1, tail.2)

theorem subAny_length (a b : List Bool) (borrow : Bool) :
    (subAny a b borrow).1.length = max a.length b.length := by
  induction a, b, borrow using subAny.induct with
  | case1 borrow => simp [subAny]
  | case2 a as borrow ih => simp [subAny, ih]
  | case3 b bs borrow ih => simp [subAny, ih]
  | case4 a as b bs borrow ih => simp [subAny, ih, Nat.succ_max_succ]

theorem subAny_value (a b : List Bool) (borrow : Bool) :
    EncodedCommunication.bitsValue a +
        2 ^ (max a.length b.length) * (subAny a b borrow).2.toNat =
      EncodedCommunication.bitsValue b +
        EncodedCommunication.bitsValue (subAny a b borrow).1 + borrow.toNat := by
  induction a, b, borrow using subAny.induct with
  | case1 borrow => cases borrow <;> simp [subAny, EncodedCommunication.bitsValue]
  | case2 a as borrow ih =>
      have h := ih
      simp only [List.length_nil, Nat.max_zero, EncodedCommunication.bitsValue] at h
      have hb := bit_identity a false borrow
      simp only [subAny, EncodedCommunication.bitsValue, Nat.bit_val, List.length_cons,
        List.length_nil, Nat.max_zero, pow_succ]
      have hm : 2 ^ as.length * 2 * (subAny as [] (nextBorrow a false borrow)).2.toNat =
          2 * (2 ^ as.length * (subAny as [] (nextBorrow a false borrow)).2.toNat) := by ring
      simp only [Bool.toNat_false, Nat.zero_add, List.length_nil,
        Nat.max_zero] at *
      omega
  | case3 b bs borrow ih =>
      have h := ih
      simp only [List.length_nil, Nat.zero_max, EncodedCommunication.bitsValue] at h
      have hb := bit_identity false b borrow
      simp only [subAny, EncodedCommunication.bitsValue, Nat.bit_val, List.length_cons,
        List.length_nil, Nat.zero_max, pow_succ]
      have hm : 2 ^ bs.length * 2 * (subAny [] bs (nextBorrow false b borrow)).2.toNat =
          2 * (2 ^ bs.length * (subAny [] bs (nextBorrow false b borrow)).2.toNat) := by ring
      simp only [Bool.toNat_false, Nat.zero_add, List.length_nil,
        Nat.zero_max] at *
      omega
  | case4 a as b bs borrow ih =>
      have h := ih
      have hb := bit_identity a b borrow
      simp only [subAny, EncodedCommunication.bitsValue, Nat.bit_val, List.length_cons,
        Nat.succ_max_succ, pow_succ]
      have hm : 2 ^ max as.length bs.length * 2 *
          (subAny as bs (nextBorrow a b borrow)).2.toNat =
          2 * (2 ^ max as.length bs.length *
            (subAny as bs (nextBorrow a b borrow)).2.toNat) := by ring
      omega

theorem subAny_spec (a b : List Bool) :
    (subAny a b false).2 =
      decide (EncodedCommunication.bitsValue a < EncodedCommunication.bitsValue b) ∧
    EncodedCommunication.bitsValue (subAny a b false).1 =
      EncodedCommunication.bitsValue a +
        2 ^ max a.length b.length * (subAny a b false).2.toNat -
          EncodedCommunication.bitsValue b := by
  have hv := subAny_value a b false
  have hl := subAny_length a b false
  have hd := bitsValue_lt_pow (subAny a b false).1
  rw [hl] at hd
  constructor
  · cases hb : (subAny a b false).2 <;>
      simp only [hb, Bool.toNat_false, Bool.toNat_true, Nat.mul_zero, Nat.mul_one,
        Nat.add_zero] at hv ⊢
    · have hnot : ¬ EncodedCommunication.bitsValue a <
          EncodedCommunication.bitsValue b := by omega
      simp [hnot]
    · have hlt : EncodedCommunication.bitsValue a <
          EncodedCommunication.bitsValue b := by omega
      simp [hlt]
  · simp only [Bool.toNat_false, Nat.add_zero] at hv
    omega

theorem run_step {c d : Config} (h : TM2.step program c = some d) (t : ℕ) :
    run (t + 1) c = run t d := by
  simp only [run, Function.iterate_succ_apply, advance, h, Option.getD_some]

theorem run_add {c d : Config} {t : ℕ} (h : run t c = d) (u : ℕ) :
    run (t + u) c = run u d := by
  rw [Nat.add_comm t u]
  simp only [run, Function.iterate_add_apply] at h ⊢
  rw [h]

private theorem step_scan_both (input quotient old saved diff as bs : List Bool)
    (a b : Bool) (borrow : Bool) :
    TM2.step program
      (cfg (some .scan) ⟨borrow, none, none, false⟩ input (b :: bs)
        (a :: as) quotient old saved diff) =
      some (cfg (some .scan) ⟨nextBorrow a b borrow, none, none, false⟩
        input bs as quotient (a :: old) (b :: saved)
        (outBit a b borrow :: diff)) := by
  simp [TM2.step, TM2.stepAux, program, cfg, bank]
  funext k
  fin_cases k <;> simp [bank]

private theorem step_scan_left (input quotient old saved diff as : List Bool)
    (a : Bool) (borrow : Bool) :
    TM2.step program
      (cfg (some .scan) ⟨borrow, none, none, false⟩ input []
        (a :: as) quotient old saved diff) =
      some (cfg (some .scan) ⟨nextBorrow a false borrow, none, none, false⟩
        input [] as quotient (a :: old) saved
        (outBit a false borrow :: diff)) := by
  simp [TM2.step, TM2.stepAux, program, cfg, bank]
  funext k
  fin_cases k <;> simp [bank]

private theorem step_scan_right (input quotient old saved diff bs : List Bool)
    (b : Bool) (borrow : Bool) :
    TM2.step program
      (cfg (some .scan) ⟨borrow, none, none, false⟩ input (b :: bs)
        [] quotient old saved diff) =
      some (cfg (some .scan) ⟨nextBorrow false b borrow, none, none, false⟩
        input bs [] quotient old (b :: saved)
        (outBit false b borrow :: diff)) := by
  simp [TM2.step, TM2.stepAux, program, cfg, bank]
  funext k
  fin_cases k <;> simp [bank]

private theorem step_scan_done (input quotient old saved diff : List Bool)
    (borrow : Bool) :
    TM2.step program
      (cfg (some .scan) ⟨borrow, none, none, false⟩ input [] []
        quotient old saved diff) =
      some (cfg (some (if borrow then .clearDiff else .clearOld))
        ⟨borrow, none, none, !borrow⟩ input [] [] quotient old saved diff) := by
  cases borrow <;>
    simp [TM2.step, TM2.stepAux, program, cfg, bank]
  all_goals
    funext k
    fin_cases k <;> simp [bank]

theorem scan_correct (a b : List Bool) (borrow : Bool)
    (input quotient old saved diff : List Bool) :
    run (max a.length b.length + 1)
      (cfg (some .scan) ⟨borrow, none, none, false⟩
        input b a quotient old saved diff) =
      cfg (some (if (subAny a b borrow).2 then .clearDiff else .clearOld))
        ⟨(subAny a b borrow).2, none, none, !(subAny a b borrow).2⟩
        input [] [] quotient (a.reverse ++ old) (b.reverse ++ saved)
        ((subAny a b borrow).1.reverse ++ diff) := by
  induction a, b, borrow using subAny.induct generalizing old saved diff with
  | case1 borrow =>
      simpa [subAny] using run_step (step_scan_done input quotient old saved diff borrow) 0
  | case2 a as borrow ih =>
      have h := run_step (step_scan_left input quotient old saved diff as a borrow)
        (max as.length 0 + 1)
      rw [show max (a :: as).length ([] : List Bool).length + 1 =
          (max as.length 0 + 1) + 1 by simp]
      simpa [subAny, List.reverse_cons, List.append_assoc] using
        h.trans (ih (a :: old) saved
          (outBit a false borrow :: diff))
  | case3 b bs borrow ih =>
      have h := run_step (step_scan_right input quotient old saved diff bs b borrow)
        (max 0 bs.length + 1)
      rw [show max ([] : List Bool).length (b :: bs).length + 1 =
          (max 0 bs.length + 1) + 1 by simp]
      simpa [subAny, List.reverse_cons, List.append_assoc] using
        h.trans (ih old (b :: saved)
          (outBit false b borrow :: diff))
  | case4 a as b bs borrow ih =>
      have h := run_step (step_scan_both input quotient old saved diff as bs a b borrow)
        (max as.length bs.length + 1)
      rw [show max (a :: as).length (b :: bs).length + 1 =
          (max as.length bs.length + 1) + 1 by simp [Nat.succ_max_succ]]
      simpa [subAny, List.reverse_cons, List.append_assoc] using
        h.trans (ih (a :: old) (b :: saved)
          (outBit a b borrow :: diff))

private theorem step_clear_old_cons (s : Control) (input d r q saved diff old : List Bool)
    (x : Bool) :
    TM2.step program (cfg (some .clearOld) s input d r q (x :: old) saved diff) =
      some (cfg (some .clearOld) ⟨s.borrow, some x, none, s.qBit⟩
        input d r q old saved diff) := by
  simp [TM2.step, TM2.stepAux, program, cfg, bank]
  funext k
  fin_cases k <;> simp [bank]

private theorem step_clear_old_nil (s : Control) (input d r q saved diff : List Bool) :
    TM2.step program (cfg (some .clearOld) s input d r q [] saved diff) =
      some (cfg (some .restoreDiff) ⟨s.borrow, none, none, s.qBit⟩
        input d r q [] saved diff) := by
  simp [TM2.step, TM2.stepAux, program, cfg, bank]

private theorem step_clear_diff_cons (s : Control) (input d r q old saved diff : List Bool)
    (x : Bool) :
    TM2.step program (cfg (some .clearDiff) s input d r q old saved (x :: diff)) =
      some (cfg (some .clearDiff) ⟨s.borrow, some x, none, s.qBit⟩
        input d r q old saved diff) := by
  simp [TM2.step, TM2.stepAux, program, cfg, bank]
  funext k
  fin_cases k <;> simp [bank]

private theorem step_clear_diff_nil (s : Control) (input d r q old saved : List Bool) :
    TM2.step program (cfg (some .clearDiff) s input d r q old saved []) =
      some (cfg (some .restoreOld) ⟨s.borrow, none, none, s.qBit⟩
        input d r q old saved []) := by
  simp [TM2.step, TM2.stepAux, program, cfg, bank]

private theorem step_restore_old_cons (s : Control) (input d r q saved diff old : List Bool)
    (x : Bool) :
    TM2.step program (cfg (some .restoreOld) s input d r q (x :: old) saved diff) =
      some (cfg (some .restoreOld) ⟨s.borrow, some x, none, s.qBit⟩
        input d (x :: r) q old saved diff) := by
  simp [TM2.step, TM2.stepAux, program, cfg, bank]
  funext k
  fin_cases k <;> simp [bank]

private theorem step_restore_old_nil (s : Control) (input d r q saved diff : List Bool) :
    TM2.step program (cfg (some .restoreOld) s input d r q [] saved diff) =
      some (cfg (some .restoreDiv) ⟨s.borrow, none, none, s.qBit⟩
        input d r q [] saved diff) := by
  simp [TM2.step, TM2.stepAux, program, cfg, bank]

private theorem step_restore_diff_cons (s : Control) (input d r q old saved diff : List Bool)
    (x : Bool) :
    TM2.step program (cfg (some .restoreDiff) s input d r q old saved (x :: diff)) =
      some (cfg (some .restoreDiff) ⟨s.borrow, some x, none, s.qBit⟩
        input d (x :: r) q old saved diff) := by
  simp [TM2.step, TM2.stepAux, program, cfg, bank]
  funext k
  fin_cases k <;> simp [bank]

private theorem step_restore_diff_nil (s : Control) (input d r q old saved : List Bool) :
    TM2.step program (cfg (some .restoreDiff) s input d r q old saved []) =
      some (cfg (some .restoreDiv) ⟨s.borrow, none, none, s.qBit⟩
        input d r q old saved []) := by
  simp [TM2.step, TM2.stepAux, program, cfg, bank]

private theorem step_restore_div_cons (s : Control) (input d r q old diff saved : List Bool)
    (x : Bool) :
    TM2.step program (cfg (some .restoreDiv) s input d r q old (x :: saved) diff) =
      some (cfg (some .restoreDiv) ⟨s.borrow, none, some x, s.qBit⟩
        input (x :: d) r q old saved diff) := by
  simp [TM2.step, TM2.stepAux, program, cfg, bank]
  funext k
  fin_cases k <;> simp [bank]

private theorem step_restore_div_nil (s : Control) (input d r q old diff : List Bool) :
    TM2.step program (cfg (some .restoreDiv) s input d r q old [] diff) =
      some (cfg (some .outer) initial input d r (s.qBit :: q) old [] diff) := by
  simp [TM2.step, TM2.stepAux, program, cfg, bank]
  funext k
  fin_cases k <;> simp [bank]

theorem clearOld_correct (s : Control) (input d r q old saved diff : List Bool) :
    run (old.length + 1) (cfg (some .clearOld) s input d r q old saved diff) =
      cfg (some .restoreDiff) ⟨s.borrow, none, none, s.qBit⟩
        input d r q [] saved diff := by
  induction old generalizing s with
  | nil => simpa using run_step (step_clear_old_nil s input d r q saved diff) 0
  | cons x old ih =>
      rw [List.length_cons, run_step (step_clear_old_cons s input d r q saved diff old x)]
      simpa using ih ⟨s.borrow, some x, none, s.qBit⟩

theorem clearDiff_correct (s : Control) (input d r q old saved diff : List Bool) :
    run (diff.length + 1) (cfg (some .clearDiff) s input d r q old saved diff) =
      cfg (some .restoreOld) ⟨s.borrow, none, none, s.qBit⟩
        input d r q old saved [] := by
  induction diff generalizing s with
  | nil => simpa using run_step (step_clear_diff_nil s input d r q old saved) 0
  | cons x diff ih =>
      rw [List.length_cons, run_step (step_clear_diff_cons s input d r q old saved diff x)]
      simpa using ih ⟨s.borrow, some x, none, s.qBit⟩

theorem restoreOld_correct (s : Control) (input d r q old saved diff : List Bool) :
    run (old.length + 1) (cfg (some .restoreOld) s input d r q old saved diff) =
      cfg (some .restoreDiv) ⟨s.borrow, none, none, s.qBit⟩
        input d (old.reverse ++ r) q [] saved diff := by
  induction old generalizing s r with
  | nil => simpa using run_step (step_restore_old_nil s input d r q saved diff) 0
  | cons x old ih =>
      rw [List.length_cons, run_step (step_restore_old_cons s input d r q saved diff old x)]
      simpa [List.reverse_cons, List.append_assoc] using
        ih ⟨s.borrow, some x, none, s.qBit⟩ (x :: r)

theorem restoreDiff_correct (s : Control) (input d r q old saved diff : List Bool) :
    run (diff.length + 1) (cfg (some .restoreDiff) s input d r q old saved diff) =
      cfg (some .restoreDiv) ⟨s.borrow, none, none, s.qBit⟩
        input d (diff.reverse ++ r) q old saved [] := by
  induction diff generalizing s r with
  | nil => simpa using run_step (step_restore_diff_nil s input d r q old saved) 0
  | cons x diff ih =>
      rw [List.length_cons, run_step (step_restore_diff_cons s input d r q old saved diff x)]
      simpa [List.reverse_cons, List.append_assoc] using
        ih ⟨s.borrow, some x, none, s.qBit⟩ (x :: r)

theorem restoreDiv_correct (s : Control) (input d r q old saved diff : List Bool) :
    run (saved.length + 1) (cfg (some .restoreDiv) s input d r q old saved diff) =
      cfg (some .outer) initial input (saved.reverse ++ d) r (s.qBit :: q)
        old [] diff := by
  induction saved generalizing s d with
  | nil => simpa using run_step (step_restore_div_nil s input d r q old diff) 0
  | cons x saved ih =>
      rw [List.length_cons, run_step (step_restore_div_cons s input d r q old diff saved x)]
      simpa [List.reverse_cons, List.append_assoc] using
        ih ⟨s.borrow, none, some x, s.qBit⟩ (x :: d)

def stepRemainder (r d : List Bool) : List Bool :=
  if (subAny r d false).2 then r else (subAny r d false).1

def stepQuotient (r d : List Bool) : Bool := !(subAny r d false).2

def cycleTime (r d : List Bool) : ℕ :=
  2 * max r.length d.length + r.length + d.length + 5

private theorem step_outer_cons (s : Control) (input divisor remainder quotient : List Bool)
    (bit : Bool) :
    TM2.step program (cfg (some .outer) s (bit :: input) divisor remainder
      quotient [] [] []) =
      some (cfg (some .scan) initial input divisor (bit :: remainder)
        quotient [] [] []) := by
  simp [TM2.step, TM2.stepAux, program, cfg, bank]
  funext k
  fin_cases k <;> simp [bank]

private theorem step_outer_nil (s : Control) (divisor remainder quotient : List Bool) :
    TM2.step program (cfg (some .outer) s [] divisor remainder quotient [] [] []) =
      some (cfg none initial [] divisor remainder quotient [] [] []) := by
  simp [TM2.step, TM2.stepAux, program, cfg, bank]

theorem finishTrial (input divisor r quotient : List Bool) :
    run (r.length + (subAny r divisor false).1.length + divisor.length + 3)
      (cfg (some (if (subAny r divisor false).2 then .clearDiff else .clearOld))
        ⟨(subAny r divisor false).2, none, none, !(subAny r divisor false).2⟩
        input [] [] quotient r.reverse divisor.reverse
        (subAny r divisor false).1.reverse) =
      cfg (some .outer) initial input divisor (stepRemainder r divisor)
        (stepQuotient r divisor :: quotient) [] [] [] := by
  let trial := subAny r divisor false
  change run (r.length + trial.1.length + divisor.length + 3)
      (cfg (some (if trial.2 then .clearDiff else .clearOld))
        ⟨trial.2, none, none, !trial.2⟩ input [] [] quotient
        r.reverse divisor.reverse trial.1.reverse) =
    cfg (some .outer) initial input divisor (stepRemainder r divisor)
      (stepQuotient r divisor :: quotient) [] [] []
  cases hb : trial.2 with
  | false =>
      have hc := clearOld_correct ⟨false, none, none, true⟩ input [] [] quotient
        r.reverse divisor.reverse trial.1.reverse
      have hr := restoreDiff_correct ⟨false, none, none, true⟩ input [] [] quotient
        [] divisor.reverse trial.1.reverse
      have hd := restoreDiv_correct ⟨false, none, none, true⟩ input [] trial.1
        quotient [] divisor.reverse []
      simp only [List.length_reverse, List.reverse_reverse] at hc hr hd
      have h := run_add hc (trial.1.length + 1)
      rw [hr] at h
      have h2 := run_add h (divisor.length + 1)
      simp only [List.append_nil] at h2 hd
      rw [hd] at h2
      have ht : r.length + trial.1.length + divisor.length + 3 =
          (r.length + 1) + (trial.1.length + 1) + (divisor.length + 1) := by omega
      rw [ht]
      simpa [trial, hb, stepRemainder, stepQuotient] using h2
  | true =>
      have hc := clearDiff_correct ⟨true, none, none, false⟩ input [] [] quotient
        r.reverse divisor.reverse trial.1.reverse
      have hr := restoreOld_correct ⟨true, none, none, false⟩ input [] [] quotient
        r.reverse divisor.reverse []
      have hd := restoreDiv_correct ⟨true, none, none, false⟩ input [] r
        quotient [] divisor.reverse []
      simp only [List.length_reverse, List.reverse_reverse] at hc hr hd
      have h := run_add hc (r.length + 1)
      rw [hr] at h
      have h2 := run_add h (divisor.length + 1)
      simp only [List.append_nil] at h2 hd
      rw [hd] at h2
      have ht : r.length + trial.1.length + divisor.length + 3 =
          (trial.1.length + 1) + (r.length + 1) + (divisor.length + 1) := by omega
      rw [ht]
      simpa [trial, hb, stepRemainder, stepQuotient] using h2

/-- One quotient bit, including every scan, discard, restore and cleanup
transition. The unchanged divisor and empty scratch banks are part of the
postcondition, so the theorem can be iterated without an oracle. -/
theorem oneStep (input divisor remainder quotient : List Bool) (bit : Bool) :
    run (cycleTime (bit :: remainder) divisor)
      (cfg (some .outer) initial (bit :: input) divisor remainder quotient [] [] []) =
      cfg (some .outer) initial input divisor
        (stepRemainder (bit :: remainder) divisor)
        (stepQuotient (bit :: remainder) divisor :: quotient) [] [] [] := by
  let r := bit :: remainder
  let trial := subAny r divisor false
  have ho := step_outer_cons initial input divisor remainder quotient bit
  have hs := scan_correct r divisor false input quotient [] [] []
  have hf := finishTrial input divisor r quotient
  simp only [List.append_nil] at hs
  have hl := subAny_length r divisor false
  have h := run_step ho (max r.length divisor.length + 1)
  dsimp only [r] at hs
  dsimp only [r] at h
  have h' := h.trans hs
  have h2 := run_add h' (r.length + trial.1.length + divisor.length + 3)
  rw [hf] at h2
  have ht : cycleTime (bit :: remainder) divisor =
      (max r.length divisor.length + 1 + 1) +
        (r.length + trial.1.length + divisor.length + 3) := by
    change 2 * max r.length divisor.length + r.length + divisor.length + 5 =
      (max r.length divisor.length + 1 + 1) +
        (r.length + trial.1.length + divisor.length + 3)
    rw [hl]
    omega
  rw [ht]
  exact h2

def divideFrom : List Bool → List Bool → List Bool → List Bool → List Bool × List Bool
  | [], _, remainder, quotient => (remainder, quotient)
  | bit :: tail, divisor, remainder, quotient =>
      divideFrom tail divisor (stepRemainder (bit :: remainder) divisor)
        (stepQuotient (bit :: remainder) divisor :: quotient)

def totalTime : List Bool → List Bool → List Bool → ℕ
  | [], _, _ => 1
  | bit :: tail, divisor, remainder =>
      cycleTime (bit :: remainder) divisor +
        totalTime tail divisor (stepRemainder (bit :: remainder) divisor)

theorem total_run (input divisor remainder quotient : List Bool) :
    run (totalTime input divisor remainder)
      (cfg (some .outer) initial input divisor remainder quotient [] [] []) =
      cfg none initial [] divisor (divideFrom input divisor remainder quotient).1
        (divideFrom input divisor remainder quotient).2 [] [] [] := by
  induction input generalizing remainder quotient with
  | nil =>
      simpa [totalTime, divideFrom] using
        run_step (step_outer_nil initial divisor remainder quotient) 0
  | cons bit tail ih =>
      simp only [totalTime, divideFrom]
      have hs := oneStep tail divisor remainder quotient bit
      have hr := ih (stepRemainder (bit :: remainder) divisor)
        (stepQuotient (bit :: remainder) divisor :: quotient)
      exact (run_add hs _).trans hr

theorem stepRemainder_length (r d : List Bool) :
    (stepRemainder r d).length ≤ max r.length d.length := by
  unfold stepRemainder
  split
  · exact le_max_left _ _
  · rw [subAny_length]

theorem totalTime_bound (input divisor remainder : List Bool) (N : ℕ)
    (h : remainder.length + input.length ≤ N + divisor.length)
    (hN : input.length ≤ N) :
    totalTime input divisor remainder ≤
      input.length * (4 * (N + divisor.length + 1) + 5) + 1 := by
  induction input generalizing remainder with
  | nil => simp [totalTime]
  | cons bit tail ih =>
      have hrem := stepRemainder_length (bit :: remainder) divisor
      have hnext : (stepRemainder (bit :: remainder) divisor).length + tail.length ≤
          N + divisor.length := by
        simp only [List.length_cons] at h
        simp only [List.length_cons] at hN
        have hmax : max (remainder.length + 1) divisor.length + tail.length ≤
            N + divisor.length := by omega
        exact (Nat.add_le_add_right hrem _).trans hmax
      have htail : tail.length ≤ N := by simp at hN; omega
      have ht := ih _ hnext htail
      have hcycle : cycleTime (bit :: remainder) divisor ≤
          4 * (N + divisor.length + 1) + 5 := by
        unfold cycleTime
        have hmax : max (remainder.length + 1) divisor.length ≤
            N + divisor.length := by
          simp only [List.length_cons] at h
          simp only [List.length_cons] at hN
          omega
        simp only [List.length_cons]
        omega
      simp only [totalTime, List.length_cons]
      have he : (tail.length + 1) * (4 * (N + divisor.length + 1) + 5) =
          tail.length * (4 * (N + divisor.length + 1) + 5) +
            (4 * (N + divisor.length + 1) + 5) := by ring
      rw [he]
      omega

/-- For the standard empty-remainder start, the actual transition count is
quadratic in the two input bit lengths. This bound does not depend on their
numeric values. -/
theorem standard_time_bound (input divisor : List Bool) :
    totalTime input divisor [] ≤
      (input.length + 1) * (4 * (input.length + divisor.length + 1) + 5) := by
  have h := totalTime_bound input divisor [] input.length
    (by simp) le_rfl
  have he : (input.length + 1) * (4 * (input.length + divisor.length + 1) + 5) =
      input.length * (4 * (input.length + divisor.length + 1) + 5) +
        (4 * (input.length + divisor.length + 1) + 5) := by ring
  rw [he]
  omega

theorem step_value (r d : List Bool) :
    EncodedCommunication.bitsValue r =
      EncodedCommunication.bitsValue d * (stepQuotient r d).toNat +
        EncodedCommunication.bitsValue (stepRemainder r d) := by
  have hs := (subAny_spec r d).2
  have hc := (subAny_spec r d).1
  cases hb : (subAny r d false).2 with
  | false =>
      have hn : EncodedCommunication.bitsValue d ≤ EncodedCommunication.bitsValue r := by
        apply Nat.le_of_not_gt
        intro hlt
        simp [hlt, hb] at hc
      have hs' : EncodedCommunication.bitsValue (subAny r d false).1 =
          EncodedCommunication.bitsValue r - EncodedCommunication.bitsValue d := by
        simpa [hb] using hs
      simp [stepQuotient, stepRemainder, hb]
      omega
  | true =>
      simp [stepQuotient, stepRemainder, hb]

theorem step_remainder_lt (r d : List Bool)
    (hr : EncodedCommunication.bitsValue r < 2 * EncodedCommunication.bitsValue d) :
    EncodedCommunication.bitsValue (stepRemainder r d) <
      EncodedCommunication.bitsValue d := by
  have hs := (subAny_spec r d).2
  have hc := (subAny_spec r d).1
  cases hb : (subAny r d false).2 with
  | false =>
      have hn : EncodedCommunication.bitsValue d ≤ EncodedCommunication.bitsValue r := by
        apply Nat.le_of_not_gt
        intro hlt
        simp [hlt, hb] at hc
      have hs' : EncodedCommunication.bitsValue (subAny r d false).1 =
          EncodedCommunication.bitsValue r - EncodedCommunication.bitsValue d := by
        simpa [hb] using hs
      simp [stepRemainder, hb]
      omega
  | true =>
      have hlt : EncodedCommunication.bitsValue r < EncodedCommunication.bitsValue d := by
        by_contra hn
        have : ¬ EncodedCommunication.bitsValue r < EncodedCommunication.bitsValue d := hn
        simp [this, hb] at hc
      simpa [stepRemainder, hb] using hlt

def msbValue (bits : List Bool) : ℕ :=
  bits.foldl (fun n b => Nat.bit b n) 0

def extendValue (start : ℕ) (bits : List Bool) : ℕ :=
  bits.foldl (fun n b => Nat.bit b n) start

theorem extendValue_nil (start : ℕ) : extendValue start [] = start := rfl

theorem extendValue_cons (start : ℕ) (bit : Bool) (tail : List Bool) :
    extendValue start (bit :: tail) =
      extendValue (Nat.bit bit start) tail := rfl

theorem step_bound_of_remainder_lt (bit : Bool) (r d : List Bool)
    (hr : EncodedCommunication.bitsValue r < EncodedCommunication.bitsValue d) :
    EncodedCommunication.bitsValue (stepRemainder (bit :: r) d) <
      EncodedCommunication.bitsValue d := by
  apply step_remainder_lt _ _
  simp only [EncodedCommunication.bitsValue, Nat.bit_val]
  cases bit <;> simp <;> omega

theorem step_combined (bit : Bool) (r d q : List Bool) :
    EncodedCommunication.bitsValue d *
        EncodedCommunication.bitsValue (stepQuotient (bit :: r) d :: q) +
      EncodedCommunication.bitsValue (stepRemainder (bit :: r) d) =
    Nat.bit bit (EncodedCommunication.bitsValue d * EncodedCommunication.bitsValue q +
      EncodedCommunication.bitsValue r) := by
  have h := step_value (bit :: r) d
  simp only [EncodedCommunication.bitsValue, Nat.bit_val] at h ⊢
  cases bit with
  | false =>
      simp only [Bool.toNat_false] at h ⊢
      have hm : EncodedCommunication.bitsValue d *
          (2 * EncodedCommunication.bitsValue q +
            (stepQuotient (false :: r) d).toNat) =
          2 * (EncodedCommunication.bitsValue d * EncodedCommunication.bitsValue q) +
            EncodedCommunication.bitsValue d * (stepQuotient (false :: r) d).toNat := by ring
      rw [hm]
      omega
  | true =>
      simp only [Bool.toNat_true] at h ⊢
      have hm : EncodedCommunication.bitsValue d *
          (2 * EncodedCommunication.bitsValue q +
            (stepQuotient (true :: r) d).toNat) =
          2 * (EncodedCommunication.bitsValue d * EncodedCommunication.bitsValue q) +
            EncodedCommunication.bitsValue d * (stepQuotient (true :: r) d).toNat := by ring
      rw [hm]
      omega

theorem divideFrom_spec (input d r q : List Bool)
    (hr : EncodedCommunication.bitsValue r < EncodedCommunication.bitsValue d) :
    let result := divideFrom input d r q
    EncodedCommunication.bitsValue result.1 < EncodedCommunication.bitsValue d ∧
      EncodedCommunication.bitsValue d * EncodedCommunication.bitsValue result.2 +
        EncodedCommunication.bitsValue result.1 =
          extendValue (EncodedCommunication.bitsValue d * EncodedCommunication.bitsValue q +
            EncodedCommunication.bitsValue r) input := by
  induction input generalizing r q with
  | nil => simp [divideFrom, extendValue, hr]
  | cons bit tail ih =>
      have hnext := step_bound_of_remainder_lt bit r d hr
      have hs := step_combined bit r d q
      have htail := ih (stepRemainder (bit :: r) d)
        (stepQuotient (bit :: r) d :: q) hnext
      simpa [divideFrom, extendValue_cons, hs] using htail

/-- On a positive divisor, the physical output banks contain exactly the
ordinary quotient and remainder of the MSB-first dividend. Leading zero bits
in either operand are allowed. The zero-divisor case is outside this domain. -/
theorem standard_division_spec (input divisor : List Bool)
    (hd : 0 < EncodedCommunication.bitsValue divisor) :
    let result := divideFrom input divisor [] []
    EncodedCommunication.bitsValue result.2 =
      msbValue input / EncodedCommunication.bitsValue divisor ∧
    EncodedCommunication.bitsValue result.1 =
      msbValue input % EncodedCommunication.bitsValue divisor := by
  have hs := divideFrom_spec input divisor [] [] (by simpa using hd)
  simp only [EncodedCommunication.bitsValue, Nat.mul_zero, Nat.zero_add,
    extendValue] at hs
  let result := divideFrom input divisor [] []
  change EncodedCommunication.bitsValue result.2 =
      msbValue input / EncodedCommunication.bitsValue divisor ∧
    EncodedCommunication.bitsValue result.1 =
      msbValue input % EncodedCommunication.bitsValue divisor
  have hmod : msbValue input % EncodedCommunication.bitsValue divisor =
      EncodedCommunication.bitsValue result.1 := by
    change (input.foldl (fun n b => Nat.bit b n) 0) % _ = _
    rw [← hs.2, Nat.mul_add_mod_self_left, Nat.mod_eq_of_lt hs.1]
  have hdiv : msbValue input / EncodedCommunication.bitsValue divisor =
      EncodedCommunication.bitsValue result.2 := by
    change (input.foldl (fun n b => Nat.bit b n) 0) / _ = _
    rw [← hs.2, Nat.mul_add_div hd, Nat.div_eq_of_lt hs.1]
    simp [result]
  exact ⟨hdiv.symm, hmod.symm⟩

/-- Final reusable raw-bank contract. The dividend is MSB-first; quotient,
divisor and remainder are LSB-first. All three scratch banks start and finish
empty. The positive-divisor guard is required for `/` and `%` semantics. -/
theorem standard_run_correct (input divisor : List Bool)
    (hd : 0 < EncodedCommunication.bitsValue divisor) :
    let result := run (totalTime input divisor [])
      (cfg (some .outer) initial input divisor [] [] [] [] [])
    result.l = none ∧
      EncodedCommunication.bitsValue (result.stk 3) =
        msbValue input / EncodedCommunication.bitsValue divisor ∧
      EncodedCommunication.bitsValue (result.stk 2) =
        msbValue input % EncodedCommunication.bitsValue divisor ∧
      result.stk 1 = divisor ∧ result.stk 4 = [] ∧
      result.stk 5 = [] ∧ result.stk 6 = [] ∧
      totalTime input divisor [] ≤
        (input.length + 1) * (4 * (input.length + divisor.length + 1) + 5) := by
  have hr := total_run input divisor [] []
  have hs := standard_division_spec input divisor hd
  have ht := standard_time_bound input divisor
  rw [hr]
  simp [cfg, bank, hs.1, hs.2, ht]

theorem divideFrom_quotient_length (input divisor remainder quotient : List Bool) :
    (divideFrom input divisor remainder quotient).2.length =
      input.length + quotient.length := by
  induction input generalizing remainder quotient with
  | nil => simp [divideFrom]
  | cons bit tail ih =>
      simp only [divideFrom, List.length_cons]
      rw [ih]
      simp only [List.length_cons]
      omega

theorem divideFrom_remainder_length (input divisor remainder quotient : List Bool)
    (N : ℕ) (h : remainder.length + input.length ≤ N + divisor.length)
    (hN : input.length ≤ N) :
    (divideFrom input divisor remainder quotient).1.length ≤ N + divisor.length := by
  induction input generalizing remainder quotient with
  | nil => simpa [divideFrom] using h
  | cons bit tail ih =>
      have hr := stepRemainder_length (bit :: remainder) divisor
      have hnext : (stepRemainder (bit :: remainder) divisor).length + tail.length ≤
          N + divisor.length := by
        simp only [List.length_cons] at h hN
        have hmax : max (remainder.length + 1) divisor.length + tail.length ≤
            N + divisor.length := by omega
        exact (Nat.add_le_add_right hr _).trans hmax
      have htail : tail.length ≤ N := by simp only [List.length_cons] at hN; omega
      simpa only [divideFrom] using ih _ _ hnext htail

def initialBank (input divisor : List Bool) : Fin 7 → List Bool :=
  bank input divisor [] [] [] [] []

def finalBank (input divisor : List Bool) : Fin 7 → List Bool :=
  bank [] divisor (divideFrom input divisor [] []).1
    (divideFrom input divisor [] []).2 [] [] []

theorem initialBank_code_length (input divisor : List Bool) :
    (BitMachineBankCodec.encode (initialBank input divisor)).length =
      2 * (input.length + divisor.length) + 7 := by
  rw [BitMachineBankCodec.encode_length]
  simp [initialBank, bank, Fin.sum_univ_succ]

theorem finalBank_code_length_le (input divisor : List Bool) :
    (BitMachineBankCodec.encode (finalBank input divisor)).length ≤
      4 * (input.length + divisor.length) + 7 := by
  have hq := divideFrom_quotient_length input divisor [] []
  have hr := divideFrom_remainder_length input divisor [] []
    input.length (by simp) le_rfl
  rw [BitMachineBankCodec.encode_length]
  simp [finalBank, bank, Fin.sum_univ_succ]
  simp at hq
  omega

def packedInput (input divisor : List Bool) : List Bool :=
  BitMachineBankCodec.encode (initialBank input divisor)

theorem packed_standard_run (input divisor : List Bool) :
    ∃ (u : ℕ) (S' : Fin 7 → List Bool),
      u ≤ 100 * ((packedInput input divisor).length + 1) ^ 2 ∧
      BitMachineBankWrapper.run program .outer initial u
        (BitMachineBankWrapper.cfg
          (some (.inr (.parse (.scan 0)))) (initial, none)
          (fun _ : Fin 7 => []) (packedInput input divisor) [] []) =
        BitMachineBankWrapper.cfg none (initial, none) S' [] []
          (BitMachineBankCodec.encode (finalBank input divisor)) := by
  let c := cfg none initial [] divisor
    (divideFrom input divisor [] []).1
    (divideFrom input divisor [] []).2 [] [] []
  have hdecode : BitMachineBankCodec.decode 7 (packedInput input divisor) =
      some (initialBank input divisor) := by
    simp [packedInput]
  have hrun : run (totalTime input divisor [])
      (cfg (some .outer) initial input divisor [] [] [] [] []) = c := by
    simpa [c] using total_run input divisor [] []
  have hlocal : ((advance program)^[totalTime input divisor []])
      (⟨some Label.outer, initial, initialBank input divisor⟩ : Config) = c := by
    simpa only [run, cfg, initialBank] using hrun
  have hhalt : c.l = none := rfl
  obtain ⟨u, S', hu, hr⟩ := BitMachineBankWrapper.packed_run
    program .outer initial (packedInput input divisor) (initialBank input divisor)
    hdecode (totalTime input divisor []) c hlocal hhalt
  have hfinal : c.stk = finalBank input divisor := rfl
  rw [hfinal] at hu hr
  have he : BitMachineBankSerialize.encode (List.ofFn (finalBank input divisor)) =
      BitMachineBankCodec.encode (finalBank input divisor) := by
    rw [BitMachineBankCodec.encode_eq_list]
    rfl
  rw [he] at hu hr
  have hsize := finalBank_code_length_le input divisor
  have htime := standard_time_bound input divisor
  have hinput := initialBank_code_length input divisor
  refine ⟨u, S', ?_, ?_⟩
  · unfold packedInput at *
    rw [hinput] at hu ⊢
    have hmul : (input.length + 1) *
        (4 * (input.length + divisor.length + 1) + 5) ≤
        (input.length + divisor.length + 1) *
          (4 * (input.length + divisor.length + 1) + 5) := by
      exact Nat.mul_le_mul_right _ (by omega)
    nlinarith
  · exact hr

noncomputable def packedMachine : BitMachine.Machine :=
  BitMachineBankWrapper.machine program .outer initial

/-- The fixed single-input finite machine executes the framed two-word
division packet in quadratic input-bitlength time. This theorem is deliberately
restricted to canonical packets with empty scratch banks; it is not a claim
that every arbitrary seven-field packet computes Euclidean division. -/
theorem packed_outputs (input divisor : List Bool) :
    packedMachine.OutputsWithin (packedInput input divisor)
      (BitMachineBankCodec.encode (finalBank input divisor))
      (100 * ((packedInput input divisor).length + 1) ^ 2) := by
  obtain ⟨u, S', hu, hr⟩ := packed_standard_run input divisor
  change (BitMachineBankWrapper.machine program .outer initial).OutputsWithin
    (packedInput input divisor) (BitMachineBankCodec.encode (finalBank input divisor))
    (100 * ((packedInput input divisor).length + 1) ^ 2)
  apply outputsWithin_of_raw_run (.inr 0) (.inr 2)
    (.inr (.parse (.scan 0))) (initial, none)
    (BitMachineBankWrapper.program program .outer initial)
    (packedInput input divisor)
    (BitMachineBankCodec.encode (finalBank input divisor)) u _ hu
  · rw [BitMachineBankWrapper.initial_cfg]
    change (BitMachineBankWrapper.run program .outer initial u _).l = none
    rw [hr]
    rfl
  · rw [BitMachineBankWrapper.initial_cfg]
    change (BitMachineBankWrapper.run program .outer initial u _).stk (.inr 2) = _
    rw [hr]
    rfl

end EthInapproximability.CurrentPaper.BitMachineBinaryDivision
