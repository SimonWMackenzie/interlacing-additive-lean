import EthInapproximability.CurrentPaper.BitMachineBinaryDivision
import EthInapproximability.CurrentPaper.BitMachineInline
import EthInapproximability.CurrentPaper.BitMachineTrimLeadingZeros
import EthInapproximability.CurrentPaper.PrimeSamplerBinaryDigit
import Mathlib.Tactic

/-!
The physical Euclidean controller.  Banks 0--6 have exactly the layout of
`BitMachineBinaryDivision`: MSB-first dividend, LSB-first divisor, remainder,
quotient, and three scratch words.  The controller scans the remainder without
losing it, clears the quotient, reverses the old divisor into the next
dividend, and moves the remainder into the next divisor.  It never stores a
natural number in finite control.

The component division run and its clock are in the inherited verified
`BitMachineBinaryDivision` module.  This file deliberately separates the raw
controller from packet framing and rational canonicalization.
-/

namespace CurrentAdditive.BinaryGCDCore

open Turing Turing.TM2.Stmt
open EthInapproximability.CurrentPaper
open BitMachineEncoding

inductive Label where
  | divide (l : BitMachineBinaryDivision.Label)
  | checkDivisor | restoreDivisor
  | test | restore | clearQuotient | moveDivisor | reverseRemainder
  | trimRemainder | moveRemainder
  deriving DecidableEq, Fintype

structure Control where
  division : BitMachineBinaryDivision.Control
  nonzero : Bool
  bit : Option Bool
  deriving DecidableEq, Fintype

def initial : Control := ⟨BitMachineBinaryDivision.initial, false, none⟩

def program : Label → TM2.Stmt (fun _ : Fin 7 => Bool) Label Control
  | .divide l => BitMachineInline.stmt Label.divide
      (fun v => (⟨v, false, none⟩ : Control)) Control.division (some .test)
      (BitMachineBinaryDivision.program l)
  | .checkDivisor =>
      pop 1 (fun s b => ⟨s.division, s.nonzero || b.getD false, b⟩)
        (branch (fun s => s.bit.isSome)
          (push 5 (fun s => s.bit.getD false) (goto (fun _ => .checkDivisor)))
          (goto (fun _ => .restoreDivisor)))
  | .restoreDivisor =>
      pop 5 (fun s b => ⟨s.division, s.nonzero, b⟩)
        (branch (fun s => s.bit.isSome)
          (push 1 (fun s => s.bit.getD false) (goto (fun _ => .restoreDivisor)))
          (branch Control.nonzero
            (load (fun _ => initial) (goto (fun _ => .divide .outer)))
            (load (fun _ => initial) halt)))
  | .test =>
      pop 2 (fun s b => ⟨s.division, s.nonzero || b.getD false, b⟩)
        (branch (fun s => s.bit.isSome)
          (push 4 (fun s => s.bit.getD false) (goto (fun _ => .test)))
          (goto (fun _ => .restore)))
  | .restore =>
      pop 4 (fun s b => ⟨s.division, s.nonzero, b⟩)
        (branch (fun s => s.bit.isSome)
          (push 2 (fun s => s.bit.getD false) (goto (fun _ => .restore)))
          (branch Control.nonzero (goto (fun _ => .clearQuotient)) halt))
  | .clearQuotient =>
      pop 3 (fun s b => ⟨s.division, s.nonzero, b⟩)
        (branch (fun s => s.bit.isSome)
          (goto (fun _ => .clearQuotient))
          (goto (fun _ => .moveDivisor)))
  | .moveDivisor =>
      pop 1 (fun s b => ⟨s.division, s.nonzero, b⟩)
        (branch (fun s => s.bit.isSome)
          (push 0 (fun s => s.bit.getD false) (goto (fun _ => .moveDivisor)))
          (goto (fun _ => .reverseRemainder)))
  | .reverseRemainder =>
      pop 2 (fun s b => ⟨s.division, s.nonzero, b⟩)
        (branch (fun s => s.bit.isSome)
          (push 4 (fun s => s.bit.getD false) (goto (fun _ => .reverseRemainder)))
          (goto (fun _ => .trimRemainder)))
  | .trimRemainder =>
      pop 4 (fun s b => ⟨s.division, s.nonzero, b⟩)
        (branch (fun s => s.bit.isSome)
          (branch (fun s => s.bit.getD false)
            (push 4 (fun _ => true) (goto (fun _ => .moveRemainder)))
            (goto (fun _ => .trimRemainder)))
          (goto (fun _ => .moveRemainder)))
  | .moveRemainder =>
      pop 4 (fun s b => ⟨s.division, s.nonzero, b⟩)
        (branch (fun s => s.bit.isSome)
          (push 1 (fun s => s.bit.getD false) (goto (fun _ => .moveRemainder)))
          (load (fun _ => initial) (goto (fun _ => .divide .outer))))

abbrev Bank := Fin 7 → List Bool
abbrev Config := TM2.Cfg (fun _ : Fin 7 => Bool) Label Control

def bank (input divisor remainder quotient old saved diff : List Bool) : Bank :=
  BitMachineBinaryDivision.bank input divisor remainder quotient old saved diff

def cfg (l : Option Label) (s : Control)
    (input divisor remainder quotient old saved diff : List Bool) : Config :=
  ⟨l, s, bank input divisor remainder quotient old saved diff⟩

def run (t : Nat) (c : Config) : Config := ((advance program)^[t]) c

private theorem run_step {c d : Config} (h : TM2.step program c = some d) (t : Nat) :
    run (t + 1) c = run t d := by
  simp only [run, Function.iterate_succ_apply, advance, h, Option.getD_some]

private theorem run_add {c d : Config} {t : Nat} (h : run t c = d) (u : Nat) :
    run (t + u) c = run u d := by
  rw [Nat.add_comm t u]
  simp only [run, Function.iterate_add_apply] at h ⊢
  rw [h]

private theorem check_cons (s : Control) (x : Bool)
    (i d r q old saved diff : List Bool) :
    TM2.step program (cfg (some .checkDivisor) s i (x :: d) r q old saved diff) =
      some (cfg (some .checkDivisor) ⟨s.division, s.nonzero || x, some x⟩
        i d r q old (x :: saved) diff) := by
  simp [TM2.step, TM2.stepAux, program, cfg, bank,
    BitMachineBinaryDivision.bank]
  funext k; fin_cases k <;> simp [bank, BitMachineBinaryDivision.bank]

private theorem check_nil (s : Control) (i r q old saved diff : List Bool) :
    TM2.step program (cfg (some .checkDivisor) s i [] r q old saved diff) =
      some (cfg (some .restoreDivisor) ⟨s.division, s.nonzero, none⟩
        i [] r q old saved diff) := by
  simp [TM2.step, TM2.stepAux, program, cfg, bank,
    BitMachineBinaryDivision.bank]

private theorem check_run (s : Control) (i d r q old saved diff : List Bool) :
    run (d.length + 1) (cfg (some .checkDivisor) s i d r q old saved diff) =
      cfg (some .restoreDivisor) ⟨s.division, s.nonzero || d.any id, none⟩
        i [] r q old (d.reverse ++ saved) diff := by
  induction d generalizing s saved with
  | nil => simpa [run, advance, check_nil] using
      run_step (check_nil s i r q old saved diff) 0
  | cons x xs ih =>
      rw [List.length_cons, run_step (check_cons s x i xs r q old saved diff)]
      simpa [List.any_cons, Bool.or_assoc, List.reverse_cons, List.append_assoc]
        using ih ⟨s.division, s.nonzero || x, some x⟩ (x :: saved)

private theorem restore_divisor_cons (s : Control) (x : Bool)
    (i d r q old saved diff : List Bool) :
    TM2.step program (cfg (some .restoreDivisor) s i d r q old (x :: saved) diff) =
      some (cfg (some .restoreDivisor) ⟨s.division, s.nonzero, some x⟩
        i (x :: d) r q old saved diff) := by
  simp [TM2.step, TM2.stepAux, program, cfg, bank,
    BitMachineBinaryDivision.bank]
  funext k; fin_cases k <;> simp [bank, BitMachineBinaryDivision.bank]

private theorem restore_divisor_nil (s : Control)
    (i d r q old diff : List Bool) :
    TM2.step program (cfg (some .restoreDivisor) s i d r q old [] diff) =
      some (cfg (if s.nonzero then some (.divide .outer) else none)
        initial i d r q old [] diff) := by
  cases s with
  | mk division nonzero bit =>
      cases nonzero <;> simp [TM2.step, TM2.stepAux, program, cfg, bank,
        BitMachineBinaryDivision.bank, initial]

private theorem restore_divisor_run (s : Control)
    (i d r q old saved diff : List Bool) :
    run (saved.length + 1)
      (cfg (some .restoreDivisor) s i d r q old saved diff) =
      cfg (if s.nonzero then some (.divide .outer) else none) initial
        i (saved.reverse ++ d) r q old [] diff := by
  induction saved generalizing s d with
  | nil => simpa [run, advance, restore_divisor_nil] using
      run_step (restore_divisor_nil s i d r q old diff) 0
  | cons x xs ih =>
      rw [List.length_cons, run_step
        (restore_divisor_cons s x i d r q old xs diff)]
      simpa [List.reverse_cons, List.append_assoc]
        using ih ⟨s.division, s.nonzero, some x⟩ (x :: d)

theorem check_divisor (input divisor : List Bool) :
    run (2 * divisor.length + 2)
      (cfg (some .checkDivisor) initial input divisor [] [] [] [] []) =
      cfg (if divisor.any id then some (.divide .outer) else none) initial
        input divisor [] [] [] [] [] := by
  have hc := check_run initial input divisor [] [] [] [] []
  have hr := restore_divisor_run
    ⟨BitMachineBinaryDivision.initial, divisor.any id, none⟩
    input [] [] [] [] divisor.reverse []
  have h := (run_add hc _).trans (by
    simpa [initial, List.append_nil] using hr)
  simpa [List.reverse_reverse, List.append_nil, Nat.two_mul,
    Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, initial] using h

private theorem test_cons (s : Control) (x : Bool)
    (i d r q old saved diff : List Bool) :
    TM2.step program (cfg (some .test) s i d (x :: r) q old saved diff) =
      some (cfg (some .test) ⟨s.division, s.nonzero || x, some x⟩
        i d r q (x :: old) saved diff) := by
  simp [TM2.step, TM2.stepAux, program, cfg, bank,
    BitMachineBinaryDivision.bank]
  funext k; fin_cases k <;> simp [bank, BitMachineBinaryDivision.bank]

private theorem test_nil (s : Control) (i d q old saved diff : List Bool) :
    TM2.step program (cfg (some .test) s i d [] q old saved diff) =
      some (cfg (some .restore) ⟨s.division, s.nonzero, none⟩
        i d [] q old saved diff) := by
  simp [TM2.step, TM2.stepAux, program, cfg, bank,
    BitMachineBinaryDivision.bank]

private theorem restore_cons (s : Control) (x : Bool)
    (i d r q old saved diff : List Bool) :
    TM2.step program (cfg (some .restore) s i d r q (x :: old) saved diff) =
      some (cfg (some .restore) ⟨s.division, s.nonzero, some x⟩
        i d (x :: r) q old saved diff) := by
  simp [TM2.step, TM2.stepAux, program, cfg, bank,
    BitMachineBinaryDivision.bank]
  funext k; fin_cases k <;> simp [bank, BitMachineBinaryDivision.bank]

private theorem restore_nil (s : Control) (i d r q saved diff : List Bool) :
    TM2.step program (cfg (some .restore) s i d r q [] saved diff) =
      some (cfg (if s.nonzero then some .clearQuotient else none)
        ⟨s.division, s.nonzero, none⟩
        i d r q [] saved diff) := by
  cases s with
  | mk division nonzero bit =>
      cases nonzero <;> simp [TM2.step, TM2.stepAux, program, cfg, bank,
        BitMachineBinaryDivision.bank]

private theorem test_run (s : Control) (i d r q old saved diff : List Bool) :
    run (r.length + 1) (cfg (some .test) s i d r q old saved diff) =
      cfg (some .restore) ⟨s.division, s.nonzero || r.any id, none⟩
        i d [] q (r.reverse ++ old) saved diff := by
  induction r generalizing s old with
  | nil => simpa [run] using run_step (test_nil s i d q old saved diff) 0
  | cons x xs ih =>
      rw [List.length_cons, run_step (test_cons s x i d xs q old saved diff)]
      simpa [List.any_cons, Bool.or_assoc, List.reverse_cons, List.append_assoc]
        using ih ⟨s.division, s.nonzero || x, some x⟩ (x :: old)

private theorem restore_run (s : Control) (i d r q old saved diff : List Bool) :
    run (old.length + 1) (cfg (some .restore) s i d r q old saved diff) =
      cfg (if s.nonzero then some .clearQuotient else none)
        ⟨s.division, s.nonzero, none⟩
        i d (old.reverse ++ r) q [] saved diff := by
  induction old generalizing s r with
  | nil =>
      simpa [run, advance, restore_nil] using
        run_step (restore_nil s i d r q saved diff) 0
  | cons x xs ih =>
      rw [List.length_cons, run_step (restore_cons s x i d r q xs saved diff)]
      simpa [List.reverse_cons, List.append_assoc]
        using ih ⟨s.division, s.nonzero, some x⟩ (x :: r)

theorem scan_remainder (s : Control) (i d r q saved diff : List Bool) :
    run (2 * r.length + 2)
      (cfg (some .test) s i d r q [] saved diff) =
    cfg (if (s.nonzero || r.any id) then some .clearQuotient else none)
      ⟨s.division, s.nonzero || r.any id, none⟩ i d r q [] saved diff := by
  have ht := test_run s i d r q [] saved diff
  have hr := restore_run ⟨s.division, s.nonzero || r.any id, none⟩
    i d [] q r.reverse saved diff
  have h := (run_add ht (r.length + 1)).trans (by
    simpa only [List.length_reverse, List.append_nil] using hr)
  simpa [run, List.reverse_reverse, List.append_nil,
    Nat.two_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

private theorem clear_cons (s : Control) (x : Bool)
    (i d r q old saved diff : List Bool) :
    TM2.step program (cfg (some .clearQuotient) s i d r (x :: q) old saved diff) =
      some (cfg (some .clearQuotient) ⟨s.division, s.nonzero, some x⟩
        i d r q old saved diff) := by
  simp [TM2.step, TM2.stepAux, program, cfg, bank,
    BitMachineBinaryDivision.bank]
  funext k; fin_cases k <;> simp [bank, BitMachineBinaryDivision.bank]

private theorem clear_nil (s : Control) (i d r old saved diff : List Bool) :
    TM2.step program (cfg (some .clearQuotient) s i d r [] old saved diff) =
      some (cfg (some .moveDivisor) ⟨s.division, s.nonzero, none⟩
        i d r [] old saved diff) := by
  simp [TM2.step, TM2.stepAux, program, cfg, bank,
    BitMachineBinaryDivision.bank]

theorem clear_quotient (s : Control) (i d r q old saved diff : List Bool) :
    run (q.length + 1) (cfg (some .clearQuotient) s i d r q old saved diff) =
      cfg (some .moveDivisor) ⟨s.division, s.nonzero, none⟩
        i d r [] old saved diff := by
  induction q generalizing s with
  | nil => simpa [run, advance, clear_nil] using
      run_step (clear_nil s i d r old saved diff) 0
  | cons x xs ih =>
      rw [List.length_cons, run_step (clear_cons s x i d r xs old saved diff)]
      simpa using ih ⟨s.division, s.nonzero, some x⟩

private theorem move_divisor_cons (s : Control) (x : Bool)
    (i d r q old saved diff : List Bool) :
    TM2.step program (cfg (some .moveDivisor) s i (x :: d) r q old saved diff) =
      some (cfg (some .moveDivisor) ⟨s.division, s.nonzero, some x⟩
        (x :: i) d r q old saved diff) := by
  simp [TM2.step, TM2.stepAux, program, cfg, bank,
    BitMachineBinaryDivision.bank]
  funext k; fin_cases k <;> simp [bank, BitMachineBinaryDivision.bank]

private theorem move_divisor_nil (s : Control)
    (i r q old saved diff : List Bool) :
    TM2.step program (cfg (some .moveDivisor) s i [] r q old saved diff) =
      some (cfg (some .reverseRemainder) ⟨s.division, s.nonzero, none⟩
        i [] r q old saved diff) := by
  simp [TM2.step, TM2.stepAux, program, cfg, bank,
    BitMachineBinaryDivision.bank]

theorem move_divisor (s : Control) (i d r q old saved diff : List Bool) :
    run (d.length + 1) (cfg (some .moveDivisor) s i d r q old saved diff) =
      cfg (some .reverseRemainder) ⟨s.division, s.nonzero, none⟩
        (d.reverse ++ i) [] r q old saved diff := by
  induction d generalizing s i with
  | nil => simpa [run, advance, move_divisor_nil] using
      run_step (move_divisor_nil s i r q old saved diff) 0
  | cons x xs ih =>
      rw [List.length_cons, run_step (move_divisor_cons s x i xs r q old saved diff)]
      simpa [List.reverse_cons, List.append_assoc]
        using ih ⟨s.division, s.nonzero, some x⟩ (x :: i)

private theorem reverse_remainder_cons (s : Control) (x : Bool)
    (i d r q old saved diff : List Bool) :
    TM2.step program (cfg (some .reverseRemainder) s i d (x :: r) q old saved diff) =
      some (cfg (some .reverseRemainder) ⟨s.division, s.nonzero, some x⟩
        i d r q (x :: old) saved diff) := by
  simp [TM2.step, TM2.stepAux, program, cfg, bank,
    BitMachineBinaryDivision.bank]
  funext k; fin_cases k <;> simp [bank, BitMachineBinaryDivision.bank]

private theorem reverse_remainder_nil (s : Control)
    (i d q old saved diff : List Bool) :
    TM2.step program (cfg (some .reverseRemainder) s i d [] q old saved diff) =
      some (cfg (some .trimRemainder) ⟨s.division, s.nonzero, none⟩
        i d [] q old saved diff) := by
  simp [TM2.step, TM2.stepAux, program, cfg, bank,
    BitMachineBinaryDivision.bank]

theorem reverse_remainder (s : Control) (i d r q old saved diff : List Bool) :
    run (r.length + 1) (cfg (some .reverseRemainder) s i d r q old saved diff) =
      cfg (some .trimRemainder) ⟨s.division, s.nonzero, none⟩
        i d [] q (r.reverse ++ old) saved diff := by
  induction r generalizing s old with
  | nil => simpa [run, advance, reverse_remainder_nil] using
      run_step (reverse_remainder_nil s i d q old saved diff) 0
  | cons x xs ih =>
      rw [List.length_cons, run_step (reverse_remainder_cons s x i d xs q old saved diff)]
      simpa [List.reverse_cons, List.append_assoc]
        using ih ⟨s.division, s.nonzero, some x⟩ (x :: old)

private theorem move_remainder_cons (s : Control) (x : Bool)
    (i d r q old saved diff : List Bool) :
    TM2.step program (cfg (some .moveRemainder) s i d r q (x :: old) saved diff) =
      some (cfg (some .moveRemainder) ⟨s.division, s.nonzero, some x⟩
        i (x :: d) r q old saved diff) := by
  simp [TM2.step, TM2.stepAux, program, cfg, bank,
    BitMachineBinaryDivision.bank]
  funext k; fin_cases k <;> simp [bank, BitMachineBinaryDivision.bank]

private theorem move_remainder_nil (s : Control)
    (i d r q saved diff : List Bool) :
    TM2.step program (cfg (some .moveRemainder) s i d r q [] saved diff) =
      some (cfg (some (.divide .outer)) initial i d r q [] saved diff) := by
  simp [TM2.step, TM2.stepAux, program, cfg, bank,
    BitMachineBinaryDivision.bank]

theorem move_remainder (s : Control) (i d r q old saved diff : List Bool) :
    run (old.length + 1) (cfg (some .moveRemainder) s i d r q old saved diff) =
      cfg (some (.divide .outer)) initial
        i (old.reverse ++ d) r q [] saved diff := by
  induction old generalizing s d with
  | nil => simpa [run, advance, move_remainder_nil] using
      run_step (move_remainder_nil s i d r q saved diff) 0
  | cons x xs ih =>
      rw [List.length_cons, run_step (move_remainder_cons s x i d r q xs saved diff)]
      simpa [List.reverse_cons, List.append_assoc]
        using ih ⟨s.division, s.nonzero, some x⟩ (x :: d)

/-- The administrative transitions prepare exactly the next Euclidean pair.
The old dividend has already been consumed by the division subroutine. -/
def trimMSB : List Bool → List Bool
  | [] => []
  | false :: xs => trimMSB xs
  | true :: xs => true :: xs

private theorem trim_false (s : Control)
    (i d r q saved diff : List Bool) (xs : List Bool) :
    TM2.step program (cfg (some .trimRemainder) s i d r q (false :: xs) saved diff) =
      some (cfg (some .trimRemainder) ⟨s.division, s.nonzero, some false⟩
        i d r q xs saved diff) := by
  simp [TM2.step, TM2.stepAux, program, cfg, bank,
    BitMachineBinaryDivision.bank]
  funext k; fin_cases k <;> simp [bank, BitMachineBinaryDivision.bank]

private theorem trim_true (s : Control)
    (i d r q saved diff : List Bool) (xs : List Bool) :
    TM2.step program (cfg (some .trimRemainder) s i d r q (true :: xs) saved diff) =
      some (cfg (some .moveRemainder) ⟨s.division, s.nonzero, some true⟩
        i d r q (true :: xs) saved diff) := by
  simp [TM2.step, TM2.stepAux, program, cfg, bank,
    BitMachineBinaryDivision.bank]

private theorem trim_nil (s : Control) (i d r q saved diff : List Bool) :
    TM2.step program (cfg (some .trimRemainder) s i d r q [] saved diff) =
      some (cfg (some .moveRemainder) ⟨s.division, s.nonzero, none⟩
        i d r q [] saved diff) := by
  simp [TM2.step, TM2.stepAux, program, cfg, bank,
    BitMachineBinaryDivision.bank]

def trimTime : List Bool → Nat
  | [] => 1
  | false :: xs => trimTime xs + 1
  | true :: _ => 1

theorem trim_run (s : Control) (i d r q saved diff : List Bool) (xs : List Bool) :
    run (trimTime xs) (cfg (some .trimRemainder) s i d r q xs saved diff) =
      cfg (some .moveRemainder) ⟨s.division, s.nonzero, (trimMSB xs).head?⟩
        i d r q (trimMSB xs) saved diff := by
  induction xs generalizing s with
  | nil =>
      simpa [trimTime, trimMSB, run, advance, trim_nil] using
        run_step (trim_nil s i d r q saved diff) 0
  | cons x xs ih =>
      cases x with
      | false =>
          rw [trimTime, run_step (trim_false s i d r q saved diff xs)]
          simpa [trimMSB] using ih ⟨s.division, s.nonzero, some false⟩
      | true =>
          simpa [trimTime, trimMSB, run, advance, trim_true] using
            run_step (trim_true s i d r q saved diff xs) 0

theorem trimTime_le (xs : List Bool) : trimTime xs ≤ xs.length + 1 := by
  induction xs with
  | nil => simp [trimTime]
  | cons x xs ih => cases x <;> simp [trimTime]; omega

theorem trimMSB_length_le (xs : List Bool) : (trimMSB xs).length ≤ xs.length := by
  induction xs with
  | nil => simp [trimMSB]
  | cons x xs ih => cases x <;> simp [trimMSB]; omega

theorem prepare_next (s : Control) (d r q : List Bool) :
    ∃ t ≤ q.length + d.length + 2 * r.length + trimTime r.reverse + 4,
    run t
      (cfg (some .clearQuotient) s [] d r q [] [] []) =
      cfg (some (.divide .outer)) initial d.reverse
        (trimMSB r.reverse).reverse [] [] [] [] [] := by
  have hq := clear_quotient s [] d r q [] [] []
  have hd := move_divisor ⟨s.division, s.nonzero, none⟩ [] d r [] [] [] []
  have hr := reverse_remainder ⟨s.division, s.nonzero, none⟩ d.reverse [] r [] [] [] []
  have ht := trim_run ⟨s.division, s.nonzero, none⟩ d.reverse [] [] [] [] [] r.reverse
  have hm := move_remainder
    ⟨s.division, s.nonzero, (trimMSB r.reverse).head?⟩ d.reverse [] [] []
    (trimMSB r.reverse) [] []
  have h01 : run ((q.length + 1) + (d.length + 1))
      (cfg (some .clearQuotient) s [] d r q [] [] []) =
      cfg (some .reverseRemainder) ⟨s.division, s.nonzero, none⟩
        d.reverse [] r [] [] [] [] := by
    simpa [List.append_nil] using (run_add hq _).trans hd
  have h02 : run (((q.length + 1) + (d.length + 1)) + (r.length + 1))
      (cfg (some .clearQuotient) s [] d r q [] [] []) =
      cfg (some .trimRemainder) ⟨s.division, s.nonzero, none⟩
        d.reverse [] [] [] r.reverse [] [] := by
    simpa [List.append_nil] using (run_add h01 _).trans hr
  have h03 := (run_add h02 _).trans ht
  have h04 := (run_add h03 _).trans hm
  refine ⟨((q.length + 1) + (d.length + 1)) + (r.length + 1) +
    trimTime r.reverse + ((trimMSB r.reverse).length + 1), ?_, ?_⟩
  · have hlen := trimMSB_length_le r.reverse
    simp only [List.length_reverse] at hlen
    omega
  · simpa [List.reverse_reverse, List.append_nil, Nat.two_mul,
      Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h04

theorem any_iff_value_ne_zero (r : List Bool) :
    r.any id = decide (EncodedCommunication.bitsValue r ≠ 0) := by
  induction r with
  | nil => simp [EncodedCommunication.bitsValue]
  | cons x xs ih =>
      cases x <;>
        simp [EncodedCommunication.bitsValue, Nat.bit_val, List.any_cons, ih]

theorem division_run (input divisor : List Bool) :
    ∃ t ≤ BitMachineBinaryDivision.totalTime input divisor [],
      run t (cfg (some (.divide .outer)) initial input divisor [] [] [] [] []) =
      cfg (some .test) initial [] divisor
        (BitMachineBinaryDivision.divideFrom input divisor [] []).1
        (BitMachineBinaryDivision.divideFrom input divisor [] []).2 [] [] [] := by
  let cLocal : BitMachineBinaryDivision.Config :=
    BitMachineBinaryDivision.cfg (some .outer) BitMachineBinaryDivision.initial
      input divisor [] [] [] [] []
  have hlocal : ((advance BitMachineBinaryDivision.program)^[
      BitMachineBinaryDivision.totalTime input divisor []]) cLocal =
      BitMachineBinaryDivision.cfg none BitMachineBinaryDivision.initial [] divisor
        (BitMachineBinaryDivision.divideFrom input divisor [] []).1
        (BitMachineBinaryDivision.divideFrom input divisor [] []).2 [] [] [] := by
    exact BitMachineBinaryDivision.total_run input divisor [] []
  have hhalt : (((advance BitMachineBinaryDivision.program)^[
      BitMachineBinaryDivision.totalTime input divisor []]) cLocal).l = none := by
    rw [hlocal]
    rfl
  obtain ⟨t, ht, hr⟩ := BitMachineInline.outputs
    Label.divide (fun v => (⟨v, false, none⟩ : Control)) Control.division
    (by intro v; rfl) (some .test)
    BitMachineBinaryDivision.program program (by intro l; rfl)
    cLocal (BitMachineBinaryDivision.totalTime input divisor []) hhalt
  refine ⟨t, ht, ?_⟩
  rw [hlocal] at hr
  simpa [run, cfg, bank, initial, cLocal, BitMachineInline.cfg,
    BitMachineBinaryDivision.cfg] using hr

def remainder (input divisor : List Bool) : List Bool :=
  (BitMachineBinaryDivision.divideFrom input divisor [] []).1

def quotient (input divisor : List Bool) : List Bool :=
  (BitMachineBinaryDivision.divideFrom input divisor [] []).2

def normalizedRemainder (input divisor : List Bool) : List Bool :=
  (trimMSB (remainder input divisor).reverse).reverse

theorem trimMSB_eq_inherited (xs : List Bool) :
    trimMSB xs = BitMachineTrimLeadingZeros.trim xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases x <;> simp [trimMSB, BitMachineTrimLeadingZeros.trim, ih]

theorem normalizedRemainder_value (input divisor : List Bool) :
    EncodedCommunication.bitsValue (normalizedRemainder input divisor) =
      EncodedCommunication.bitsValue (remainder input divisor) := by
  have h1 := PrimeSamplerBinaryDigit.msbValue_reverse
    (normalizedRemainder input divisor)
  have h2 := PrimeSamplerBinaryDigit.msbValue_reverse
    (remainder input divisor)
  rw [← h1, ← h2]
  simpa [normalizedRemainder, trimMSB_eq_inherited]
    using BitMachineTrimLeadingZeros.trim_value
      (remainder input divisor).reverse

theorem normalizedRemainder_length_le_divisor (input divisor : List Bool)
    (hd : 0 < EncodedCommunication.bitsValue divisor) :
    (normalizedRemainder input divisor).length ≤ divisor.length := by
  have hrem := (BitMachineBinaryDivision.standard_division_spec input divisor hd).2
  have hmod : BitMachineBinaryDivision.msbValue input %
      EncodedCommunication.bitsValue divisor <
      EncodedCommunication.bitsValue divisor := Nat.mod_lt _ hd
  have hpow := BitMachineBinarySubtract.bitsValue_lt_pow divisor
  have hvalue : BitMachineBinaryDivision.msbValue
      (remainder input divisor).reverse < 2 ^ divisor.length := by
    rw [PrimeSamplerBinaryDigit.msbValue_reverse]
    have hrem' : EncodedCommunication.bitsValue (remainder input divisor) =
        BitMachineBinaryDivision.msbValue input %
          EncodedCommunication.bitsValue divisor := by
      simpa [remainder] using hrem
    rw [hrem']
    omega
  have hlen := BitMachineTrimLeadingZeros.trim_length_le_of_value_lt_pow
    (remainder input divisor).reverse divisor.length hvalue
  simpa [normalizedRemainder, trimMSB_eq_inherited] using hlen

def cycleTimeBound (input divisor : List Bool) : Nat :=
  BitMachineBinaryDivision.totalTime input divisor [] +
    5 * (remainder input divisor).length +
    (quotient input divisor).length + divisor.length + 7

theorem cycle_nonzero (input divisor : List Bool)
    (hn : (remainder input divisor).any id = true) :
    ∃ t ≤ cycleTimeBound input divisor,
      run t (cfg (some (.divide .outer)) initial input divisor [] [] [] [] []) =
        cfg (some (.divide .outer)) initial divisor.reverse
          (normalizedRemainder input divisor) [] [] [] [] [] := by
  obtain ⟨t, ht, hdiv⟩ := division_run input divisor
  have hs := scan_remainder initial [] divisor
    (remainder input divisor) (quotient input divisor) [] []
  simp only [initial, Bool.false_or, hn, ite_true] at hs
  obtain ⟨tp, htp, hp⟩ := prepare_next
    ⟨BitMachineBinaryDivision.initial, true, none⟩
    divisor (remainder input divisor) (quotient input divisor)
  have h01 := (run_add hdiv _).trans hs
  have h02 := (run_add h01 tp).trans hp
  refine ⟨t + (2 * (remainder input divisor).length + 2) + tp, ?_, ?_⟩
  · unfold cycleTimeBound
    have htrim := trimTime_le (remainder input divisor).reverse
    simp only [List.length_reverse] at htrim
    omega
  · simpa [remainder, quotient, normalizedRemainder] using h02

theorem cycle_zero (input divisor : List Bool)
    (hz : (remainder input divisor).any id = false) :
    ∃ t ≤ BitMachineBinaryDivision.totalTime input divisor [] +
        2 * (remainder input divisor).length + 2,
      run t (cfg (some (.divide .outer)) initial input divisor [] [] [] [] []) =
        cfg none ⟨BitMachineBinaryDivision.initial, false, none⟩ [] divisor
          (remainder input divisor) (quotient input divisor) [] [] [] := by
  obtain ⟨t, ht, hdiv⟩ := division_run input divisor
  have hs := scan_remainder initial [] divisor
    (remainder input divisor) (quotient input divisor) [] []
  simp only [initial, Bool.false_or, hz, ite_false] at hs
  refine ⟨t + (2 * (remainder input divisor).length + 2), by omega, ?_⟩
  simpa [remainder, quotient, initial] using (run_add hdiv _).trans hs

theorem remainder_value (input divisor : List Bool)
    (hd : 0 < EncodedCommunication.bitsValue divisor) :
    EncodedCommunication.bitsValue (remainder input divisor) =
      BitMachineBinaryDivision.msbValue input %
        EncodedCommunication.bitsValue divisor :=
  (BitMachineBinaryDivision.standard_division_spec input divisor hd).2

theorem cycle_gcd_value (input divisor : List Bool)
    (hd : 0 < EncodedCommunication.bitsValue divisor) :
    Nat.gcd (BitMachineBinaryDivision.msbValue input)
        (EncodedCommunication.bitsValue divisor) =
      Nat.gcd (EncodedCommunication.bitsValue divisor)
        (EncodedCommunication.bitsValue (remainder input divisor)) := by
  rw [remainder_value input divisor hd]
  calc
    Nat.gcd (BitMachineBinaryDivision.msbValue input)
        (EncodedCommunication.bitsValue divisor) =
      Nat.gcd (EncodedCommunication.bitsValue divisor)
        (BitMachineBinaryDivision.msbValue input) := Nat.gcd_comm _ _
    _ = Nat.gcd (BitMachineBinaryDivision.msbValue input %
        EncodedCommunication.bitsValue divisor)
        (EncodedCommunication.bitsValue divisor) := Nat.gcd_rec _ _
    _ = Nat.gcd (EncodedCommunication.bitsValue divisor)
        (BitMachineBinaryDivision.msbValue input %
          EncodedCommunication.bitsValue divisor) := Nat.gcd_comm _ _

/-- For every positive divisor, the *same fixed program* eventually halts
with the numerical gcd in bank 1.  This theorem does not yet assert a
polynomial clock; its induction uses the strict Euclidean remainder. -/
theorem euclid_terminates (input divisor : List Bool)
    (hd : 0 < EncodedCommunication.bitsValue divisor) :
    ∃ (t : Nat) (c : Config),
      run t (cfg (some (.divide .outer)) initial input divisor [] [] [] [] []) = c ∧
      c.l = none ∧
      EncodedCommunication.bitsValue (c.stk 1) =
        Nat.gcd (BitMachineBinaryDivision.msbValue input)
          (EncodedCommunication.bitsValue divisor) := by
  have main : ∀ N : Nat, ∀ (a b : List Bool),
      EncodedCommunication.bitsValue b = N → 0 < N →
      ∃ (t : Nat) (c : Config),
        run t (cfg (some (.divide .outer)) initial a b [] [] [] [] []) = c ∧
        c.l = none ∧
        EncodedCommunication.bitsValue (c.stk 1) =
          Nat.gcd (BitMachineBinaryDivision.msbValue a)
            (EncodedCommunication.bitsValue b) := by
    intro N
    induction N using Nat.strong_induction_on with
    | h N ih =>
        intro a b hN hpos
        have hb : 0 < EncodedCommunication.bitsValue b := by omega
        by_cases hz : (remainder a b).any id = false
        · obtain ⟨t, ht, hr⟩ := cycle_zero a b hz
          let c : Config := cfg none ⟨BitMachineBinaryDivision.initial, false, none⟩
            [] b (remainder a b) (quotient a b) [] [] []
          refine ⟨t, c, hr, rfl, ?_⟩
          have hzero : EncodedCommunication.bitsValue (remainder a b) = 0 := by
            have hiff := any_iff_value_ne_zero (remainder a b)
            rw [hz] at hiff
            by_contra hn
            simp [hn] at hiff
          have hg := cycle_gcd_value a b hb
          rw [hzero] at hg
          simp at hg
          simpa [c, cfg, bank, BitMachineBinaryDivision.bank] using hg.symm
        · have hn : (remainder a b).any id = true := by
            cases h : (remainder a b).any id <;> simp_all
          obtain ⟨t₁, ht₁, hfirst⟩ := cycle_nonzero a b hn
          have hvalue := normalizedRemainder_value a b
          have hrem : EncodedCommunication.bitsValue
              (normalizedRemainder a b) < N := by
            rw [hvalue, remainder_value a b hb, ← hN]
            exact Nat.mod_lt _ hb
          have hpositive : 0 < EncodedCommunication.bitsValue
              (normalizedRemainder a b) := by
            rw [hvalue]
            have hiff := any_iff_value_ne_zero (remainder a b)
            rw [hn] at hiff
            by_contra hzero
            have heq : EncodedCommunication.bitsValue (remainder a b) = 0 := by omega
            simp [heq] at hiff
          obtain ⟨t₂, c, hsecond, hc, hcg⟩ := ih
            (EncodedCommunication.bitsValue (normalizedRemainder a b)) hrem
            b.reverse (normalizedRemainder a b) rfl hpositive
          have htwo := (run_add hfirst t₂).trans hsecond
          refine ⟨t₁ + t₂, c, htwo, hc, ?_⟩
          have hrev := PrimeSamplerBinaryDigit.msbValue_reverse b
          have hg := cycle_gcd_value a b hb
          rw [hrev, hvalue] at hcg
          exact hcg.trans hg.symm
  exact main (EncodedCommunication.bitsValue divisor) input divisor rfl hd

end CurrentAdditive.BinaryGCDCore
