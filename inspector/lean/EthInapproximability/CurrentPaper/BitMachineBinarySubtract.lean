import EthInapproximability.CurrentPaper.BitMachineEncoding
import EthInapproximability.CurrentPaper.EncodedCommunication
import Mathlib.Tactic

/-!
# Fixed-width binary subtraction on Boolean stacks

Source: frozen v8 `B-effectivity-details.tex`, the binary arithmetic needed by
`lem:paper-explicit-balanced-family`. Both operands are LSB-first, of equal
physical length, and occupy separate Boolean stacks. The program has two
labels, four finite control bits/options, and three fixed Boolean banks. The
borrow is an actual finite control bit, not a natural-number register.

This is a raw-bank subroutine. It does not yet implement division or the
balanced-family random-access algorithm.
-/

namespace EthInapproximability.CurrentPaper.BitMachineBinarySubtract

open Turing Turing.TM2.Stmt BitMachineEncoding

def outBit (a b borrow : Bool) : Bool := xor (xor a b) borrow

def nextBorrow (a b borrow : Bool) : Bool :=
  (!a && (b || borrow)) || (b && borrow)

theorem bit_identity (a b borrow : Bool) :
    a.toNat + 2 * (nextBorrow a b borrow).toNat =
      b.toNat + borrow.toNat + (outBit a b borrow).toNat := by
  cases a <;> cases b <;> cases borrow <;> decide

def subtractPairs : List (Bool × Bool) → Bool → List Bool × Bool
  | [], borrow => ([], borrow)
  | (a, b) :: rest, borrow =>
      let r := subtractPairs rest (nextBorrow a b borrow)
      (outBit a b borrow :: r.1, r.2)

theorem subtractPairs_length (q : List (Bool × Bool)) (borrow : Bool) :
    (subtractPairs q borrow).1.length = q.length := by
  induction q generalizing borrow with
  | nil => rfl
  | cons p q ih => rcases p with ⟨a, b⟩; simp [subtractPairs, ih]

theorem bitsValue_lt_pow (q : List Bool) :
    EncodedCommunication.bitsValue q < 2 ^ q.length := by
  induction q with
  | nil => simp [EncodedCommunication.bitsValue]
  | cons b q ih =>
      cases b <;>
        simp only [EncodedCommunication.bitsValue, Nat.bit_val, List.length_cons,
          pow_succ, Bool.toNat_false, Bool.toNat_true] <;> omega

theorem subtractPairs_value (q : List (Bool × Bool)) (borrow : Bool) :
    EncodedCommunication.bitsValue (q.map Prod.fst) +
        2 ^ q.length * (subtractPairs q borrow).2.toNat =
      EncodedCommunication.bitsValue (q.map Prod.snd) +
        EncodedCommunication.bitsValue (subtractPairs q borrow).1 + borrow.toNat := by
  induction q generalizing borrow with
  | nil => cases borrow <;> simp [subtractPairs, EncodedCommunication.bitsValue]
  | cons p q ih =>
      rcases p with ⟨a, b⟩
      have h := ih (nextBorrow a b borrow)
      have hb := bit_identity a b borrow
      simp only [subtractPairs, List.map_cons, List.length_cons,
        EncodedCommunication.bitsValue, Nat.bit_val, pow_succ]
      have hfactor : 2 ^ q.length * 2 *
          (subtractPairs q (nextBorrow a b borrow)).2.toNat =
          2 * (2 ^ q.length *
            (subtractPairs q (nextBorrow a b borrow)).2.toNat) := by ring
      omega

/-- For the equal-width operands actually scanned by the machine, the borrow
bit is the exact unsigned comparison and the output is truncated subtraction.
The relation holds with arbitrary leading zero padding. -/
theorem subtractPairs_spec (q : List (Bool × Bool)) :
    (subtractPairs q false).2 =
        decide (EncodedCommunication.bitsValue (q.map Prod.fst) <
          EncodedCommunication.bitsValue (q.map Prod.snd)) ∧
    EncodedCommunication.bitsValue (subtractPairs q false).1 =
      (EncodedCommunication.bitsValue (q.map Prod.fst) +
        2 ^ q.length * (subtractPairs q false).2.toNat) -
        EncodedCommunication.bitsValue (q.map Prod.snd) := by
  have hv := subtractPairs_value q false
  have hl := subtractPairs_length q false
  have hd := bitsValue_lt_pow (subtractPairs q false).1
  rw [hl] at hd
  constructor
  · cases hb : (subtractPairs q false).2 <;>
      simp only [hb, Bool.toNat_false, Bool.toNat_true, Nat.mul_zero, Nat.mul_one,
        Nat.add_zero] at hv ⊢
    · have hnot : ¬ EncodedCommunication.bitsValue (q.map Prod.fst) <
          EncodedCommunication.bitsValue (q.map Prod.snd) := by omega
      simp [hnot]
    · have hlt : EncodedCommunication.bitsValue (q.map Prod.fst) <
          EncodedCommunication.bitsValue (q.map Prod.snd) := by omega
      simp [hlt]
  · simp only [Bool.toNat_false, Nat.add_zero] at hv
    omega

inductive Label where
  | scan | restore
  deriving DecidableEq, Fintype

structure Control where
  borrow : Bool
  a : Option Bool
  b : Option Bool
  deriving DecidableEq, Fintype

def initial : Control := ⟨false, none, none⟩

def program : Label → TM2.Stmt (fun _ : Fin 3 => Bool) Label Control
  | .scan =>
      pop 0 (fun s a => ⟨s.borrow, a, none⟩)
        (pop 1 (fun s b => ⟨s.borrow, s.a, b⟩)
          (branch (fun s => s.a.isSome)
            (push 2 (fun s => outBit (s.a.getD false) (s.b.getD false) s.borrow)
              (load (fun s => ⟨nextBorrow (s.a.getD false) (s.b.getD false)
                  s.borrow, none, none⟩)
                (goto (fun _ => .scan))))
            (goto (fun _ => .restore))))
  | .restore =>
      pop 2 (fun s a => ⟨s.borrow, a, none⟩)
        (branch (fun s => s.a.isSome)
          (push 0 (fun s => s.a.getD false) (goto (fun _ => .restore)))
          (push 1 (fun s => s.borrow) (load (fun _ => initial) halt)))

def bank (a b saved : List Bool) : Fin 3 → List Bool :=
  fun k => if k = 0 then a else if k = 1 then b else saved

def cfg (label : Option Label) (state : Control) (a b saved : List Bool) :
    TM2.Cfg (fun _ : Fin 3 => Bool) Label Control :=
  ⟨label, state, bank a b saved⟩

def run (t : ℕ) (c : TM2.Cfg (fun _ : Fin 3 => Bool) Label Control) :=
  ((advance program)^[t]) c

private theorem run_step {c d : TM2.Cfg (fun _ : Fin 3 => Bool) Label Control}
    (h : TM2.step program c = some d) (t : ℕ) : run (t + 1) c = run t d := by
  simp only [run, Function.iterate_succ_apply, advance, h, Option.getD_some]

private theorem run_add {c d : TM2.Cfg (fun _ : Fin 3 => Bool) Label Control}
    {t : ℕ} (h : run t c = d) (u : ℕ) : run (t + u) c = run u d := by
  rw [Nat.add_comm t u]
  simp only [run, Function.iterate_add_apply] at h ⊢
  rw [h]

private theorem scan_cons (s : Control) (a b : Bool) (as bs saved : List Bool) :
    TM2.step program (cfg (some .scan) s (a :: as) (b :: bs) saved) =
      some (cfg (some .scan) ⟨nextBorrow a b s.borrow, none, none⟩ as bs
        (outBit a b s.borrow :: saved)) := by
  simp [TM2.step, TM2.stepAux, program, cfg, bank]
  funext k
  fin_cases k <;> simp [bank]

private theorem scan_nil (s : Control) (saved : List Bool) :
    TM2.step program (cfg (some .scan) s [] [] saved) =
      some (cfg (some .restore) ⟨s.borrow, none, none⟩ [] [] saved) := by
  simp [TM2.step, TM2.stepAux, program, cfg, bank]
  funext k
  fin_cases k <;> simp [bank]

private theorem restore_cons (s : Control) (a b : List Bool) (x : Bool)
    (saved : List Bool) :
    TM2.step program (cfg (some .restore) s a b (x :: saved)) =
      some (cfg (some .restore) ⟨s.borrow, some x, none⟩ (x :: a) b saved) := by
  simp [TM2.step, TM2.stepAux, program, cfg, bank]
  funext k
  fin_cases k <;> simp [bank]

private theorem restore_nil (s : Control) (a b : List Bool) :
    TM2.step program (cfg (some .restore) s a b []) =
      some (cfg none initial a (s.borrow :: b) []) := by
  simp [TM2.step, TM2.stepAux, program, cfg, bank]
  funext k
  fin_cases k <;> simp [bank]

theorem restore_correct (s : Control) (a b saved : List Bool) :
    run (saved.length + 1) (cfg (some .restore) s a b saved) =
      cfg none initial (saved.reverse ++ a) (s.borrow :: b) [] := by
  induction saved generalizing s a with
  | nil => simpa using run_step (restore_nil s a b) 0
  | cons x saved ih =>
      rw [List.length_cons, run_step (restore_cons s a b x saved)]
      simpa [List.reverse_cons, List.append_assoc] using
        ih ⟨s.borrow, some x, none⟩ (x :: a)

theorem scan_correct (q : List (Bool × Bool)) (s : Control) (saved : List Bool) :
    run (2 * q.length + saved.length + 2)
      (cfg (some .scan) s (q.map Prod.fst) (q.map Prod.snd) saved) =
      cfg none initial (saved.reverse ++ (subtractPairs q s.borrow).1)
        [(subtractPairs q s.borrow).2] [] := by
  induction q generalizing s saved with
  | nil =>
      have h := run_step (scan_nil s saved) (saved.length + 1)
      simpa [subtractPairs] using h.trans
        (restore_correct ⟨s.borrow, none, none⟩ [] [] saved)
  | cons p q ih =>
      rcases p with ⟨a, b⟩
      have h := run_step (scan_cons s a b (q.map Prod.fst) (q.map Prod.snd) saved)
        (2 * q.length + (outBit a b s.borrow :: saved).length + 2)
      rw [show 2 * ((a, b) :: q).length + saved.length + 2 =
          (2 * q.length + (outBit a b s.borrow :: saved).length + 2) + 1 by simp; omega]
      simpa [subtractPairs, List.reverse_cons, List.append_assoc] using
        h.trans (ih ⟨nextBorrow a b s.borrow, none, none⟩
          (outBit a b s.borrow :: saved))

/-- Exact raw-bank execution for any equal-width operand pair. The third bank
is cleared; the second bank contains the one-bit final borrow. -/
theorem run_correct (q : List (Bool × Bool)) :
    run (2 * q.length + 2)
      (cfg (some .scan) initial (q.map Prod.fst) (q.map Prod.snd) []) =
      cfg none initial (subtractPairs q false).1
        [(subtractPairs q false).2] [] := by
  simpa using scan_correct q initial []

theorem run_time_linear (q : List (Bool × Bool)) :
    2 * q.length + 2 ≤ 2 * ((q.map Prod.fst).length + (q.map Prod.snd).length + 1) := by
  simp; omega

end EthInapproximability.CurrentPaper.BitMachineBinarySubtract
