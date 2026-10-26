import EthInapproximability.CurrentPaper.EncodedCommunication
import EthInapproximability.CurrentPaper.BitMachineEncoding

/-! Exact strict comparison with an arbitrary fixed depth. The bounded
accumulator and bit weight are finite control, both saturated at D. The
input's little-endian binary value is never expanded into unbounded memory. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace CurrentAdditive.GenericFeatureDepthGuard
open Turing EthInapproximability.CurrentPaper BitMachineEncoding EncodedCommunication

def cap (D n : Nat) : Fin (D + 1) := ⟨min D n, by omega⟩
abbrev Control (D : Nat) := Fin (D + 1) × Fin (D + 1) × Option Bool

def next (D : Nat) (v : Control D) : Option Bool → Control D
  | none => (v.1, v.2.1, none)
  | some b => (cap D (v.1.val + if b then v.2.1.val else 0),
      cap D (2 * v.2.1.val), some b)

def program (D : Nat) (_ : Unit) :
    TM2.Stmt (fun _ : Fin 2 => Bool) Unit (Control D) :=
  .pop 0 (next D)
    (.branch (fun v => v.2.2.isSome) (.goto (fun _ => ()))
      (.push 1 (fun v => decide (v.1.val < D)) .halt))

def initial (D : Nat) : Control D := (cap D 0, cap D 1, none)
def machine (D : Nat) : BitMachine.Machine := ofFinite (0 : Fin 2) 1 () (initial D) (program D)
def bank (word out : List Bool) : Fin 2 → List Bool := ![word, out]
def cfg (D : Nat) (a w : Fin (D + 1)) (seen : Option Bool) (word : List Bool) :=
  (⟨some (), (a,w,seen), bank word []⟩ : TM2.Cfg (fun _ : Fin 2 => Bool) Unit (Control D))
def run (D t : Nat) (c : TM2.Cfg (fun _ : Fin 2 => Bool) Unit (Control D)) :=
  ((advance (program D))^[t]) c

theorem capped_expression (D x y z : Nat) :
    min D x + min D y * z < D ↔ x + y * z < D := by
  by_cases hx : x < D
  · rw [Nat.min_eq_right (by omega : x ≤ D)]
    by_cases hy : y < D
    · rw [Nat.min_eq_right (by omega : y ≤ D)]
    · rw [Nat.min_eq_left (by omega : D ≤ y)]
      by_cases hz : z = 0
      · simp [hz]
      · have hDz := Nat.mul_le_mul_left D (show 1 ≤ z by omega)
        have hyz := Nat.mul_le_mul_left y (show 1 ≤ z by omega)
        constructor <;> intro h <;> nlinarith
  · rw [Nat.min_eq_left (by omega : D ≤ x)]
    omega

theorem step_cons (D : Nat) (a w : Fin (D + 1)) (seen : Option Bool)
    (b : Bool) (tail : List Bool) :
    advance (program D) (cfg D a w seen (b :: tail)) =
      cfg D (cap D (a.val + if b then w.val else 0))
        (cap D (2 * w.val)) (some b) tail := by
  simp [advance, program, TM2.step, TM2.stepAux, cfg, bank, next]
  funext k
  fin_cases k <;> rfl

theorem scan_run (D : Nat) (word : List Bool) :
    ∀ (a w : Fin (D + 1)) (seen : Option Bool),
      (run D (word.length + 1) (cfg D a w seen word)).l = none ∧
      (run D (word.length + 1) (cfg D a w seen word)).stk 1 =
        [decide (a.val + w.val * bitsValue word < D)] := by
  induction word with
  | nil =>
      intro a w seen
      simp [run, cfg, program, next, bank, advance, TM2.step, TM2.stepAux, bitsValue]
  | cons b word ih =>
      intro a w seen
      have h := ih (cap D (a.val + if b then w.val else 0)) (cap D (2 * w.val)) (some b)
      have hp :
          (cap D (a.val + if b then w.val else 0)).val +
            (cap D (2 * w.val)).val * bitsValue word < D ↔
          a.val + w.val * bitsValue (b :: word) < D := by
        have hc := capped_expression D (a.val + if b then w.val else 0)
          (2 * w.val) (bitsValue word)
        have he : a.val + (if b then w.val else 0) + (2 * w.val) * bitsValue word =
            a.val + w.val * bitsValue (b :: word) := by
          cases b <;> simp [bitsValue, Nat.bit] <;> ring
        simpa only [cap, he] using hc
      have heq := propext hp
      rw [show (b :: word).length + 1 = (word.length + 1) + 1 by simp,
        run, Function.iterate_succ_apply, step_cons]
      simpa only [run, heq] using h

/-- Exact value comparison for every bitword, including noncanonical words.
The depth is fixed in finite control before the input is supplied. -/
theorem physical_word (D : Nat) (word : List Bool) :
    (machine D).OutputsWithin word [decide (bitsValue word < D)] (word.length + 1) := by
  have h := scan_run D word (cap D 0) (cap D 1) none
  have hp : (cap D 0).val + (cap D 1).val * bitsValue word < D ↔ bitsValue word < D := by
    simpa only [cap, zero_add, one_mul] using capped_expression D 0 1 (bitsValue word)
  have heq := propext hp
  have hi : cfg D (cap D 0) (cap D 1) none word =
      rawInit (0 : Fin 2) () (initial D) word := by
    unfold cfg rawInit initial
    congr 1
    funext k
    fin_cases k <;> rfl
  rw [hi] at h
  apply outputsWithin_of_raw_run (0 : Fin 2) 1 () (initial D) (program D)
    word [decide (bitsValue word < D)] (word.length + 1) (word.length + 1) le_rfl h.1
  simpa only [heq] using h.2

theorem physical_guard (D n : Nat) :
    (machine D).OutputsWithin n.bits [decide (n < D)] (n.bits.length + 1) := by
  simpa only [bitsValue_bits] using physical_word D n.bits

#print axioms physical_guard
#print axioms physical_word
end CurrentAdditive.GenericFeatureDepthGuard
