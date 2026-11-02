import EthInapproximability.CurrentPaper.SamplerMachine

/-!
A literal two-stack TM2 incrementer for a fixed-width binary trial counter.
The low bit is at the head of the first stack. One full cycle scans and
restores the word in exactly `2d+2` transitions. A retained carry bit marks
overflow; in particular, the all-ones word wraps to all zeros.
-/

namespace CurrentAdditive.FieldMachineHelper.TrialCounterMachine

open Turing Turing.TM2.Stmt
open EthInapproximability.CurrentPaper.BitMachineEncoding

inductive Label where
  | scan | restore
  deriving DecidableEq, Fintype

abbrev Control := Bool × Option Bool
abbrev Config := TM2.Cfg (fun _ : Fin 2 => Bool) Label Control

def initial : Control := (true, none)

def program : Label → TM2.Stmt (fun _ : Fin 2 => Bool) Label Control
  | .scan => pop 0 (fun s b => (s.1, b))
      (branch (fun s => s.2.isSome)
        (push 1 (fun s => s.2.getD false ^^ s.1)
          (load (fun s => (s.1 && s.2.getD false, none))
            (goto (fun _ => .scan))))
        (goto (fun _ => .restore)))
  | .restore => pop 1 (fun s b => (s.1, b))
      (branch (fun s => s.2.isSome)
        (push 0 (fun s => s.2.getD false)
          (goto (fun _ => .restore)))
        halt)

def bank (word scratch : List Bool) : Fin 2 → List Bool :=
  fun k => if k = 0 then word else scratch

def cfg (l : Option Label) (s : Control) (word scratch : List Bool) : Config :=
  ⟨l, s, bank word scratch⟩

def run (t : Nat) (q : Config) : Config := ((advance program)^[t]) q

private theorem run_succ {c e : Config} (h : TM2.step program c = some e)
    (t : Nat) : run (t + 1) c = run t e := by
  simp only [run, Function.iterate_succ_apply, advance, h, Option.getD_some]

private theorem run_add (t u : Nat) (q : Config) :
    run (t + u) q = run u (run t q) := by
  rw [Nat.add_comm t u]
  simp only [run, Function.iterate_add_apply]

def incrementAux : Bool → List Bool → Bool × List Bool
  | carry, [] => (carry, [])
  | carry, b :: rest =>
      let (finalCarry, tail) := incrementAux (carry && b) rest
      (finalCarry, (b ^^ carry) :: tail)

private theorem step_scan_bit (carry b : Bool)
    (rest scratch : List Bool) :
    TM2.step program (cfg (some .scan) (carry, none) (b :: rest) scratch) =
      some (cfg (some .scan) (carry && b, none)
        rest ((b ^^ carry) :: scratch)) := by
  simp [TM2.step, TM2.stepAux, program, cfg, bank]
  funext k
  fin_cases k <;> rfl

private theorem step_scan_end (carry : Bool) (scratch : List Bool) :
    TM2.step program (cfg (some .scan) (carry, none) [] scratch) =
      some (cfg (some .restore) (carry, none) [] scratch) := by
  simp [TM2.step, TM2.stepAux, program, cfg, bank]

private theorem step_restore_bit (carry b : Bool)
    (word rest : List Bool) :
    TM2.step program (cfg (some .restore) (carry, none) word (b :: rest)) =
      some (cfg (some .restore) (carry, some b) (b :: word) rest) := by
  simp [TM2.step, TM2.stepAux, program, cfg, bank]
  funext k
  fin_cases k <;> rfl

private theorem step_restore_end (carry : Bool) (word : List Bool) :
    TM2.step program (cfg (some .restore) (carry, none) word []) =
      some (cfg none (carry, none) word []) := by
  simp [TM2.step, TM2.stepAux, program, cfg, bank]

theorem scan_run (carry : Bool) (word scratch : List Bool) :
    run (word.length + 1)
      (cfg (some .scan) (carry, none) word scratch) =
    cfg (some .restore) ((incrementAux carry word).1, none)
      [] ((incrementAux carry word).2.reverse ++ scratch) := by
  induction word generalizing carry scratch with
  | nil =>
      simpa [incrementAux] using run_succ (step_scan_end carry scratch) 0
  | cons b rest ih =>
      rw [List.length_cons, run_succ (step_scan_bit carry b rest scratch)]
      simpa [incrementAux, List.reverse_cons, List.append_assoc] using
        ih (carry && b) ((b ^^ carry) :: scratch)

theorem restore_run (carry : Bool) (word scratch : List Bool) :
    run (scratch.length + 1)
      (cfg (some .restore) (carry, none) word scratch) =
    cfg none (carry, none) (scratch.reverse ++ word) [] := by
  induction scratch generalizing word with
  | nil =>
      simpa using run_succ (step_restore_end carry word) 0
  | cons b rest ih =>
      rw [List.length_cons, run_succ (step_restore_bit carry b word rest)]
      simpa [List.reverse_cons, List.append_assoc] using ih (b :: word)

private theorem length_incrementAux (carry : Bool) (word : List Bool) :
    (incrementAux carry word).2.length = word.length := by
  induction word generalizing carry with
  | nil => simp [incrementAux]
  | cons b rest ih => simp [incrementAux, ih]

theorem run_increment (word : List Bool) :
    run (2 * word.length + 2)
      (cfg (some .scan) initial word []) =
    cfg none ((incrementAux true word).1, none)
      (incrementAux true word).2 [] := by
  have hs := scan_run true word []
  have hr := restore_run (incrementAux true word).1 []
    (incrementAux true word).2.reverse
  have hlen : (incrementAux true word).2.length = word.length :=
    length_incrementAux true word
  have hbudget : 2 * word.length + 2 =
      (word.length + 1) + ((incrementAux true word).2.reverse.length + 1) := by
    simp [hlen]; omega
  rw [hbudget, run_add]
  change run ((incrementAux true word).2.reverse.length + 1)
    (run (word.length + 1) (cfg (some .scan) (true, none) word [])) = _
  rw [hs]
  simpa using hr

/-- Numeric value of a fixed-width word in least-significant-bit-first order. -/
def bitsValue : List Bool → Nat
  | [] => 0
  | b :: rest => (if b then 1 else 0) + 2 * bitsValue rest

theorem bitsValue_lt_pow (word : List Bool) :
    bitsValue word < 2 ^ word.length := by
  induction word with
  | nil => simp [bitsValue]
  | cons b rest ih =>
      cases b <;> simp [bitsValue, pow_succ] <;> omega

theorem incrementAux_value (carry : Bool) (word : List Bool) :
    bitsValue (incrementAux carry word).2 +
      (if (incrementAux carry word).1 then 2 ^ word.length else 0) =
    bitsValue word + (if carry then 1 else 0) := by
  induction word generalizing carry with
  | nil => cases carry <;> simp [incrementAux, bitsValue]
  | cons b rest ih =>
      have h := ih (carry && b)
      cases carry <;> cases b <;>
        simp [incrementAux, bitsValue, pow_succ] at h ⊢ <;>
        split_ifs at h ⊢ <;> omega

theorem incrementAux_value_mod (word : List Bool) :
    bitsValue (incrementAux true word).2 =
      (bitsValue word + 1) % 2 ^ word.length := by
  have h := incrementAux_value true word
  have hbound := bitsValue_lt_pow (incrementAux true word).2
  rw [length_incrementAux] at hbound
  by_cases hc : (incrementAux true word).1 = true
  · simp [hc] at h
    rw [← h]
    simp [Nat.mod_eq_of_lt hbound]
  · have hc' : (incrementAux true word).1 = false := Bool.eq_false_iff.mpr hc
    simp [hc'] at h
    rw [← h]
    exact (Nat.mod_eq_of_lt hbound).symm

def counterWord (d : Nat) : Nat → List Bool
  | 0 => List.replicate d false
  | k + 1 => (incrementAux true (counterWord d k)).2

private theorem bitsValue_replicate_false (d : Nat) :
    bitsValue (List.replicate d false) = 0 := by
  induction d with
  | zero => rfl
  | succ d ih => simp [List.replicate_succ, bitsValue, ih]

theorem counterWord_length (d k : Nat) :
    (counterWord d k).length = d := by
  induction k with
  | zero => simp [counterWord]
  | succ k ih =>
      simp only [counterWord]
      rw [length_incrementAux, ih]

theorem counterWord_value (d k : Nat) :
    bitsValue (counterWord d k) = k % 2 ^ d := by
  induction k with
  | zero => simp [counterWord, bitsValue_replicate_false]
  | succ k ih =>
      simp only [counterWord]
      rw [incrementAux_value_mod, ih, counterWord_length]
      simp [Nat.add_mod]

theorem counterWord_value_lt (d k : Nat) (hk : k < 2 ^ d) :
    bitsValue (counterWord d k) = k := by
  rw [counterWord_value, Nat.mod_eq_of_lt hk]

theorem counterWord_physical_step (d k : Nat) :
    run (2 * d + 2)
      (cfg (some .scan) initial (counterWord d k) []) =
    cfg none ((incrementAux true (counterWord d k)).1, none)
      (counterWord d (k + 1)) [] := by
  simpa [counterWord_length, counterWord] using
    run_increment (counterWord d k)

theorem candidate_values_are_range (d : Nat) :
    ((List.range (2 ^ d)).map
      (fun k => bitsValue (counterWord d k))) =
      List.range (2 ^ d) := by
  calc
    ((List.range (2 ^ d)).map
        (fun k => bitsValue (counterWord d k))) =
        (List.range (2 ^ d)).map id := by
          apply List.map_congr_left
          intro k hk
          exact counterWord_value_lt d k (List.mem_range.mp hk)
    _ = List.range (2 ^ d) := by simp

#print axioms incrementAux_value_mod
#print axioms counterWord_physical_step
#print axioms candidate_values_are_range

#print axioms run_increment

end CurrentAdditive.FieldMachineHelper.TrialCounterMachine
