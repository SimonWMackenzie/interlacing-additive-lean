import EthInapproximability.CurrentPaper.BitMachineBinaryDivision
import Mathlib.Tactic

/-!
# Physical leading-zero normalization of an MSB-first word

Horner remainders are mathematically less than the prime, but long division
may store leading zero bits. This one-bank finite Boolean controller removes
those bits in at most the input word length plus one transitions. In
particular, an all-zero nonempty word becomes empty.
-/

namespace EthInapproximability.CurrentPaper.BitMachineTrimLeadingZeros

open Turing Turing.TM2.Stmt BitMachineEncoding

inductive Label where
  | scan
  deriving DecidableEq, Fintype

abbrev Control := Option Bool

def program : Label → TM2.Stmt (fun _ : Fin 1 => Bool) Label Control
  | .scan => pop 0 (fun _ b => b)
      (branch (fun b => b.getD false)
        (push 0 (fun _ => true) halt)
        (branch (fun b => b.isSome)
          (goto (fun _ => .scan))
          halt))

def cfg (l : Option Label) (s : Control) (word : List Bool) :
    TM2.Cfg (fun _ : Fin 1 => Bool) Label Control :=
  ⟨l,s,fun _ => word⟩

def run (t : ℕ) (c : TM2.Cfg (fun _ : Fin 1 => Bool) Label Control) :=
  ((advance program)^[t]) c

def trim : List Bool → List Bool
  | [] => []
  | false :: bs => trim bs
  | true :: bs => true :: bs

def trimTime : List Bool → ℕ
  | [] => 1
  | false :: bs => trimTime bs + 1
  | true :: _ => 1

private theorem run_step {c d : TM2.Cfg (fun _ : Fin 1 => Bool) Label Control}
    (h : TM2.step program c = some d) (t : ℕ) : run (t + 1) c = run t d := by
  simp only [run, Function.iterate_succ_apply, advance, h, Option.getD_some]

private theorem step_nil (s : Control) :
    TM2.step program (cfg (some .scan) s []) =
      some (cfg none none []) := by
  simp [TM2.step, TM2.stepAux, program, cfg]

private theorem step_false (s : Control) (bs : List Bool) :
    TM2.step program (cfg (some .scan) s (false :: bs)) =
      some (cfg (some .scan) (some false) bs) := by
  simp [TM2.step, TM2.stepAux, program, cfg]
  funext k
  fin_cases k <;> simp

private theorem step_true (s : Control) (bs : List Bool) :
    TM2.step program (cfg (some .scan) s (true :: bs)) =
      some (cfg none (some true) (true :: bs)) := by
  simp [TM2.step, TM2.stepAux, program, cfg]

theorem run_correct (word : List Bool) (start : Control) :
    ∃ s : Control, run (trimTime word) (cfg (some .scan) start word) =
      cfg none s (trim word) := by
  induction word generalizing start with
  | nil => exact ⟨none, by simpa [trimTime, trim] using run_step (step_nil start) 0⟩
  | cons b bs ih =>
      cases b with
      | false =>
          obtain ⟨s, hs⟩ := ih (some false)
          refine ⟨s, ?_⟩
          rw [trimTime, run_step (step_false start bs)]
          simpa [trim] using hs
      | true =>
          exact ⟨some true, by
            simpa [trimTime, trim] using run_step (step_true start bs) 0⟩

theorem trimTime_le (word : List Bool) : trimTime word ≤ word.length + 1 := by
  induction word with
  | nil => simp [trimTime]
  | cons b bs ih => cases b <;> simp [trimTime] <;> omega

theorem trim_value (word : List Bool) :
    BitMachineBinaryDivision.msbValue (trim word) =
      BitMachineBinaryDivision.msbValue word := by
  induction word with
  | nil => rfl
  | cons b bs ih =>
      cases b with
      | false => simpa [trim, BitMachineBinaryDivision.msbValue] using ih
      | true => rfl

theorem trim_canonical (word : List Bool) :
    trim word = [] ∨ ∃ bs, trim word = true :: bs := by
  induction word with
  | nil => exact Or.inl rfl
  | cons b bs ih => cases b with
      | false => simpa [trim] using ih
      | true => exact Or.inr ⟨bs,rfl⟩

private theorem foldl_bit_start (bits : List Bool) (start : ℕ) :
    bits.foldl (fun n b => Nat.bit b n) start =
      2 ^ bits.length * start + BitMachineBinaryDivision.msbValue bits := by
  induction bits generalizing start with
  | nil => simp [BitMachineBinaryDivision.msbValue]
  | cons b bs ih =>
      have h₁ := ih (Nat.bit b start)
      have h₂ := ih b.toNat
      have hb : Nat.bit b 0 = b.toNat := by cases b <;> rfl
      simp only [List.foldl_cons, List.length_cons,
        BitMachineBinaryDivision.msbValue] at h₁ h₂ ⊢
      rw [h₁, hb, h₂]
      simp only [Nat.bit_val, pow_succ]
      ring

theorem msbValue_true_cons (bs : List Bool) :
    BitMachineBinaryDivision.msbValue (true :: bs) =
      2 ^ bs.length + BitMachineBinaryDivision.msbValue bs := by
  simpa [BitMachineBinaryDivision.msbValue] using foldl_bit_start bs 1

/-- Once leading zeros are physically stripped, a value below `2^P` fits
in at most `P` bits. This is the size invariant needed for iterated Horner. -/
theorem trim_length_le_of_value_lt_pow (word : List Bool) (P : ℕ)
    (hvalue : BitMachineBinaryDivision.msbValue word < 2 ^ P) :
    (trim word).length ≤ P := by
  rcases trim_canonical word with hz | ⟨bs,hb⟩
  · simp [hz]
  · have hlower : 2 ^ bs.length ≤
        BitMachineBinaryDivision.msbValue word := by
      rw [← trim_value word, hb, msbValue_true_cons]
      omega
    have hlen : bs.length < P := by
      by_contra hnot
      have hpow : 2 ^ P ≤ 2 ^ bs.length :=
        pow_le_pow_right₀ (by omega : 1 ≤ (2 : ℕ)) (by omega)
      omega
    simp [hb]
    omega

end EthInapproximability.CurrentPaper.BitMachineTrimLeadingZeros
