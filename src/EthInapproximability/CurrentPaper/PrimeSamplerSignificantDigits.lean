import EthInapproximability.CurrentPaper.PrimeSamplerEntryAlgorithm
import EthInapproximability.CurrentPaper.BitMachineBinarySubtract
import Mathlib.Tactic

/-!
# Significant base-p coefficients

The frozen Appendix B accessor omits leading zero coefficients. For `p ≥ 2`,
this list recurses on the decreasing numerical quotient until zero and is
proved to agree with the fixed-width Horner polynomial whenever `l < p^t`.
Its length is at most the *binary bit length* of `l`. These are semantic and
counting facts, not a physical digit-extraction machine certificate.
-/

namespace EthInapproximability.CurrentPaper.PrimeSamplerSignificantDigits

open PrimeSamplerEntryAlgorithm

def digits (p : ℕ) (hp : 2 ≤ p) : ℕ → List ℕ
  | 0 => []
  | l + 1 => digits p hp ((l + 1) / p) ++ [(l + 1) % p]
termination_by l => l
decreasing_by
  apply Nat.div_lt_self <;> omega

theorem digits_zero (p : ℕ) (hp : 2 ≤ p) : digits p hp 0 = [] := by
  rw [digits]

theorem digits_succ (p l : ℕ) (hp : 2 ≤ p) :
    digits p hp (l + 1) = digits p hp ((l + 1) / p) ++ [(l + 1) % p] := by
  rw [digits]

theorem digits_length_le (p : ℕ) (hp : 2 ≤ p) (n l : ℕ)
    (hl : l < 2 ^ n) : (digits p hp l).length ≤ n := by
  induction n generalizing l with
  | zero =>
      have hzero : l = 0 := by simpa using hl
      subst l
      simp [digits_zero]
  | succ n ih =>
      cases l with
      | zero => simp [digits_zero]
      | succ l =>
          have hq : (l + 1) / p < 2 ^ n := by
            apply (Nat.div_lt_iff_lt_mul (by omega)).2
            rw [pow_succ] at hl
            nlinarith
          have hrec := ih ((l + 1) / p) hq
          rw [digits_succ]
          simp only [List.length_append, List.length_singleton]
          omega

theorem evaluate_digits (p j t l : ℕ) (hp : 2 ≤ p)
    (hl : l < p ^ t) :
    evaluate p j (digits p hp l) 0 = horner p j t l := by
  induction t generalizing l with
  | zero =>
      have hzero : l = 0 := by simpa using hl
      subst l
      simp [digits_zero, evaluate, horner]
  | succ t ih =>
      cases l with
      | zero => simp [digits_zero, evaluate, PrimeSamplerEntryAlgorithm.zero_label]
      | succ l =>
          have hq : (l + 1) / p < p ^ t := by
            apply (Nat.div_lt_iff_lt_mul (by omega)).2
            rw [pow_succ] at hl
            simpa only [Nat.mul_comm] using hl
          rw [digits_succ]
          simp only [evaluate, List.foldl_append, List.foldl_cons, List.foldl_nil]
          change (j * evaluate p j (digits p hp ((l + 1) / p)) 0 +
              (l + 1) % p) % p = horner p j (t + 1) (l + 1)
          rw [ih _ hq, horner]
          rw [Nat.add_comm]

theorem digits_length_le_word (p : ℕ) (hp : 2 ≤ p)
    (labelBits : List Bool) :
    (digits p hp (EncodedCommunication.bitsValue labelBits)).length ≤
      labelBits.length :=
  digits_length_le p hp labelBits.length
    (EncodedCommunication.bitsValue labelBits)
    (BitMachineBinarySubtract.bitsValue_lt_pow labelBits)

theorem evaluate_word_digits (p j t : ℕ) (hp : 2 ≤ p)
    (labelBits : List Bool)
    (hl : EncodedCommunication.bitsValue labelBits < p ^ t) :
    evaluate p j
      (digits p hp (EncodedCommunication.bitsValue labelBits)) 0 =
      horner p j t (EncodedCommunication.bitsValue labelBits) :=
  evaluate_digits p j t _ hp hl

end EthInapproximability.CurrentPaper.PrimeSamplerSignificantDigits
