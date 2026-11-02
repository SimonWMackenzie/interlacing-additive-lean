import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas
import Mathlib.Algebra.Order.Floor.Div

/-!
Executable arithmetic kernel for the v35 Appendix `det:parameters` exceptional-count
test.  This file has no real-valued decision procedure: all operations on the
input are natural-number additions, powers, division and `Nat.nthRoot`.

For `v = 2^(-b)` and positive tolerance `tau = p/q`, the manuscript's
exceptional count is `8*t`, where `t` is the least positive natural satisfying
both inequalities below.  The bridge from this arithmetic characterization
back to `conditioningExceptionCount` is a separate proof obligation.
-/

namespace CurrentAdditive.PublicScheduleIntegerPower

def ceilRootPow (e a : ℕ) : ℕ := Nat.nthRoot e (a - 1) + 1

theorem ceilRootPow_spec (e a t : ℕ) (he : e ≠ 0) (ha : 0 < a) :
    ceilRootPow e a ≤ t ↔ a ≤ t ^ e := by
  unfold ceilRootPow
  rw [Nat.succ_le_iff, Nat.nthRoot_lt_iff he]
  omega

def ceilRootRatio (e a b : ℕ) : ℕ := ceilRootPow e (a ⌈/⌉ b)

theorem ceilRootRatio_spec (e a b t : ℕ) (he : e ≠ 0)
    (ha : 0 < a) (hb : 0 < b) :
    ceilRootRatio e a b ≤ t ↔ a ≤ b * t ^ e := by
  have hceil : 0 < a ⌈/⌉ b := by
    by_contra h
    have hz : a ⌈/⌉ b = 0 := by omega
    have hm : a ≤ b * (a ⌈/⌉ b) := (ceilDiv_le_iff_le_mul hb).1 le_rfl
    simp [hz] at hm
    omega
  rw [ceilRootRatio, ceilRootPow_spec e (a ⌈/⌉ b) t he hceil]
  exact ceilDiv_le_iff_le_mul hb

def firstPowerWitness (b p q : ℕ) : ℕ :=
  max
    (ceilRootRatio 512 (2 ^ (5120 + b) * q ^ 1024) (p ^ 1024))
    (ceilRootPow 512 (2 ^ (35840 + 5 * b)))

theorem firstPowerWitness_spec (b p q t : ℕ) (hp : 0 < p) (hq : 0 < q) :
    firstPowerWitness b p q ≤ t ↔
      2 ^ (5120 + b) * q ^ 1024 ≤ p ^ 1024 * t ^ 512 ∧
      2 ^ (35840 + 5 * b) ≤ t ^ 512 := by
  simp only [firstPowerWitness, max_le_iff]
  rw [ceilRootRatio_spec 512 _ _ t (by omega) (by positivity) (by positivity),
    ceilRootPow_spec 512 _ t (by omega) (by positivity)]

theorem firstPowerWitness_positive (b p q : ℕ) :
    0 < firstPowerWitness b p q := by
  unfold firstPowerWitness ceilRootRatio ceilRootPow
  omega

theorem firstPowerWitness_passes (b p q : ℕ) (hp : 0 < p) (hq : 0 < q) :
    2 ^ (5120 + b) * q ^ 1024 ≤
      p ^ 1024 * (firstPowerWitness b p q) ^ 512 ∧
    2 ^ (35840 + 5 * b) ≤ (firstPowerWitness b p q) ^ 512 :=
  (firstPowerWitness_spec b p q (firstPowerWitness b p q) hp hq).mp le_rfl

theorem firstPowerWitness_le_of_passes (b p q t : ℕ)
    (hp : 0 < p) (hq : 0 < q)
    (h₁ : 2 ^ (5120 + b) * q ^ 1024 ≤ p ^ 1024 * t ^ 512)
    (h₂ : 2 ^ (35840 + 5 * b) ≤ t ^ 512) :
    firstPowerWitness b p q ≤ t :=
  (firstPowerWitness_spec b p q t hp hq).mpr ⟨h₁, h₂⟩

/-- An integer envelope whose binary length is linear in `b` and the binary
length of `q` (all exponents here are fixed constants). This is a value bound,
not a bit-machine runtime proof for `Nat.nthRoot`. -/
theorem firstPowerWitness_envelope (b p q : ℕ) (hp : 0 < p) (hq : 0 < q) :
    firstPowerWitness b p q ≤
      max (2 ^ (5120 + b) * q ^ 1024) (2 ^ (35840 + 5 * b)) := by
  let a := 2 ^ (5120 + b) * q ^ 1024
  let d := 2 ^ (35840 + 5 * b)
  let t := max a d
  have hdpos : 0 < d := by dsimp [d]; positivity
  have ht : 1 ≤ t := by dsimp [t]; omega
  have hpow : t ≤ t ^ 512 := le_self_pow ht (by decide)
  have hp1 : 1 ≤ p ^ 1024 := by have h := pow_pos hp 1024; omega
  have ha : a ≤ t := le_max_left _ _
  have hd : d ≤ t := le_max_right _ _
  exact firstPowerWitness_le_of_passes b p q t hp hq
    (by
      change a ≤ p ^ 1024 * t ^ 512
      have hmul : t ^ 512 ≤ p ^ 1024 * t ^ 512 := by
        simpa only [one_mul] using Nat.mul_le_mul_right (t ^ 512) hp1
      exact ha.trans (hpow.trans hmul))
    (by change d ≤ t ^ 512; exact hd.trans hpow)

/-- Explicit binary-width envelope for the exact count.  If the denominator
has at most `k+1` bits, this witness has at most `B+1` bits, where `B` is
linear in `b` and `k`. -/
theorem firstPowerWitness_bit_envelope (b p q k : ℕ)
    (hp : 0 < p) (hq : 0 < q) (hqk : q ≤ 2 ^ k) :
    firstPowerWitness b p q ≤
      2 ^ max (5120 + b + 1024 * k) (35840 + 5 * b) := by
  have hfirst : 2 ^ (5120 + b) * q ^ 1024 ≤
      2 ^ (5120 + b + 1024 * k) := by
    calc
      2 ^ (5120 + b) * q ^ 1024 ≤
          2 ^ (5120 + b) * (2 ^ k) ^ 1024 := by gcongr
      _ = 2 ^ (5120 + b + 1024 * k) := by
        rw [← pow_mul, ← pow_add]
        congr 1
        omega
  have hsecond : 2 ^ (35840 + 5 * b) ≤
      2 ^ max (5120 + b + 1024 * k) (35840 + 5 * b) :=
    Nat.pow_le_pow_right (by decide) (le_max_right _ _)
  exact (firstPowerWitness_envelope b p q hp hq).trans
    (max_le (hfirst.trans (Nat.pow_le_pow_right (by decide) (le_max_left _ _)))
      hsecond)

#print axioms ceilRootPow_spec
#print axioms ceilRootRatio_spec
#print axioms firstPowerWitness_spec
#print axioms firstPowerWitness_passes
#print axioms firstPowerWitness_envelope
#print axioms firstPowerWitness_bit_envelope

end CurrentAdditive.PublicScheduleIntegerPower
