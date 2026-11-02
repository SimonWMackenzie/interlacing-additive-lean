import CurrentAdditive.RationalCount
import Mathlib.Data.Nat.Log

/-! A bounded binary-search value algorithm for the physical root controller.
It invokes an explicit Boolean power comparison and takes only the bit
length of its upper bound many iterations.  TM2 realization is separate. -/
namespace CurrentAdditive.PublicScheduleBitBisection

open CurrentAdditive.PublicScheduleIntegerPower

def powerTest (b p q t : ℕ) : Bool :=
  decide (2 ^ (5120 + b) * q ^ 1024 ≤ p ^ 1024 * t ^ 512 ∧
    2 ^ (35840 + 5 * b) ≤ t ^ 512)

theorem powerTest_true_iff (b p q t : ℕ) (hp : 0 < p) (hq : 0 < q) :
    powerTest b p q t = true ↔ firstPowerWitness b p q ≤ t := by
  rw [powerTest, decide_eq_true_eq, firstPowerWitness_spec b p q t hp hq]

def bisect (test : ℕ → Bool) : ℕ → ℕ → ℕ → ℕ
  | lo, hi, 0 => lo
  | lo, hi, fuel + 1 =>
      if lo < hi then
        let mid := lo + (hi - lo) / 2
        if test mid then bisect test lo mid fuel
        else bisect test (mid + 1) hi fuel
      else lo

private theorem half_lt_power (d fuel : ℕ)
    (h : d < 2 ^ (fuel + 1)) : d / 2 < 2 ^ fuel := by
  rw [pow_succ] at h
  omega

theorem bisect_exact (test : ℕ → Bool) (w lo hi fuel : ℕ)
    (htest : ∀ t, test t = true ↔ w ≤ t)
    (hlo : lo ≤ w) (hhi : w ≤ hi)
    (hwidth : hi - lo < 2 ^ fuel) :
    bisect test lo hi fuel = w := by
  induction fuel generalizing lo hi with
  | zero =>
      have hw0 : hi - lo = 0 := by omega
      simp only [bisect]
      omega
  | succ fuel ih =>
      by_cases hlt : lo < hi
      · let mid := lo + (hi - lo) / 2
        have hmidlo : lo ≤ mid := by dsimp [mid]; omega
        have hmidhi : mid < hi := by dsimp [mid]; omega
        by_cases hpass : test mid = true
        · have hw : w ≤ mid := (htest mid).mp hpass
          have hwid : mid - lo < 2 ^ fuel := by
            have hd := half_lt_power (hi - lo) fuel hwidth
            dsimp [mid]
            omega
          simp only [bisect, if_pos hlt, mid, hpass]
          exact ih lo mid hlo hw hwid
        · have hw : mid < w := by
            have hf : test mid = false := by cases hh : test mid <;> simp_all
            by_contra hn
            have hm : w ≤ mid := by omega
            have htrue := (htest mid).mpr hm
            simp [hf] at htrue
          have hwid : hi - (mid + 1) < 2 ^ fuel := by
            have hd := half_lt_power (hi - lo) fuel hwidth
            dsimp [mid]
            omega
          have hfalse : test mid = false := by cases hh : test mid <;> simp_all
          simp only [bisect, if_pos hlt, mid, hfalse]
          exact ih (mid + 1) hi (by omega) hhi hwid
      · have heq : lo = hi := by omega
        simp [bisect, hlt]
        omega

/-- Fixed-round form for a physical controller.  It needs no separate
`lo < hi` branch: once the interval collapses, every remaining midpoint
equals its unique element. -/
def bisectFixed (test : ℕ → Bool) : ℕ → ℕ → ℕ → ℕ
  | lo, _, 0 => lo
  | lo, hi, fuel + 1 =>
      let mid := (lo + hi) / 2
      if test mid then bisectFixed test lo mid fuel
      else bisectFixed test (mid + 1) hi fuel

theorem bisectFixed_exact (test : ℕ → Bool) (w lo hi fuel : ℕ)
    (htest : ∀ t, test t = true ↔ w ≤ t)
    (hlo : lo ≤ w) (hhi : w ≤ hi)
    (hwidth : hi - lo < 2 ^ fuel) :
    bisectFixed test lo hi fuel = w := by
  induction fuel generalizing lo hi with
  | zero =>
      simp only [bisectFixed]
      omega
  | succ fuel ih =>
      let mid := (lo + hi) / 2
      have hmidlo : lo ≤ mid := by dsimp [mid]; omega
      have hmidhi : mid ≤ hi := by dsimp [mid]; omega
      by_cases hpass : test mid = true
      · have hw : w ≤ mid := (htest mid).mp hpass
        have hwid : mid - lo < 2 ^ fuel := by
          have hd := half_lt_power (hi - lo) fuel hwidth
          dsimp [mid]
          omega
        simp only [bisectFixed, mid, hpass]
        exact ih lo mid hlo hw hwid
      · have hw : mid < w := by
          have hf : test mid = false := by cases hh : test mid <;> simp_all
          by_contra hn
          have hm : w ≤ mid := by omega
          have htrue := (htest mid).mpr hm
          simp [hf] at htrue
        have hwid : hi - (mid + 1) < 2 ^ fuel := by
          have hd := half_lt_power (hi - lo) fuel hwidth
          dsimp [mid]
          omega
        have hfalse : test mid = false := by cases hh : test mid <;> simp_all
        simp only [bisectFixed, mid, hfalse]
        exact ih (mid + 1) hi (by omega) hhi hwid

def rootUpper (b p q : ℕ) : ℕ :=
  max (2 ^ (5120 + b) * q ^ 1024) (2 ^ (35840 + 5 * b))

def rootFuel (b p q : ℕ) : ℕ := Nat.clog 2 (rootUpper b p q + 1)

def searchedWitness (b p q : ℕ) : ℕ :=
  bisect (powerTest b p q) 0 (rootUpper b p q) (rootFuel b p q)

theorem searchedWitness_eq_firstPowerWitness (b p q : ℕ)
    (hp : 0 < p) (hq : 0 < q) :
    searchedWitness b p q = firstPowerWitness b p q := by
  have hbound := firstPowerWitness_envelope b p q hp hq
  have hwidth : rootUpper b p q - 0 < 2 ^ rootFuel b p q := by
    unfold rootFuel
    have h := Nat.le_pow_clog (by decide : 1 < 2) (rootUpper b p q + 1)
    omega
  exact bisect_exact (powerTest b p q) (firstPowerWitness b p q)
    0 (rootUpper b p q) (rootFuel b p q)
    (fun t => (powerTest_true_iff b p q t hp hq))
    (Nat.zero_le _) hbound hwidth

/-- A machine-friendly bisection variant: the initial high endpoint is a
single dyadic word, whose exponent is linear in the unary `b` and the
denominator's bit count `k`. -/
def dyadicFuelExponent (b k : ℕ) : ℕ :=
  max (5120 + b + 1024 * k) (35840 + 5 * b)

def dyadicSearchedWitness (b p q k : ℕ) : ℕ :=
  bisect (powerTest b p q) 0 (2 ^ dyadicFuelExponent b k)
    (dyadicFuelExponent b k + 1)

theorem dyadicSearchedWitness_eq_firstPowerWitness (b p q k : ℕ)
    (hp : 0 < p) (hq : 0 < q) (hqk : q ≤ 2 ^ k) :
    dyadicSearchedWitness b p q k = firstPowerWitness b p q := by
  have hbound := firstPowerWitness_bit_envelope b p q k hp hq hqk
  have hwidth : 2 ^ dyadicFuelExponent b k - 0 <
      2 ^ (dyadicFuelExponent b k + 1) := by
    simp only [Nat.sub_zero, pow_succ]
    have hpow : 0 < 2 ^ dyadicFuelExponent b k := by positivity
    omega
  exact bisect_exact (powerTest b p q) (firstPowerWitness b p q)
    0 (2 ^ dyadicFuelExponent b k) (dyadicFuelExponent b k + 1)
    (fun t => powerTest_true_iff b p q t hp hq)
    (Nat.zero_le _) hbound hwidth

def dyadicFixedWitness (b p q k : ℕ) : ℕ :=
  bisectFixed (powerTest b p q) 0 (2 ^ dyadicFuelExponent b k)
    (dyadicFuelExponent b k + 1)

theorem dyadicFixedWitness_eq_firstPowerWitness (b p q k : ℕ)
    (hp : 0 < p) (hq : 0 < q) (hqk : q ≤ 2 ^ k) :
    dyadicFixedWitness b p q k = firstPowerWitness b p q := by
  have hbound := firstPowerWitness_bit_envelope b p q k hp hq hqk
  have hwidth : 2 ^ dyadicFuelExponent b k - 0 <
      2 ^ (dyadicFuelExponent b k + 1) := by
    simp only [Nat.sub_zero, pow_succ]
    have hpow : 0 < 2 ^ dyadicFuelExponent b k := by positivity
    omega
  exact bisectFixed_exact (powerTest b p q) (firstPowerWitness b p q)
    0 (2 ^ dyadicFuelExponent b k) (dyadicFuelExponent b k + 1)
    (fun t => powerTest_true_iff b p q t hp hq)
    (Nat.zero_le _) hbound hwidth

def searchedCount (b : ℕ) (τ : ℚ) : ℕ :=
  8 * searchedWitness b τ.num.toNat τ.den

theorem searchedCount_eq_source (b : ℕ) (τ : ℚ) (hτ : 0 < τ) :
    searchedCount b τ =
      CurrentAdditive.conditioningExceptionCount
        ((2 : ℝ) ^ (-(b : ℝ))) (τ : ℝ) := by
  have hpos : 0 < τ.num := Rat.num_pos.mpr hτ
  have hn : (τ.num.toNat : ℤ) = τ.num := Int.toNat_of_nonneg hpos.le
  have hp : 0 < τ.num.toNat := by omega
  have hq : 0 < τ.den := τ.den_pos
  rw [searchedCount, searchedWitness_eq_firstPowerWitness b _ _ hp hq]
  exact CurrentAdditive.PublicScheduleRationalCount.exactCount_eq_source b τ hτ

#print axioms bisect_exact
#print axioms searchedWitness_eq_firstPowerWitness
#print axioms dyadicSearchedWitness_eq_firstPowerWitness
#print axioms dyadicFixedWitness_eq_firstPowerWitness
#print axioms searchedCount_eq_source

end CurrentAdditive.PublicScheduleBitBisection
