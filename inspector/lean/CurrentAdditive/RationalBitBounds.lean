import Mathlib

/-!
Exact common-denominator accounting for the sequential construction in
v27 Appendix H, `det:code`.  This file does not claim a clock for the current
Gauss--Jordan implementation: a bound for the particular integer relation it
returns is still needed.  The lemmas below charge every coordinate append and
every support deletion once such a coefficient bound is supplied.
-/

namespace CurrentAdditive.RationalBitBounds

/-- The witness that all current rational weights use one positive common
denominator.  The numerators may be signed during the algebraic calculation;
positivity is recovered from the actual weight update. -/
structure CommonDenominator {κ : Type*} (w : κ → ℚ) where
  denominator : ℕ
  positive : 0 < denominator
  numerator : κ → ℤ
  represents : ∀ i, w i = (numerator i : ℚ) / (denominator : ℚ)

/-- Any common multiple of the canonical rational denominators gives an
integer representation, with no search over rational values. -/
def commonDenominatorOfDvd {κ : Type*} (w : κ → ℚ) (b : ℕ)
    (hb : 0 < b) (hdiv : ∀ i, (w i).den ∣ b) :
    CommonDenominator w :=
  { denominator := b
    positive := hb
    numerator := fun i => (w i).num * ((b / (w i).den : ℕ) : ℤ)
    represents := by
      intro i
      obtain ⟨d, hd⟩ := hdiv i
      subst b
      have hden : (w i).den ≠ 0 := (w i).den_nz
      have hdpos : 0 < d := by
        by_contra h
        have hd0 : d = 0 := by omega
        simp [hd0] at hb
      have hdq : (d : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hdpos)
      simp only [Nat.mul_div_cancel_left d (w i).den_pos]
      calc
        w i = ((w i).num : ℚ) / ((w i).den : ℚ) := (Rat.num_div_den _).symm
        _ = (((w i).num * (d : ℤ) : ℤ) : ℚ) /
            (((w i).den * d : ℕ) : ℚ) := by
          push_cast
          field_simp [hdq] }

/-- The product of the input rationals' denominators is an executable common
denominator. Its bit length is at most the sum of their binary lengths plus
one; the exact sum-of-lengths bound is supplied separately below. -/
def inputLawCommonDenominator {κ : Type*} [Fintype κ] (w : κ → ℚ) :
    CommonDenominator w :=
  commonDenominatorOfDvd w (∏ i : κ, (w i).den)
    (Finset.prod_pos (by intro i hi; exact (w i).den_pos))
    (by intro i; simpa using
      (Finset.dvd_prod_of_mem (fun j : κ => (w j).den) (Finset.mem_univ i)))

theorem finite_product_bits {κ : Type*} (s : Finset κ) (f : κ → ℕ) :
    ∏ i ∈ s, f i ≤ 2 ^ (∑ i ∈ s, Nat.size (f i)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s his ih =>
      simp only [Finset.prod_insert his, Finset.sum_insert his]
      calc
        f i * ∏ j ∈ s, f j ≤
            2 ^ Nat.size (f i) * 2 ^ (∑ j ∈ s, Nat.size (f j)) :=
          Nat.mul_le_mul (le_of_lt (Nat.lt_size_self _)) ih
        _ = 2 ^ (Nat.size (f i) + ∑ j ∈ s, Nat.size (f j)) := by
          rw [pow_add]

/-- The product common denominator has a binary length bounded by the sum
of the canonical denominators' binary lengths. -/
theorem inputLaw_denominator_bits {κ : Type*} [Fintype κ] (w : κ → ℚ) :
    Nat.size (inputLawCommonDenominator w).denominator ≤
      (∑ i : κ, Nat.size (w i).den) + 1 := by
  apply Nat.size_le.mpr
  have h := finite_product_bits Finset.univ (fun i => (w i).den)
  change (∏ i : κ, (w i).den) <
    2 ^ ((∑ i : κ, Nat.size (w i).den) + 1)
  calc
    (∏ i : κ, (w i).den) ≤ 2 ^ (∑ i : κ, Nat.size (w i).den) := by
      simpa using h
    _ < 2 ^ ((∑ i : κ, Nat.size (w i).den) + 1) := by
      rw [pow_succ]
      have hp : 0 < 2 ^ (∑ i : κ, Nat.size (w i).den) := by positivity
      omega

/-- The exact integer numerator after removing support with the minimum ratio
attained at `j`.  The new common denominator is `b * z j`. -/
def removedNumerator {κ : Type*} (N : κ → ℤ) (z : κ → ℤ) (j i : κ) : ℤ :=
  N i * z j - N j * z i

def removeWeight {κ : Type*} (w : κ → ℚ) (z : κ → ℤ) (j i : κ) : ℚ :=
  w i - (w j / (z j : ℚ)) * (z i : ℚ)

theorem removeWeight_represents {κ : Type*} {w : κ → ℚ}
    (enc : CommonDenominator w) (z : κ → ℤ) (j i : κ)
    (hz : 0 < z j) :
    removeWeight w z j i =
      (removedNumerator enc.numerator z j i : ℚ) /
        ((enc.denominator * (z j).toNat : ℕ) : ℚ) := by
  have hb : (enc.denominator : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt enc.positive)
  have hzq : (z j : ℚ) ≠ 0 := by exact_mod_cast (ne_of_gt hz)
  have hnat : ((z j).toNat : ℤ) = z j := Int.toNat_of_nonneg (le_of_lt hz)
  have hzcast : (((z j).toNat : ℕ) : ℚ) = (z j : ℚ) := by exact_mod_cast hnat
  rw [removeWeight, enc.represents i, enc.represents j]
  simp only [removedNumerator, Int.cast_sub, Int.cast_mul, Nat.cast_mul, hzcast]
  field_simp

def removeWeight_commonDenominator {κ : Type*} {w : κ → ℚ}
    (enc : CommonDenominator w) (z : κ → ℤ) (j : κ)
    (hz : 0 < z j) : CommonDenominator (removeWeight w z j) :=
  { denominator := enc.denominator * (z j).toNat
    positive := Nat.mul_pos enc.positive (by omega)
    numerator := removedNumerator enc.numerator z j
    represents := fun i => removeWeight_represents enc z j i hz }

/-- Appending a symbol of probability `u` multiplies the common denominator
by the input law's common denominator. -/
def append_commonDenominator {κ ι : Type*} {w : κ → ℚ} {u : ι → ℚ}
    (ew : CommonDenominator w) (eu : CommonDenominator u) :
    CommonDenominator (fun p : κ × ι => w p.1 * u p.2) :=
  { denominator := ew.denominator * eu.denominator
    positive := Nat.mul_pos ew.positive eu.positive
    numerator := fun p => ew.numerator p.1 * eu.numerator p.2
    represents := by
      intro p
      rw [ew.represents p.1, eu.represents p.2]
      push_cast
      ring }

/-- In a probability law every represented numerator is between zero and the
common denominator, so its signed magnitude requires no extra bit budget. -/
theorem numerator_bounds {κ : Type*} {w : κ → ℚ}
    (enc : CommonDenominator w) (i : κ)
    (h0 : 0 ≤ w i) (h1 : w i ≤ 1) :
    0 ≤ enc.numerator i ∧ enc.numerator i ≤ (enc.denominator : ℤ) := by
  have hb : (0 : ℚ) < enc.denominator := by exact_mod_cast enc.positive
  rw [enc.represents i] at h0 h1
  constructor
  · have h := (le_div_iff₀ hb).mp h0
    simp only [zero_mul] at h
    exact_mod_cast h
  · have h := (div_le_iff₀ hb).mp h1
    simp only [one_mul] at h
    exact_mod_cast h

theorem numerator_bits_le_denominator {κ : Type*} {w : κ → ℚ}
    (enc : CommonDenominator w) (i : κ)
    (h0 : 0 ≤ w i) (h1 : w i ≤ 1) :
    Nat.size (enc.numerator i).natAbs ≤ Nat.size enc.denominator := by
  obtain ⟨hn0, hn1⟩ := numerator_bounds enc i h0 h1
  have hle : (enc.numerator i).natAbs ≤ enc.denominator := by
    have hi : ((enc.numerator i).natAbs : ℤ) ≤ enc.denominator := by
      rw [Int.natAbs_of_nonneg hn0]
      exact hn1
    exact_mod_cast hi
  exact Nat.size_le_size hle

/-- The elementary bit-budget rule for one denominator multiplication. -/
theorem mul_fits_bits {b a B A : ℕ}
    (hb : b ≤ 2 ^ B) (ha : a ≤ 2 ^ A) :
    b * a ≤ 2 ^ (B + A) := by
  calc
    b * a ≤ 2 ^ B * 2 ^ A := Nat.mul_le_mul hb ha
    _ = 2 ^ (B + A) := by rw [pow_add]

theorem size_le_of_pow_bound {b B : ℕ} (hb : b ≤ 2 ^ B) :
    Nat.size b ≤ B + 1 := by
  apply Nat.size_le.mpr
  calc
    b ≤ 2 ^ B := hb
    _ < 2 ^ (B + 1) := by
      rw [pow_succ]
      have hp : 0 < 2 ^ B := by positivity
      omega

/-- A coefficient bounded by `(n+1)^n` needs at most `n*(n+1)+1`
bits.  This intentionally uses a loose elementary bound instead of a
determinant estimate, since the latter is unnecessary for polynomiality. -/
theorem coefficient_pow_bound (n : ℕ) :
    (n + 1) ^ n ≤ 2 ^ (n * (n + 1)) := by
  have hbase : n + 1 ≤ 2 ^ (n + 1) := by
    have h := (n + 1).lt_two_pow_self
    omega
  calc
    (n + 1) ^ n ≤ (2 ^ (n + 1)) ^ n := Nat.pow_le_pow_left hbase n
    _ = 2 ^ (n * (n + 1)) := by
      rw [← pow_mul]
      congr 1
      exact Nat.mul_comm (n + 1) n

theorem coefficient_fits_bits {a n : ℕ}
    (ha : a ≤ (n + 1) ^ n) :
    Nat.size a ≤ n * (n + 1) + 1 :=
  size_le_of_pow_bound (ha.trans (coefficient_pow_bound n))

/-- A sharper coefficient charge uses the actual number of binary digits in
`n+1`; this recovers the manuscript's `O(n log(n+1))` per elimination. -/
theorem coefficient_log_bound (n : ℕ) :
    (n + 1) ^ n ≤ 2 ^ (n * Nat.size (n + 1)) := by
  have hb := le_of_lt (Nat.lt_size_self (n + 1))
  calc
    (n + 1) ^ n ≤ (2 ^ Nat.size (n + 1)) ^ n := Nat.pow_le_pow_left hb n
    _ = 2 ^ (n * Nat.size (n + 1)) := by
      rw [← pow_mul]
      congr 1
      exact Nat.mul_comm _ _

/-- Charge an actual append by its input-law denominator and an actual
support removal by its selected positive integer coefficient. -/
inductive DenominatorEvent where
  | append (lawDenominator : ℕ)
  | remove (selectedCoefficient : ℕ)
  deriving Repr

def DenominatorEvent.factor : DenominatorEvent → ℕ
  | .append d => d
  | .remove a => a

def appendCount : List DenominatorEvent → ℕ
  | [] => 0
  | .append _ :: xs => appendCount xs + 1
  | .remove _ :: xs => appendCount xs

def removalCount : List DenominatorEvent → ℕ
  | [] => 0
  | .append _ :: xs => removalCount xs
  | .remove _ :: xs => removalCount xs + 1

def denominatorAfter (initial : ℕ) (events : List DenominatorEvent) : ℕ :=
  events.foldl (fun b e => b * e.factor) initial

/-- The event order is immaterial to the denominator upper bound, but the
list itself can be the trace of the sequential algorithm. -/
theorem denominatorAfter_bound (initial C A : ℕ)
    (events : List DenominatorEvent)
    (happend : ∀ d, DenominatorEvent.append d ∈ events → d ≤ C)
    (hremove : ∀ a, DenominatorEvent.remove a ∈ events → a ≤ A) :
    denominatorAfter initial events ≤
      initial * C ^ appendCount events * A ^ removalCount events := by
  induction events generalizing initial with
  | nil => simp [denominatorAfter, appendCount, removalCount]
  | cons e es ih =>
      cases e with
      | append d =>
          have hd : d ≤ C := happend d (by simp)
          have htailA : ∀ x, DenominatorEvent.append x ∈ es → x ≤ C := by
            intro x hx
            exact happend x (by simp [hx])
          have htailR : ∀ x, DenominatorEvent.remove x ∈ es → x ≤ A := by
            intro x hx
            exact hremove x (by simp [hx])
          have hi := ih (initial * d) htailA htailR
          simp only [denominatorAfter, List.foldl_cons, appendCount, removalCount]
          calc
            es.foldl (fun b e => b * DenominatorEvent.factor e) (initial * d) ≤
                initial * d * C ^ appendCount es * A ^ removalCount es := hi
            _ ≤ initial * C ^ (appendCount es + 1) * A ^ removalCount es := by
              calc
                initial * d * C ^ appendCount es * A ^ removalCount es =
                    (initial * C ^ appendCount es * A ^ removalCount es) * d := by ring
                _ ≤ (initial * C ^ appendCount es * A ^ removalCount es) * C :=
                  Nat.mul_le_mul_left _ hd
                _ = initial * C ^ (appendCount es + 1) * A ^ removalCount es := by
                  rw [pow_succ]
                  ring
      | remove a =>
          have ha : a ≤ A := hremove a (by simp)
          have htailA : ∀ x, DenominatorEvent.append x ∈ es → x ≤ C := by
            intro x hx
            exact happend x (by simp [hx])
          have htailR : ∀ x, DenominatorEvent.remove x ∈ es → x ≤ A := by
            intro x hx
            exact hremove x (by simp [hx])
          have hi := ih (initial * a) htailA htailR
          simp only [denominatorAfter, List.foldl_cons, appendCount, removalCount]
          calc
            es.foldl (fun b e => b * DenominatorEvent.factor e) (initial * a) ≤
                initial * a * C ^ appendCount es * A ^ removalCount es := hi
            _ ≤ initial * C ^ appendCount es * A ^ (removalCount es + 1) := by
              rw [pow_succ]
              calc
                initial * a * C ^ appendCount es * A ^ removalCount es =
                    (initial * C ^ appendCount es * A ^ removalCount es) * a := by ring
                _ ≤ (initial * C ^ appendCount es * A ^ removalCount es) * A :=
                  Nat.mul_le_mul_left _ ha
                _ = initial * C ^ appendCount es * (A ^ removalCount es * A) := by ring

theorem sequential_fits_bits (q m M B L : ℕ)
    (initial : ℕ) (events : List DenominatorEvent)
    (hinit : initial ≤ 2 ^ B)
    (happends : appendCount events ≤ q)
    (hremovals : removalCount events ≤ q * m * M)
    (happend : ∀ d, DenominatorEvent.append d ∈ events → d ≤ 2 ^ L)
    (hremove : ∀ a, DenominatorEvent.remove a ∈ events → a ≤ (M + 1) ^ M) :
    Nat.size (denominatorAfter initial events) ≤
      B + q * L + (q * m * M) * (M * Nat.size (M + 1)) + 1 := by
  have hevent := denominatorAfter_bound initial (2 ^ L) ((M + 1) ^ M)
    events happend hremove
  have hA := coefficient_log_bound M
  have hpowC : (2 ^ L) ^ appendCount events ≤ (2 ^ L) ^ q :=
    Nat.pow_le_pow_right (by positivity) happends
  have hpowA : ((M + 1) ^ M) ^ removalCount events ≤
      ((M + 1) ^ M) ^ (q * m * M) :=
    Nat.pow_le_pow_right (by positivity) hremovals
  have hbound : denominatorAfter initial events ≤
      2 ^ B * (2 ^ L) ^ q * (2 ^ (M * Nat.size (M + 1))) ^ (q * m * M) := by
    calc
      denominatorAfter initial events ≤
          initial * (2 ^ L) ^ appendCount events * ((M + 1) ^ M) ^ removalCount events :=
        hevent
      _ ≤ 2 ^ B * (2 ^ L) ^ q * ((M + 1) ^ M) ^ (q * m * M) := by
        exact Nat.mul_le_mul (Nat.mul_le_mul hinit hpowC) hpowA
      _ ≤ 2 ^ B * (2 ^ L) ^ q * (2 ^ (M * Nat.size (M + 1))) ^ (q * m * M) := by
        exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hA _)
  apply size_le_of_pow_bound
  calc
    denominatorAfter initial events ≤ _ := hbound
    _ = 2 ^ (B + q * L + (q * m * M) * (M * Nat.size (M + 1))) := by
      simp only [← pow_mul, ← pow_add]
      congr 1
      ring

/-- The implementation may clear every rational denominator rather than
choose one determinant.  This version charges the *actual* positive integer
coefficient with any verified `H`-bit upper bound. -/
theorem sequential_fits_bits_from_coefficient_budget
    (q m M B L H : ℕ)
    (initial : ℕ) (events : List DenominatorEvent)
    (hinit : initial ≤ 2 ^ B)
    (happends : appendCount events ≤ q)
    (hremovals : removalCount events ≤ q * m * M)
    (happend : ∀ d, DenominatorEvent.append d ∈ events → d ≤ 2 ^ L)
    (hremove : ∀ a, DenominatorEvent.remove a ∈ events → a ≤ 2 ^ H) :
    Nat.size (denominatorAfter initial events) ≤
      B + q * L + (q * m * M) * H + 1 := by
  have hevent := denominatorAfter_bound initial (2 ^ L) (2 ^ H)
    events happend hremove
  have hpowC : (2 ^ L) ^ appendCount events ≤ (2 ^ L) ^ q :=
    Nat.pow_le_pow_right (by positivity) happends
  have hpowA : (2 ^ H) ^ removalCount events ≤
      (2 ^ H) ^ (q * m * M) :=
    Nat.pow_le_pow_right (by positivity) hremovals
  apply size_le_of_pow_bound
  calc
    denominatorAfter initial events ≤
        initial * (2 ^ L) ^ appendCount events * (2 ^ H) ^ removalCount events :=
      hevent
    _ ≤ 2 ^ B * (2 ^ L) ^ q * (2 ^ H) ^ (q * m * M) :=
      Nat.mul_le_mul (Nat.mul_le_mul hinit hpowC) hpowA
    _ = 2 ^ (B + q * L + (q * m * M) * H) := by
      simp only [← pow_mul, ← pow_add]
      congr 1
      ring

/-- If each of `t` support removals uses a positive coefficient at most
`A`, the common denominator after those exact updates is at most `b*A^t`.
This is the direct numerical recurrence charged by the manuscript. -/
theorem foldl_denominator_bound (b A : ℕ) (coeffs : List ℕ)
    (hcoeff : ∀ a ∈ coeffs, a ≤ A) :
    coeffs.foldl (· * ·) b ≤ b * A ^ coeffs.length := by
  induction coeffs generalizing b with
  | nil => simp
  | cons a rest ih =>
      simp only [List.foldl_cons, List.length_cons]
      have ha : a ≤ A := hcoeff a (by simp)
      have hrest : ∀ x ∈ rest, x ≤ A := by
        intro x hx
        exact hcoeff x (by simp [hx])
      calc
        rest.foldl (· * ·) (b * a) ≤ (b * a) * A ^ rest.length := ih (b * a) hrest
        _ ≤ (b * A) * A ^ rest.length := by
          apply Nat.mul_le_mul_right
          exact Nat.mul_le_mul_left b ha
        _ = b * A ^ (rest.length + 1) := by rw [pow_succ]; ring

/-- Exact manuscript-scale denominator budget: at most `q` appends by an
input denominator `C`, and at most `q*m*M` support removals with coefficient
at most `(M+1)^M`.  The sequence records the real operation order and may
contain fewer steps. -/
theorem sequential_denominator_bound (q m M C : ℕ)
    (factors : List ℕ)
    (hsteps : factors.length ≤ q + q * m * M)
    (hfactor : ∀ a ∈ factors, a ≤ max C ((M + 1) ^ M)) :
    factors.foldl (· * ·) 1 ≤
      (max C ((M + 1) ^ M)) ^ (q + q * m * M) := by
  have h := foldl_denominator_bound 1 (max C ((M + 1) ^ M)) factors hfactor
  have hpow : (max C ((M + 1) ^ M)) ^ factors.length ≤
      (max C ((M + 1) ^ M)) ^ (q + q * m * M) :=
    Nat.pow_le_pow_right (by have : 0 < (M + 1) ^ M := pow_pos (by omega) _; omega) hsteps
  have h' : factors.foldl (· * ·) 1 ≤
      (max C ((M + 1) ^ M)) ^ factors.length := by
    simpa only [one_mul] using h
  exact h'.trans hpow

end CurrentAdditive.RationalBitBounds
