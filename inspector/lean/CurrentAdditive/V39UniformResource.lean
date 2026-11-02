import CurrentAdditive.DeterministicIteration

/-!
Source: selected v39 `sections/deterministic.tex`, `det:reduction`, the
uniform resource calculation following the displayed polynomial recurrence.

This file discharges the numerical absorption which the existing
`ResourceContract` leaves as a premise. It starts with one fixed coefficient
and degree for the complete seed/round encodings and actual charged round
clocks, and computes one power-of-two amplification constant. It does not
provide a constructor, a physical printer, or either promise implication.
-/

namespace CurrentAdditive.V39UniformResource

open CurrentAdditive.DeterministicIteration

universe u v

/-- Fixed per-round coefficients produce a fixed positive binary exponent. -/
def amplificationLog (c d : ℕ) : ℕ := c+d+2

/-- The amplification constant is a power of two, as required by `det:eth`. -/
def amplification (c d : ℕ) : ℕ := 2 ^ amplificationLog c d

/-- A coarse effective exponent for the complete seed encoding. -/
def seedExponent (c d : ℕ) : ℕ := c+d+3

theorem self_le_two_pow (n : ℕ) : n ≤ 2^n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    have hp : 1 ≤ 2^n := Nat.one_le_two_pow
    rw [pow_succ]
    omega

theorem amplificationLog_positive (c d : ℕ) : 1 ≤ amplificationLog c d := by
  simp only [amplificationLog]
  omega

theorem amplification_ge_two (c d : ℕ) : 2 ≤ amplification c d := by
  have hh := Nat.pow_le_pow_right (by decide : 0 < (2:ℕ))
    (amplificationLog_positive c d)
  simpa only [pow_one, amplification] using hh

/-- A fixed coefficient and a fixed degree are absorbed uniformly at every
integer input at least two. No eventual input cutoff is used here. -/
theorem polynomial_plus_linear_le_power (c d x : ℕ) (hx : 2 ≤ x) :
    x + c*x^d ≤ x^(amplification c d) := by
  have hx1 : 1 ≤ x := by omega
  have hcoef : c+1 ≤ x^(c+1) :=
    (self_le_two_pow (c+1)).trans (Nat.pow_le_pow_left hx (c+1))
  have hxd : x^d ≤ x^(d+1) := Nat.pow_le_pow_right hx1 (by omega)
  have hxpow : x ≤ x^(d+1) := Nat.le_self_pow (by omega) x
  have hpoly : x+c*x^d ≤ (c+1)*x^(d+1) := by
    have hh := Nat.mul_le_mul_left c hxd
    nlinarith
  calc
    x+c*x^d ≤ (c+1)*x^(d+1) := hpoly
    _ ≤ x^(c+1)*x^(d+1) := Nat.mul_le_mul_right _ hcoef
    _ = x^(c+d+2) := by rw [← pow_add]; congr 1; omega
    _ ≤ x^(amplification c d) := by
      apply Nat.pow_le_pow_right hx1
      exact self_le_two_pow (c+d+2)

/-- The complete seed envelope `N+S₀+2` has an explicit polynomial bound,
including coefficient zero and degree zero. -/
theorem seed_envelope_le_power (c d N S : ℕ) (hN : 2 ≤ N)
    (hS : S ≤ c*N^d) :
    N+S+2 ≤ N^(seedExponent c d) := by
  have hN1 : 1 ≤ N := by omega
  have hcoef : c+2 ≤ N^(c+2) :=
    (self_le_two_pow (c+2)).trans (Nat.pow_le_pow_left hN (c+2))
  have hNd : N^d ≤ N^(d+1) := Nat.pow_le_pow_right hN1 (by omega)
  have hNpow : N ≤ N^(d+1) := Nat.le_self_pow (by omega) N
  have hsmall : N+S+2 ≤ (c+2)*N^(d+1) := by
    have hh := Nat.mul_le_mul_left c hNd
    nlinarith
  calc
    N+S+2 ≤ (c+2)*N^(d+1) := hsmall
    _ ≤ N^(c+2)*N^(d+1) := Nat.mul_le_mul_right _ hcoef
    _ = N^(seedExponent c d) := by
      rw [← pow_add]
      congr 1
      simp [seedExponent]
      omega

/-- Construct the previously assumed absorbed resource record directly from
fixed polynomial bounds on the actual complete encodings and round clocks.
The coefficient and degree are quantified before the input and round number.
There is no promise, NO hypothesis, or resource conclusion in the premises. -/
theorem resourceContract_of_fixed_polynomial
    {Graph : Type u} {State : Type v}
    (C : Construction Graph State) (G : Graph) (N c d : ℕ)
    (hN : 2 ≤ N)
    (hseed : C.size (C.seed G) ≤ c*N^d)
    (hsize : ∀ R, C.valid G R →
      C.size (C.step G R) ≤ c*(envelope C N R)^d)
    (hclock : ∀ R, C.valid G R →
      C.stepTime R ≤ c*(envelope C N R)^d) :
    ResourceContract C G N (amplification c d) (seedExponent c d) := by
  constructor
  · exact seed_envelope_le_power c d N _ hN hseed
  · intro R hR
    have hx : 2 ≤ envelope C N R := by simp only [envelope]; omega
    have hNenv : N+2 ≤ envelope C N R := by simp only [envelope]; omega
    have hS := hsize R hR
    have hh := polynomial_plus_linear_le_power c d (envelope C N R) hx
    change N+C.size (C.step G R)+2 ≤ (envelope C N R)^(amplification c d)
    calc
      N+C.size (C.step G R)+2 ≤ envelope C N R+c*(envelope C N R)^d := by
        omega
      _ ≤ (envelope C N R)^(amplification c d) := hh
  · intro R hR
    have hx : 2 ≤ envelope C N R := by simp only [envelope]; omega
    exact (hclock R hR).trans
      ((Nat.le_add_left _ _).trans
        (polynomial_plus_linear_le_power c d (envelope C N R) hx))

/-- The same effective constants bound every complete encoding and the sum
of the actual charged round clocks, uniformly in the number of rounds. -/
theorem uniform_iteration_resource
    {Graph : Type u} {State : Type v}
    (C : Construction Graph State) (G : Graph) (N c d k : ℕ)
    (hN : 2 ≤ N) (V : ValidContract C G)
    (hseed : C.size (C.seed G) ≤ c*N^d)
    (hsize : ∀ R, C.valid G R →
      C.size (C.step G R) ≤ c*(envelope C N R)^d)
    (hclock : ∀ R, C.valid G R →
      C.stepTime R ≤ c*(envelope C N R)^d) :
    C.size (state C G k) ≤
        N^((seedExponent c d+1)*(amplification c d)^k) ∧
    totalStepTime C G k ≤
        N^((seedExponent c d+1)*(amplification c d)^k) := by
  exact size_and_steps_at_public_exponent C G N (amplification c d)
    (seedExponent c d) (seedExponent c d+1) k hN
    (amplification_ge_two c d) (by omega) V
    (resourceContract_of_fixed_polynomial C G N c d hN hseed hsize hclock)

#print axioms self_le_two_pow
#print axioms amplificationLog_positive
#print axioms amplification_ge_two
#print axioms polynomial_plus_linear_le_power
#print axioms seed_envelope_le_power
#print axioms resourceContract_of_fixed_polynomial
#print axioms uniform_iteration_resource

end CurrentAdditive.V39UniformResource
