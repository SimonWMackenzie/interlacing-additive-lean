import CurrentAdditive.DeterministicEndpointNumeric

/-! A fully finite version of the `2^{o(m)}` estimate in v27 `det:eth`.
For each reciprocal error scale `1/n`, the bound has an explicit threshold.
The theorem concerns the numeric time bound, not an algorithm implementing
the graph source, CodeD, output writer, or estimator. -/

namespace CurrentAdditive.DeterministicEndpointNumeric

/-- At every fixed reciprocal scale, the public output-time power is
subexponential in the source variable count. The bound is deliberately
written with integer powers, avoiding an unproved asymptotic slogan. -/
theorem eth_discrete_subexponential_bound
    (a C₀ b n m : ℕ)
    (ha : 1 ≤ a) (hC₀ : 1 ≤ C₀) (hb : 1 ≤ b) (hn : 1 ≤ n)
    (hm : 2^(max (32*(n*b*C₀)+16) (8*a)) ≤ m) :
    (m^(b*C₀*(2^a)^ethIterations a m))^n ≤ 2^m := by
  let j := Nat.log 2 m
  let k := ethIterations a m
  let M := n*b*C₀
  have hJ : max (32*M+16) (8*a) ≤ j := by
    dsimp [j, M] at *
    exact Nat.le_log_of_pow_le (by decide) hm
  have hMpos : 0 < M := by dsimp [M]; positivity
  have hlin : M*(j+1) ≤ 2^(j/4) :=
    linear_le_pow_quarter M j (by omega) (by omega)
  have hden : 0 < 2*a := by omega
  have hdiv : k*(2*a) ≤ j := by
    dsimp [k, ethIterations, j]
    exact Nat.div_mul_le_self _ _
  have hhalf : a*k ≤ j/2 :=
    (Nat.le_div_iff_mul_le (by omega : 0 < (2:ℕ))).2 (by nlinarith)
  have hA : (2^a)^k ≤ 2^(j/2) := by
    calc
      (2^a)^k = 2^(a*k) := by rw [pow_mul]
      _ ≤ 2^(j/2) := Nat.pow_le_pow_right (by decide) hhalf
  have hjquarters : j/4+j/2 ≤ j := by omega
  have hpow : M*(j+1)*(2^a)^k ≤ m := by
    calc
      M*(j+1)*(2^a)^k ≤ 2^(j/4) * (2^a)^k :=
        Nat.mul_le_mul_right _ hlin
      _ ≤ 2^(j/4) * 2^(j/2) := Nat.mul_le_mul_left _ hA
      _ = 2^(j/4+j/2) := by rw [pow_add]
      _ ≤ 2^j := Nat.pow_le_pow_right (by decide) hjquarters
      _ ≤ m := Nat.pow_log_le_self 2 (by
        have hp : 0 < 2^(max (32*(n*b*C₀)+16) (8*a)) := by positivity
        omega)
  have hmPow : m ≤ 2^(j+1) := by
    have hp : m < 2^(j+1) := by
      simpa only [j, Nat.succ_eq_add_one] using
        (Nat.lt_pow_succ_log_self (by decide : 1 < (2:ℕ)) m)
    omega
  calc
    (m^(b*C₀*(2^a)^k))^n = m^(n*b*C₀*(2^a)^k) := by
      rw [← pow_mul]
      congr 1
      ring
    _ ≤ (2^(j+1))^(n*b*C₀*(2^a)^k) := Nat.pow_le_pow_left hmPow _
    _ = 2^((j+1)*(n*b*C₀*(2^a)^k)) := by
      exact (pow_mul (2:ℕ) (j+1) (n*b*C₀*(2^a)^k)).symm
    _ ≤ 2^m := by
      apply Nat.pow_le_pow_right (by decide)
      dsimp [M] at hpow
      nlinarith [hpow]

/-- Apply the finite subexponential estimate to any actual clock bounded
by the endpoint's public power. -/
theorem eth_clock_discrete_subexponential
    (a C₀ b n m clock : ℕ)
    (ha : 1 ≤ a) (hC₀ : 1 ≤ C₀) (hb : 1 ≤ b) (hn : 1 ≤ n)
    (hclock : clock ≤ m^(b*C₀*(2^a)^ethIterations a m))
    (hm : 2^(max (32*(n*b*C₀)+16) (8*a)) ≤ m) :
    clock^n ≤ 2^m :=
  (Nat.pow_le_pow_left hclock n).trans
    (eth_discrete_subexponential_bound a C₀ b n m ha hC₀ hb hn hm)

#print axioms eth_discrete_subexponential_bound
#print axioms eth_clock_discrete_subexponential

end CurrentAdditive.DeterministicEndpointNumeric
