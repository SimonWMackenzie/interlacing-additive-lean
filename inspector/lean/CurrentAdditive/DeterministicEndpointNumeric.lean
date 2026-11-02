import CurrentAdditive.DeterministicIteration

/-! Integer endpoint arithmetic for v27 `det:reduction` and `det:eth`.
The resource theorem is applied to a real output bound elsewhere; this file
contains no proxy for the physical table or its run time. -/

namespace CurrentAdditive.DeterministicEndpointNumeric

/-- The manuscript chooses a power-of-two amplification constant so its
binary logarithm is the positive integer `a`. -/
def ethIterations (a m : ℕ) : ℕ := Nat.log 2 m / (2*a)

theorem ethIterations_square_bound (a m : ℕ) (ha : 1 ≤ a) (hm : 1 ≤ m) :
    ((2^a)^ethIterations a m)^2 ≤ m := by
  have hden : 0 < 2*a := by omega
  have hdiv : (Nat.log 2 m / (2*a)) * (2*a) ≤ Nat.log 2 m :=
    Nat.div_mul_le_self _ _
  have hexp : 2*(a*ethIterations a m) ≤ Nat.log 2 m := by
    dsimp [ethIterations]
    nlinarith
  calc
    ((2^a)^ethIterations a m)^2 = 2^(2*(a*ethIterations a m)) := by
      rw [← pow_mul, ← pow_mul]
      congr 1
      ring
    _ ≤ 2^(Nat.log 2 m) := Nat.pow_le_pow_right (by decide) hexp
    _ ≤ m := Nat.pow_log_le_self 2 (by omega)

theorem ethIterations_positive (a m : ℕ) (ha : 1 ≤ a)
    (hm : 2^(2*a) ≤ m) : 1 ≤ ethIterations a m := by
  have hden : 0 < 2*a := by omega
  have hlog : 2*a ≤ Nat.log 2 m :=
    Nat.le_log_of_pow_le (by decide) hm
  exact (Nat.le_div_iff_mul_le hden).2 (by simpa [ethIterations] using hlog)

/-- If a table has at most `N^(C₀ A^k)` entries and `A=2^a`, then its
double binary logarithm has the exact finite upper bound used in the ETH
proof. The extra term is only the logarithm of `C₀*clog₂ N`. -/
theorem double_log_output_bound (N C₀ a k T : ℕ)
    (hT : T ≤ N^(C₀*(2^a)^k)) :
    Nat.clog 2 (Nat.clog 2 T) ≤
      a*k + Nat.clog 2 (C₀*Nat.clog 2 N) := by
  have hN : N ≤ 2^(Nat.clog 2 N) := Nat.le_pow_clog (by decide) N
  have hTpow : T ≤ 2^(Nat.clog 2 N * (C₀*(2^a)^k)) := by
    calc
      T ≤ N^(C₀*(2^a)^k) := hT
      _ ≤ (2^(Nat.clog 2 N))^(C₀*(2^a)^k) :=
        Nat.pow_le_pow_left hN _
      _ = 2^(Nat.clog 2 N * (C₀*(2^a)^k)) := by rw [← pow_mul]
  have hclogT : Nat.clog 2 T ≤ Nat.clog 2 N * (C₀*(2^a)^k) :=
    (Nat.clog_le_iff_le_pow (by decide)).2 hTpow
  have hcoeff : C₀*Nat.clog 2 N ≤
      2^(Nat.clog 2 (C₀*Nat.clog 2 N)) :=
    Nat.le_pow_clog (by decide) _
  have hpow : (2^a)^k = 2^(a*k) := by rw [pow_mul]
  have hclogpow : Nat.clog 2 T ≤
      2^(a*k + Nat.clog 2 (C₀*Nat.clog 2 N)) := by
    calc
      Nat.clog 2 T ≤ Nat.clog 2 N * (C₀*(2^a)^k) := hclogT
      _ = (C₀*Nat.clog 2 N) * 2^(a*k) := by rw [hpow]; ring
      _ ≤ 2^(Nat.clog 2 (C₀*Nat.clog 2 N)) * 2^(a*k) :=
        Nat.mul_le_mul_right _ hcoeff
      _ = 2^(a*k + Nat.clog 2 (C₀*Nat.clog 2 N)) := by
        rw [pow_add]
        ring
  exact (Nat.clog_le_iff_le_pow (by decide)).2 hclogpow

/-- With the manuscript's effective positive constant `1/(4a)`, a
single explicit scalar margin suffices to separate the two costs. -/
theorem eth_loglog_gap (N C₀ a k T : ℕ)
    (ha : 1 ≤ a)
    (hT : T ≤ N^(C₀*(2^a)^k))
    (hmargin : Nat.clog 2 (C₀*Nat.clog 2 N) < a*k) :
    2 * (1 / (4*(a:ℝ))) *
      (Nat.clog 2 (Nat.clog 2 T):ℝ) < (k:ℝ) := by
  have hlog := double_log_output_bound N C₀ a k T hT
  have hn : Nat.clog 2 (Nat.clog 2 T) < 2*(a*k) := by omega
  have hnR : (Nat.clog 2 (Nat.clog 2 T):ℝ) <
      2*(a:ℝ)*(k:ℝ) := by
    have hc : (Nat.clog 2 (Nat.clog 2 T):ℝ) <
        ((2*(a*k):ℕ):ℝ) := by exact_mod_cast hn
    convert hc using 1
    push_cast
    ring
  have haR : (0:ℝ) < a := by exact_mod_cast (by omega : 0 < a)
  have hdiv : (Nat.clog 2 (Nat.clog 2 T):ℝ) / (2*(a:ℝ)) <
      (k:ℝ) := by
    apply (div_lt_iff₀ (by positivity : (0:ℝ) < 2*(a:ℝ))).2
    nlinarith [hnR]
  convert hdiv using 1
  field_simp
  ring

private theorem square_le_two_pow (t : ℕ) (ht : 4 ≤ t) :
    t*t ≤ 2^t := by
  induction t, ht using Nat.le_induction with
  | base => norm_num
  | succ t ht ih =>
      have hfour : 4*t ≤ t*t := Nat.mul_le_mul_right t ht
      have hstep : (t+1)*(t+1) ≤ 2*(t*t) := by nlinarith
      calc
        (t+1)*(t+1) ≤ 2*(t*t) := hstep
        _ ≤ 2*2^t := Nat.mul_le_mul_left 2 ih
        _ = 2^(t+1) := by simp [pow_succ, mul_comm]

/-- An explicit power beats a linear term after a computable threshold.
The constants are intentionally generous so the endpoint cutoff is simple. -/
theorem linear_le_pow_quarter (M j : ℕ)
    (hM : 1 ≤ M) (hj : 32*M+16 ≤ j) :
    M*(j+1) ≤ 2^(j/4) := by
  let t := j/4
  have ht : 8*M+4 ≤ t := by
    dsimp [t]
    exact (Nat.le_div_iff_mul_le (by omega : 0 < (4:ℕ))).2 (by nlinarith)
  have hjt : j+1 ≤ 4*(t+1) := by
    dsimp [t]
    omega
  have h4M : 4*M ≤ t := by omega
  have h8M : 8*M ≤ t := by omega
  have hbig : 4*M*(t+1) ≤ t*t := by
    have hh : 8*M*t ≤ t*t := Nat.mul_le_mul_right t h8M
    have hhh : 4*M ≤ 4*M*t := by
      simpa only [mul_one] using Nat.mul_le_mul_left (4*M)
        (by omega : 1 ≤ t)
    nlinarith
  calc
    M*(j+1) ≤ M*(4*(t+1)) := Nat.mul_le_mul_left M hjt
    _ = 4*M*(t+1) := by ring
    _ ≤ t*t := hbig
    _ ≤ 2^t := square_le_two_pow t (by omega)

/-- The local logarithmic correction is less than `a*k` once the input
variable count crosses an explicit threshold. `N≤m^b` is the exact
source-graph polynomial-size input needed by the manuscript's ETH argument. -/
theorem eth_margin_from_polynomial_source
    (a C₀ b m N : ℕ)
    (ha : 1 ≤ a) (hC₀ : 1 ≤ C₀) (hb : 1 ≤ b)
    (hN : N ≤ m^b)
    (hm : 2^(max (32*(C₀*b)+16) (8*a)) ≤ m) :
    Nat.clog 2 (C₀*Nat.clog 2 N) <
      a*ethIterations a m := by
  let j := Nat.log 2 m
  let k := ethIterations a m
  let M := C₀*b
  have hJ : max (32*M+16) (8*a) ≤ j := by
    dsimp [j, M] at *
    exact Nat.le_log_of_pow_le (by decide) hm
  have hmpos : 0 < m := by
    have hp : 0 < 2^(max (32*(C₀*b)+16) (8*a)) := by positivity
    omega
  have hmPow : m < 2^(j+1) := by
    simpa only [j, Nat.succ_eq_add_one] using
      (Nat.lt_pow_succ_log_self (by decide : 1 < (2:ℕ)) m)
  have hNpow : N ≤ 2^((j+1)*b) := by
    calc
      N ≤ m^b := hN
      _ ≤ (2^(j+1))^b := Nat.pow_le_pow_left (by omega : m ≤ 2^(j+1)) _
      _ = 2^((j+1)*b) := by rw [pow_mul]
  have hclogN : Nat.clog 2 N ≤ (j+1)*b :=
    (Nat.clog_le_iff_le_pow (by decide)).2 hNpow
  have hcoeff : C₀*Nat.clog 2 N ≤ M*(j+1) := by
    dsimp [M]
    nlinarith [Nat.mul_le_mul_left C₀ hclogN]
  have hlin : M*(j+1) ≤ 2^(j/4) :=
    linear_le_pow_quarter M j (by dsimp [M]; nlinarith) (by omega)
  have hclogCoeff : Nat.clog 2 (C₀*Nat.clog 2 N) ≤ j/4 :=
    (Nat.clog_le_iff_le_pow (by decide)).2 (hcoeff.trans hlin)
  have hden : 0 < 2*a := by omega
  have hmod : j % (2*a) < 2*a := Nat.mod_lt _ hden
  have hdecomp : j % (2*a) + (2*a)*(j/(2*a)) = j :=
    Nat.mod_add_div j (2*a)
  have hjk : j < 2*a*(k+1) := by
    dsimp [k, ethIterations]
    nlinarith
  have h2a : 2*a ≤ j/4 := by
    have hja : 8*a ≤ j := by omega
    exact (Nat.le_div_iff_mul_le (by omega : 0 < (4:ℕ))).2 (by omega)
  have hjfour : 4*(j/4) ≤ j := by
    simpa only [mul_comm] using Nat.div_mul_le_self j 4
  have hmargin : j/4 < a*k := by nlinarith
  simpa only [k] using lt_of_le_of_lt hclogCoeff hmargin

/-- All finite scalar inequalities used after the actual table writer.
`N≤m^b`, `m≤N`, and the two entry bounds are precisely the external
source-size and output-size facts consumed here. -/
theorem eth_public_numerics
    (a C₀ b m N T : ℕ)
    (ha : 1 ≤ a) (hC₀ : 1 ≤ C₀) (hb : 1 ≤ b)
    (hNlow : m ≤ N) (hNhigh : N ≤ m^b)
    (hTlow : N^2 ≤ T)
    (hThigh : T ≤ N^(C₀*(2^a)^ethIterations a m))
    (hm : 2^(max (32*(C₀*b)+16) (8*a)) ≤ m) :
    let k := ethIterations a m
    1 ≤ k ∧ ((2^a)^k)^2 ≤ m ∧ m^2 ≤ T ∧
    2 * (1 / (4*(a:ℝ))) *
      (Nat.clog 2 (Nat.clog 2 T):ℝ) < (k:ℝ) ∧
    T ≤ m^(b*C₀*(2^a)^k) := by
  let k := ethIterations a m
  have hmpos : 1 ≤ m := by
    have hp : 0 < 2^(max (32*(C₀*b)+16) (8*a)) := by positivity
    omega
  have hlogbound : 2*a ≤ max (32*(C₀*b)+16) (8*a) := by omega
  have hk : 1 ≤ k :=
    ethIterations_positive a m ha
      ((Nat.pow_le_pow_right (by decide) hlogbound).trans hm)
  have hsqrt := ethIterations_square_bound a m ha hmpos
  have hTmin : m^2 ≤ T :=
    (Nat.pow_le_pow_left hNlow 2).trans hTlow
  have hmargin := eth_margin_from_polynomial_source a C₀ b m N
    ha hC₀ hb hNhigh hm
  have hgap := eth_loglog_gap N C₀ a k T ha hThigh hmargin
  have hsize : T ≤ m^(b*C₀*(2^a)^k) := by
    calc
      T ≤ N^(C₀*(2^a)^k) := hThigh
      _ ≤ (m^b)^(C₀*(2^a)^k) := Nat.pow_le_pow_left hNhigh _
      _ = m^(b*C₀*(2^a)^k) := by
        rw [← pow_mul]
        congr 1
        ring
  exact ⟨hk, hsqrt, hTmin, hgap, hsize⟩

#print axioms ethIterations_square_bound
#print axioms double_log_output_bound
#print axioms eth_loglog_gap
#print axioms eth_margin_from_polynomial_source
#print axioms eth_public_numerics

end CurrentAdditive.DeterministicEndpointNumeric
