import CurrentAdditive.DeterministicEndpointETH
import CurrentAdditive.DeterministicEndpointSubexp

/-! The final midpoint test and its polynomial estimator-time arithmetic.
The test assumes the estimate is produced by an actual algorithm; the
physical estimator/machine model is not supplied here. -/

namespace CurrentAdditive.DeterministicEndpointClassifier

open CurrentAdditive.DeterministicEndpointNumeric

/-- Strictly separated integer costs can be decided by a real estimate at
the manuscript's midpoint. The actual estimates need only obey the stated
additive error, independently of how they were computed. -/
theorem midpoint_classifies
    (d B k : ℕ) (z δ : ℝ) (Yes No : Prop)
    (hYes : Yes → d ≤ B) (hNo : No → d = B+k)
    (hgap : 2*δ < (k:ℝ))
    (hestimate : |z-(d:ℝ)| ≤ δ) :
    (Yes → z < (B:ℝ)+(k:ℝ)/2) ∧
    (No → (B:ℝ)+(k:ℝ)/2 < z) := by
  have he := abs_le.mp hestimate
  constructor
  · intro hy
    have hd : (d:ℝ) ≤ B := by exact_mod_cast hYes hy
    nlinarith [he.2]
  · intro hn
    have hd : (d:ℝ) = (B:ℝ)+(k:ℝ) := by exact_mod_cast hNo hn
    nlinarith [he.1]

/-- A fixed polynomial in the generated table length is also bounded by
each desired reciprocal subexponential rate, at an explicit threshold. -/
theorem polynomial_estimator_discrete_subexponential
    (a C₀ b p n m T : ℕ)
    (ha : 1 ≤ a) (hC₀ : 1 ≤ C₀) (hb : 1 ≤ b)
    (hp : 1 ≤ p) (hn : 1 ≤ n)
    (hT : T ≤ m^(b*C₀*(2^a)^ethIterations a m))
    (hm : 2^(max (32*((n*p)*b*C₀)+16) (8*a)) ≤ m) :
    (T^p)^n ≤ 2^m := by
  have hnp : 1 ≤ n*p := by nlinarith
  have hpow := eth_discrete_subexponential_bound a C₀ b (n*p) m
    ha hC₀ hb hnp hm
  calc
    (T^p)^n = T^(n*p) := by rw [← pow_mul]; congr 1; ring
    _ ≤ (m^(b*C₀*(2^a)^ethIterations a m))^(n*p) :=
      Nat.pow_le_pow_left hT _
    _ ≤ 2^m := hpow

#print axioms midpoint_classifies
#print axioms polynomial_estimator_discrete_subexponential

end CurrentAdditive.DeterministicEndpointClassifier
