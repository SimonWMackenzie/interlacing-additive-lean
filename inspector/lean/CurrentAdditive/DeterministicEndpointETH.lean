import CurrentAdditive.DeterministicEndpointAssembly

/-! Finite semantic endpoint of v27 `det:eth`. The same table is used for
YES, NO, power-of-two padding, output length, and the growing error margin.
The constructor clock, graph source reduction, encoded writer and estimator
machine are not supplied by this theorem. -/

namespace CurrentAdditive.DeterministicEndpointETH

open CurrentAdditive.DeterministicIteration
open CurrentAdditive.DeterministicEndpointNumeric
open CurrentAdditive.DeterministicEndpointAssembly
open Paper2.SquarePadding
open Workspace.Types.CommComplexity

universe u v

variable {Graph : Type u} {State : Type v}

theorem padded_eth_finite_endpoint
    (C : Construction Graph State) (G : Graph)
    (Yes No : Graph → Prop)
    (m N a b C₁ C₀ d₀ h : ℕ)
    (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hN : 2 ≤ N) (hNlow : m ≤ N) (hNhigh : N ≤ m^b)
    (hC₀ : 2*C₁+2 ≤ C₀)
    (hlarge : 2^(max (32*(C₀*b)+16) (8*a)) ≤ m)
    (V : ValidContract C G)
    (U : UniversalContract C G d₀ h)
    (Y : Yes G → YesContract C G d₀ h)
    (H : No G → NoContract C G d₀ h)
    (R : ResourceContract C G N (2^a) C₁)
    (P : TablePresentation C N) :
    let k := ethIterations a m
    let F := state C G k
    let S := side (P.rows F) (P.cols F)
    let M := paddedTable C N P F
    let T := S^2
    let cstar : ℝ := 1 / (4*(a:ℝ))
    0 < cstar ∧ 1 ≤ k ∧ ((2^a)^k)^2 ≤ m ∧
    D M ≤ budget d₀ h k + k ∧
    (Yes G → D M ≤ budget d₀ h k) ∧
    (No G → D M = budget d₀ h k + k ∧ C.profile G F) ∧
    N ≤ S ∧ (∃ e, S = 2^e) ∧
    m^2 ≤ T ∧ T ≤ m^(b*C₀*(2^a)^k) ∧
    2*cstar*(Nat.clog 2 (Nat.clog 2 T):ℝ) < (k:ℝ) ∧
    totalStepTime C G k ≤ N^(C₀*(2^a)^k) := by
  let k := ethIterations a m
  let F := state C G k
  let S := side (P.rows F) (P.cols F)
  let T := S^2
  have hA : 2 ≤ 2^a := by
    simpa only [pow_one] using
      (Nat.pow_le_pow_right (by decide : 0 < (2:ℕ)) ha)
  have hout := padded_conditional_one_exponent C G Yes No N (2^a)
    C₁ C₀ d₀ h k hN hA hC₀ V U Y H R P
  change D (paddedTable C N P F) ≤ budget d₀ h k + k ∧
    (Yes G → D (paddedTable C N P F) ≤ budget d₀ h k) ∧
    (No G → D (paddedTable C N P F) = budget d₀ h k + k ∧
      C.profile G F) ∧ N ≤ S ∧ (∃ e, S = 2^e) ∧
    T ≤ N^(C₀*(2^a)^k) ∧
    totalStepTime C G k ≤ N^(C₀*(2^a)^k) at hout
  rcases hout with ⟨hu, hy, hno, hSide, hPow, hT, hClock⟩
  have hTlow : N^2 ≤ T := Nat.pow_le_pow_left hSide 2
  have hCpos : 1 ≤ C₀ := by omega
  have hn := eth_public_numerics a C₀ b m N T ha hCpos hb
    hNlow hNhigh hTlow hT hlarge
  change 1 ≤ k ∧ ((2^a)^k)^2 ≤ m ∧ m^2 ≤ T ∧
    2 * (1/(4*(a:ℝ))) * (Nat.clog 2 (Nat.clog 2 T):ℝ) < (k:ℝ) ∧
    T ≤ m^(b*C₀*(2^a)^k) at hn
  have hcstar : (0:ℝ) < 1/(4*(a:ℝ)) := by
    have har : (0:ℝ) < a := by exact_mod_cast (by omega : 0 < a)
    positivity
  exact ⟨hcstar, hn.1, hn.2.1, hu, hy, hno,
    hSide, hPow, hn.2.2.1, hn.2.2.2.2,
    hn.2.2.2.1, hClock⟩

#print axioms padded_eth_finite_endpoint

end CurrentAdditive.DeterministicEndpointETH
