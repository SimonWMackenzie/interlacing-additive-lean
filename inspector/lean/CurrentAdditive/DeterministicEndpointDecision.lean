import CurrentAdditive.DeterministicEndpointClassifier

/-! The exact same padded table from the finite endpoint is fed to the
midpoint test. This is a semantic decision theorem; executable source,
writer, and estimator machines are separately required for det:eth. -/

namespace CurrentAdditive.DeterministicEndpointDecision

open CurrentAdditive.DeterministicIteration
open CurrentAdditive.DeterministicEndpointNumeric
open CurrentAdditive.DeterministicEndpointAssembly
open CurrentAdditive.DeterministicEndpointETH
open CurrentAdditive.DeterministicEndpointClassifier
open Paper2.SquarePadding
open Workspace.Types.CommComplexity

universe u v

variable {Graph : Type u} {State : Type v}

/-- Any additive estimate within the explicit growing error decides the
YES/NO promise by comparing it to the midpoint for this one table. -/
theorem padded_estimate_decides
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
    (P : TablePresentation C N)
    (z : ℝ)
    (hestimate :
      let k := ethIterations a m
      let F := state C G k
      let S := side (P.rows F) (P.cols F)
      let M := paddedTable C N P F
      |z-(D M:ℝ)| ≤ (1/(4*(a:ℝ))) *
        (Nat.clog 2 (Nat.clog 2 (S^2)):ℝ)) :
    let k := ethIterations a m
    (Yes G → z < (budget d₀ h k:ℝ)+(k:ℝ)/2) ∧
    (No G → (budget d₀ h k:ℝ)+(k:ℝ)/2 < z) := by
  let k := ethIterations a m
  let F := state C G k
  let S := side (P.rows F) (P.cols F)
  let M := paddedTable C N P F
  have he := padded_eth_finite_endpoint C G Yes No m N a b C₁ C₀ d₀ h
    ha hb hN hNlow hNhigh hC₀ hlarge V U Y H R P
  change (0:ℝ) < 1/(4*(a:ℝ)) ∧ 1 ≤ k ∧
    ((2^a)^k)^2 ≤ m ∧ D M ≤ budget d₀ h k + k ∧
    (Yes G → D M ≤ budget d₀ h k) ∧
    (No G → D M = budget d₀ h k + k ∧ C.profile G F) ∧
    N ≤ S ∧ (∃ e, S = 2^e) ∧
    m^2 ≤ S^2 ∧ S^2 ≤ m^(b*C₀*(2^a)^k) ∧
    2*(1/(4*(a:ℝ)))*(Nat.clog 2 (Nat.clog 2 (S^2)):ℝ) < (k:ℝ) ∧
    totalStepTime C G k ≤ N^(C₀*(2^a)^k) at he
  rcases he with ⟨_, _, _, _, hy, hno, _, _, _, _, hgap, _⟩
  have hgap' :
      2*((1/(4*(a:ℝ))) * (Nat.clog 2 (Nat.clog 2 (S^2)):ℝ)) <
        (k:ℝ) := by simpa only [mul_assoc] using hgap
  exact midpoint_classifies (D M) (budget d₀ h k) k z
    ((1/(4*(a:ℝ))) * (Nat.clog 2 (Nat.clog 2 (S^2)):ℝ))
    (Yes G) (No G) hy (fun hn => (hno hn).1) hgap' hestimate

#print axioms padded_estimate_decides

end CurrentAdditive.DeterministicEndpointDecision
