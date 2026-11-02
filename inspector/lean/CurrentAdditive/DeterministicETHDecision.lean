import CurrentAdditive.DeterministicETHComparator
import CurrentAdditive.DeterministicEndpointDecision

/-!
The literal encoded square table, the deterministic estimator's dyadic output,
and the physical midpoint comparator are applied to one and the same generated
matrix. The construction and writer are supplied by the concrete successor
development; the present theorem adds no graph promise to the YES branch.
-/

namespace CurrentAdditive.DeterministicETHDecision

open EthInapproximability.CurrentPaper
open Workspace.Types.CommComplexity
open CurrentAdditive.DeterministicIteration
open CurrentAdditive.DeterministicEndpointNumeric
open CurrentAdditive.DeterministicEndpointAssembly
open CurrentAdditive.DeterministicEndpointETH
open CurrentAdditive.DeterministicEndpointDecision
open CurrentAdditive.DeterministicETHEstimator
open CurrentAdditive.DeterministicETHEncodedTable
open CurrentAdditive.DeterministicETHComparator
open Paper2.SquarePadding

universe u v

variable {Graph : Type u} {State : Type v}

/-- On the actual padded table, a dyadic estimate in the manuscript's
eventual domain makes the checked midpoint comparator return the SAT bit. -/
theorem encoded_padded_midpoint
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
    (est : List Bool → List Bool)
    (hest : EventuallyAccurate est (1/(4*(a:ℝ))))
    (hthreshold : hest.2.choose ≤ m^2) :
    let k := ethIterations a m
    let F := state C G k
    let S := side (P.rows F) (P.cols F)
    let M := paddedTable C N P F
    ∃ z : ℝ,
      Paper2.AModel.decodeDyadic (est (squareWord M)) = some z ∧
      (Yes G → z < (budget d₀ h k:ℝ)+(k:ℝ)/2) ∧
      (No G → (budget d₀ h k:ℝ)+(k:ℝ)/2 < z) ∧
      Paper2.CmpOwner.machine.OutputsWithin
        (EncodedComplexity.pair
          (midpointHeader (budget d₀ h k) k) (est (squareWord M)))
        [decide (z < (budget d₀ h k:ℝ)+(k:ℝ)/2)]
        (Paper2.CmpOwner.cmpTime
          (midpointHeader (budget d₀ h k) k).length
          (est (squareWord M)).length) := by
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
    N ≤ S ∧ (∃ e, S = 2^e) ∧ m^2 ≤ S^2 ∧
    S^2 ≤ m^(b*C₀*(2^a)^k) ∧
    2*(1/(4*(a:ℝ)))*(Nat.clog 2 (Nat.clog 2 (S^2)):ℝ) < (k:ℝ) ∧
    totalStepTime C G k ≤ N^(C₀*(2^a)^k) at he
  rcases he with ⟨hcpos, _, _, _, _, _, hside, _, hTlo, _, _, _⟩
  have hS : 0 < S := by omega
  have hT0 : hest.2.choose ≤ S^2 := hthreshold.trans hTlo
  have hT4 : 4 ≤ S^2 := by
    have hs2 : 2 ≤ S := hN.trans hside
    nlinarith
  have hc : (0:ℝ) ≤ 1/(4*(a:ℝ)) := hcpos.le
  obtain ⟨z, hz, herr⟩ := accurate_on_encoded_square est _ hc hest M hS hT0 hT4
  have hclass := padded_estimate_decides C G Yes No m N a b C₁ C₀ d₀ h
    ha hb hN hNlow hNhigh hC₀ hlarge V U Y H R P z herr
  exact ⟨z, hz, hclass.1, hclass.2,
    comparator_run (budget d₀ h k) k (est (squareWord M)) z hz⟩

#print axioms encoded_padded_midpoint

end CurrentAdditive.DeterministicETHDecision
