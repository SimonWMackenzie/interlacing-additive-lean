import CurrentV43.Randomized.Concrete
import CurrentV43.Randomized.OuterClock
import CurrentV43.ResourceTotal
namespace CurrentV43.RandomizedRate
noncomputable section
open CurrentAdditive ParametricSource
open Paper2 EthInapproximability.CurrentPaper
open EncodedETHSource EncodedETHSourceComposition
open Unit4Shell.T10Finite Unit4Shell.Asymptotics
open V42RandomizedETHEndpoint V39PermittedNumericalExtraction V39ActualOutputMajority
open CurrentAdditive.V43RandomizedRate
set_option maxHeartbeats 4000000
set_option maxRecDepth 32768
set_option synthInstance.maxSize 32768
variable (D : DinurReduction) (B : BOTReduction (booleanOccurrence D))
/-- The same concrete program that satisfies the all-input run and exact
probability theorems has the required paid worst-case runtime. -/
theorem algorithm_power_time (E : ActualEstimator) (a b : ℕ) (ha : 0 < a) (hb : 0 < b)
    (α : ℝ) (hβα : (a:ℝ)/(b:ℝ) ≤ α) (hβ1 : (a:ℝ)/(b:ℝ) ≤ 1)
    (cs cutoff : ℕ) (hcutoff : 1 ≤ cutoff)
    (hsource : V42SourceGeometry.originalCutoff D B (cs+2) ≤ cutoff) :
    ∃ K N₀ : ℕ, ∀ Φ : ValidFormula,
      Φ.val.clauses.length ≤ cs*Φ.val.variables → N₀ ≤ Φ.val.variables →
      (algorithm D B E a b cs cutoff hcutoff hsource).totalTime (EncodedCNF.encode Φ.val) ≤
        ⌈(2:ℝ)^((K:ℝ)*(Φ.val.variables:ℝ)^α)⌉₊ := by
  let S := rationalSchedule a b
  let e := ResourceFit.resourceExponent D B E.classifier
  have he : ResourceFit.sourceExponent D B ≤ e := by
    dsimp [e,ResourceFit.resourceExponent]
    omega
  have he1 : 1 ≤ e := ResourceFit.resourceExponent_pos D B E.classifier
  obtain ⟨C,d,hC⟩ := ResourceFit.total_clock_resource_polynomial D B E.classifier S cs e he he1
  let R := 3000+30*AEth4.phiLen cutoff
  let A := 3*C+2*R+22
  obtain ⟨K,Nt,ht⟩ := input_polynomial_clock_power_time D B a b e A (d+3) cs ha hb α hβα hβ1
  refine ⟨K,max Nt cutoff,?_⟩
  intro Φ hsp hN
  have hNc : cutoff ≤ Φ.val.variables := (le_max_right _ _).trans hN
  have hρ : routedSource cs cutoff hcutoff (EncodedCNF.encode Φ.val) = Φ :=
    Subtype.ext (AEth4.routed4_encode (cs+2) cutoff Φ.val Φ.property
      (hsp.trans (Nat.mul_le_mul_right _ (by omega))) hNc)
  have htests := routedTests D B cs cutoff hcutoff hsource (EncodedCNF.encode Φ.val)
  rw [hρ] at htests
  let w := EncodedCNF.encode Φ.val
  let F := ResourceFit.budget e S Φ
  let inner := ResourceFit.totalClock D B E.classifier S e Φ
  let r := resource D B E.classifier a b
  let T := carrierLength r w
  have hinner : inner ≤ C*(F+1)^d := hC Φ hsp
    (sourceCoefficient D B Φ) (sourceDeltaV D B Φ) (sourceZeta D B) htests
  have hm : w.length ≤ F := by
    have hexp : e*(S.gap Φ.val.variables+1) ≠ 0 :=
      Nat.mul_ne_zero (Nat.ne_of_gt he1) (Nat.succ_ne_zero _)
    exact (show w.length ≤ w.length+2 by omega).trans (Nat.le_self_pow hexp _)
  have heq : inner = (carrierProducer r).clock w+T+4*(w.length+T+1)+
      uniformClock D B E.classifier S r Φ := rfl
  have hout' := add_router_clock_bound w.length T inner ((carrierProducer r).clock w)
    (uniformClock D B E.classifier S r Φ) R C d F heq hinner hm
  have hid : (algorithm D B E a b cs cutoff hcutoff hsource).totalTime w =
      (carrierProducer r).clock w+uniformClock D B E.classifier S r Φ+
      2*AEth4.route3Time (cs+2) cutoff w+14*w.length+7*T+16 :=
    routedAlgorithm_totalTime_large D B E.classifier S r cs cutoff hcutoff hsource _ Φ hsp hNc
  rw [hid]
  have hb : F+1 ≤ w.length+F+1 := by omega
  have houter : (carrierProducer r).clock w+uniformClock D B E.classifier S r Φ+
      2*AEth4.route3Time (cs+2) cutoff w+14*w.length+7*T+16 ≤ A*(w.length+F+1)^(d+3) := by
    apply (show _ ≤ A*(F+1)^(d+3) by simpa only [AEth4.route3Time] using hout').trans
    exact Nat.mul_le_mul_left A (Nat.pow_le_pow_left hb _)
  exact houter.trans (ht Φ hsp ((le_max_left _ _).trans hN))

#print axioms algorithm_power_time
end
end CurrentV43.RandomizedRate
