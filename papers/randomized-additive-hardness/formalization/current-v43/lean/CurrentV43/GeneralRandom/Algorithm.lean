import CurrentV43.GeneralRandom.Source
import CurrentV43.Randomized.AlgorithmLaw
import CurrentV43.ResourceFit
import CurrentV43.Parametric.Resource

set_option autoImplicit false

namespace CurrentV43.GeneralRandom
noncomputable section
open CurrentAdditive Paper2 EthInapproximability.CurrentPaper
open EncodedETHSource EncodedETHSourceComposition Unit4Shell.T10Finite
open ParametricSource TimeTradeoff V39ActualOutputMajority
open CurrentAdditive.V42RandomizedETHEndpoint
set_option maxHeartbeats 3000000
set_option maxRecDepth 32768
set_option synthInstance.maxSize 32768
variable (D : DinurReduction) (B : BOTReduction (booleanOccurrence D))

def resource (C : SelectedTape.Algorithm) (G : Schedule) :=
  resourceProducer G (ResourceFit.resourceExponent D B C)

theorem concrete_resources (C : SelectedTape.Algorithm) (G : Schedule)
    (Φ : ValidFormula) (ht : V42RandomizedETHEndpoint.SourceTests D B Φ) :
    RandomizedRate.resources D B C G (resource D B C G) Φ ht := by
  have hfit := ResourceFit.actual_tapes_fit D B C G Φ
    (RandomizedRate.sourceCoefficient D B Φ) (RandomizedRate.sourceDeltaV D B Φ)
    (RandomizedRate.sourceZeta D B) ht
  have hb := resource_le_block (resource D B C G) (EncodedCNF.encode Φ.val)
  change ((resourceProducer G (ResourceFit.resourceExponent D B C)).result
    (EncodedCNF.encode Φ.val)).length ≤ _ at hb
  rw [resource_length] at hb
  refine ⟨hfit.1.trans hb,?_⟩
  intro tape
  exact (hfit.2 (sampledBits D B G Φ tape)).trans hb

/-- The finite-prefix SAT router, schedule printer, carrier printer,
sampler and estimator are parts of this one actual all-input machine. -/
def algorithm (C : SelectedTape.Algorithm) (G : Schedule) (cs cutoff : Nat)
    (hcut : 1 ≤ cutoff) (hsource : V42SourceGeometry.originalCutoff D B (cs+2) ≤ cutoff) :
    FairBitAlgorithm.Algorithm :=
  RandomizedRate.routedAlgorithm D B C G (resource D B C G) cs cutoff hcut hsource
    (fun w => concrete_resources D B C G (routedSource cs cutoff hcut w)
      (RandomizedRate.routedTests D B cs cutoff hcut hsource w))

theorem algorithm_probability (E : ActualEstimator) (G : Schedule) (cs cutoff : Nat)
    (hcut : 1 ≤ cutoff) (hsource : V42SourceGeometry.originalCutoff D B (cs+2) ≤ cutoff)
    (w : List Bool) :
    (algorithm D B E.classifier G cs cutoff hcut hsource).prob w (·=[true]) =
    let Φ := routedSource cs cutoff hcut w
    (RandomizedRate.sourceLaw D B (G.gap Φ.val.variables) E Φ).prob
      (fun z => RandomizedRate.sourceAccepts D B (G.gap Φ.val.variables) Φ
        (RandomizedRate.routedTests D B cs cutoff hcut hsource w) E z.1 z.2) :=
  RandomizedRate.routedAlgorithm_probability D B E G (resource D B E.classifier G)
    cs cutoff hcut hsource _ w

/-- Exact all-size sparse-SAT correctness; the finite prefix is decided
inside the existing charged router before the source construction runs. -/
theorem algorithm_correct (C0 : Nat) (hC0 : sourceConstant D ≤ C0)
    (A : NumericalEstimator) (a : Nat → Real) (ha : Monotone a)
    (T₀ : Nat) (hA : Accurate A a T₀) (G : Schedule) (hpos : ∀ N,1 ≤ G.gap N)
    (hgap : ∃ Ng : Nat,∀ N,Ng ≤ N →
      2*a (randomizedSize C0 N (G.gap N)) < (G.gap N:Real)) (cs : Nat) :
    ∃ cutoff : Nat, ∃ hcut : 1 ≤ cutoff,
      ∃ hsource : V42SourceGeometry.originalCutoff D B (cs+2) ≤ cutoff,
      ∀ Φ : ValidFormula, Φ.val.clauses.length ≤ cs*Φ.val.variables →
      (EncodedCNF.Satisfiable Φ.val → (2:Real)/3 ≤
        (algorithm D B (selected A).classifier G cs cutoff hcut hsource).prob
          (EncodedCNF.encode Φ.val) (·=[true])) ∧
      (¬EncodedCNF.Satisfiable Φ.val →
        (algorithm D B (selected A).classifier G cs cutoff hcut hsource).prob
          (EncodedCNF.encode Φ.val) (·=[true]) ≤ (1:Real)/3) := by
  obtain ⟨cutoff,hcut,hsource,h⟩ := source_all_large D B (cs+2) C0 hC0 A a ha T₀ hA G hpos hgap
  refine ⟨cutoff,hcut,hsource,?_⟩
  intro Φ hsp
  rw [algorithm_probability]
  let ρ := routedSource cs cutoff hcut (EncodedCNF.encode Φ.val)
  have hρ := h ρ (routedSource_sparse cs cutoff hcut _)
    (AEth4.routed4_variables (cs+2) cutoff _) (RandomizedRate.routedTests D B cs cutoff hcut hsource _)
  have hsp' : Φ.val.clauses.length ≤ (cs+2)*Φ.val.variables :=
    hsp.trans (Nat.mul_le_mul_right _ (by omega))
  have hsat : EncodedCNF.Satisfiable ρ.val ↔ EncodedCNF.Satisfiable Φ.val :=
    (AEth4.routed4_sat_iff (cs+2) hcut Φ.val Φ.property hsp').trans
      (EncodedCNF.encode_mem_iff Φ.val Φ.property)
  exact ⟨fun hy => by have hp := hρ.1 (hsat.2 hy); linarith,
    fun hn => by have hp := hρ.2 (fun hy=>hn (hsat.1 hy)); linarith⟩

#print axioms algorithm
#print axioms algorithm_correct
end
end CurrentV43.GeneralRandom
