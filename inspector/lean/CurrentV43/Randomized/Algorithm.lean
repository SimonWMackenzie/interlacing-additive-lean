import CurrentV43.Randomized.Router
import CurrentV43.Randomized.Parameters
import CurrentV43.Parametric.Algorithm
import CurrentV43.Parametric.Timing

namespace CurrentV43.RandomizedRate
noncomputable section
open CurrentAdditive ParametricSource
open Paper2 EthInapproximability.CurrentPaper
open EncodedETHSource EncodedETHSourceComposition
open Unit4Shell.T10Finite Unit4Shell.Asymptotics
open V42RandomizedETHEndpoint V39PermittedNumericalExtraction
set_option maxHeartbeats 4000000
set_option maxRecDepth 32768
set_option synthInstance.maxSize 32768

variable (D : DinurReduction) (B : BOTReduction (booleanOccurrence D))

def resources (C : SelectedTape.Algorithm) (S : Schedule) (R : PhysicalConcat.Producer)
    (Φ : ValidFormula) (ht : SourceTests D B Φ) : Prop :=
  V42RawSamplerJoin.precision (t10Graph D B Φ).vertices (S.gap Φ.val.variables)*
    V42RawSamplerJoin.reservation (t10Graph D B Φ).vertices (S.gap Φ.val.variables) ≤
      blockLength R (EncodedCNF.encode Φ.val) ∧
  ∀ tape, C.tapeLength (request D B S Φ (sourceCoefficient D B Φ)
    (sourceDeltaV D B Φ) (sourceZeta D B) ht tape) ≤ blockLength R (EncodedCNF.encode Φ.val)

def routedTests (cs cutoff : ℕ) (hcutoff : 1 ≤ cutoff)
    (hsource : V42SourceGeometry.originalCutoff D B (cs+2) ≤ cutoff) (w : List Bool) :
    SourceTests D B (routedSource cs cutoff hcutoff w) :=
  routedSource_tests D B cs cutoff hcutoff w hsource

def routedMachine (C : SelectedTape.Algorithm) (S : Schedule) (R : PhysicalConcat.Producer)
    (cs cutoff : ℕ) (hcutoff : 1 ≤ cutoff) :=
  BitMachineComposition.composition (routerTapeMachine cs cutoff hcutoff)
    (randomMachine D B C S R)

def routedOutput (C : SelectedTape.Algorithm) (S : Schedule) (R : PhysicalConcat.Producer)
    (cs cutoff : ℕ) (hcutoff : 1 ≤ cutoff)
    (hsource : V42SourceGeometry.originalCutoff D B (cs+2) ≤ cutoff) (w tape : List Bool) :=
  let Φ := routedSource cs cutoff hcutoff w
  randomOutput D B C S R Φ (sourceCoefficient D B Φ) (sourceDeltaV D B Φ) (sourceZeta D B)
    (routedTests D B cs cutoff hcutoff hsource w) tape

def routedTime (C : SelectedTape.Algorithm) (S : Schedule) (R : PhysicalConcat.Producer)
    (cs cutoff : ℕ) (hcutoff : 1 ≤ cutoff) (w : List Bool) :=
  let Φ := routedSource cs cutoff hcutoff w
  let L := carrierLength R (EncodedCNF.encode Φ.val)
  routerTapeClock cs cutoff hcutoff w+
    2*(EncodedComplexity.pair (EncodedCNF.encode Φ.val) (List.replicate L false)).length+2+
    uniformClock D B C S R Φ

/-- One concrete all-input machine. The resource premises describe only
the lengths that its already-built finite sampler and classifier consume;
the final corollary discharges them from the concrete resource printer. -/
def routedAlgorithm (C : SelectedTape.Algorithm) (S : Schedule) (R : PhysicalConcat.Producer)
    (cs cutoff : ℕ) (hcutoff : 1 ≤ cutoff)
    (hsource : V42SourceGeometry.originalCutoff D B (cs+2) ≤ cutoff)
    (hfit : ∀ w, resources D B C S R (routedSource cs cutoff hcutoff w)
      (routedTests D B cs cutoff hcutoff hsource w)) : FairBitAlgorithm.Algorithm where
  carrier := ParametricSource.compose (router cs cutoff hcutoff) (carrierProducer R)
  tapeLength w := carrierLength R (EncodedCNF.encode (routedSource cs cutoff hcutoff w).val)
  carrier_result w := by
    change (carrierProducer R).result ((router cs cutoff hcutoff).result w) = _
    exact carrier_result R _
  machine := routedMachine D B C S R cs cutoff hcutoff
  output := routedOutput D B C S R cs cutoff hcutoff hsource
  time := routedTime D B C S R cs cutoff hcutoff
  runs w tape := by
    let Φ := routedSource cs cutoff hcutoff w
    have h1 := routerTape_outputs cs cutoff hcutoff w (List.ofFn tape)
    have h2 := random_runs_uniform D B C S R Φ (sourceCoefficient D B Φ)
      (sourceDeltaV D B Φ) (sourceZeta D B) (routedTests D B cs cutoff hcutoff hsource w)
      (hfit w).1 (hfit w).2 tape
    have h := BitMachineComposition.composition_outputsWithin _ _ h1 h2
    simpa only [routedTime,EncodedComplexity.pair_length,List.length_ofFn,List.length_replicate] using h

/-- Large sparse inputs pass through the physical router unchanged. This
identity exposes every carrier, framing, routing and actual caller charge
in the original formula; no random tape occurs in the final clock. -/
theorem routedAlgorithm_totalTime_large (C : SelectedTape.Algorithm) (S : Schedule)
    (R : PhysicalConcat.Producer) (cs cutoff : ℕ) (hcutoff : 1 ≤ cutoff)
    (hsource : V42SourceGeometry.originalCutoff D B (cs+2) ≤ cutoff)
    (hfit : ∀ w, resources D B C S R (routedSource cs cutoff hcutoff w)
      (routedTests D B cs cutoff hcutoff hsource w))
    (Φ : ValidFormula) (hsp : Φ.val.clauses.length ≤ cs*Φ.val.variables)
    (hN : cutoff ≤ Φ.val.variables) :
    (routedAlgorithm D B C S R cs cutoff hcutoff hsource hfit).totalTime (EncodedCNF.encode Φ.val) =
      (carrierProducer R).clock (EncodedCNF.encode Φ.val)+uniformClock D B C S R Φ+
      2*AEth4.route3Time (cs+2) cutoff (EncodedCNF.encode Φ.val)+
      14*(EncodedCNF.encode Φ.val).length+7*carrierLength R (EncodedCNF.encode Φ.val)+16 := by
  have hρ : routedSource cs cutoff hcutoff (EncodedCNF.encode Φ.val)=Φ :=
    Subtype.ext (AEth4.routed4_encode (cs+2) cutoff Φ.val Φ.property
      (hsp.trans (Nat.mul_le_mul_right _ (by omega))) hN)
  unfold FairBitAlgorithm.Algorithm.totalTime
  simp only [routedAlgorithm,ParametricSource.compose,router,routedTime,routerTapeClock,
    hρ,EncodedComplexity.pair_length,List.length_replicate]
  ring

#print axioms routedAlgorithm
#print axioms routedAlgorithm_totalTime_large
end
end CurrentV43.RandomizedRate
