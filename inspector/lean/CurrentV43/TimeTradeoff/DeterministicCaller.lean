import CurrentV43.TimeTradeoff.DeterministicFront
import CurrentV43.MixedCaller.Request

/-! Actual fixed arbitrary-gap deterministic caller for v43
`thm:time-tradeoff`. The sparse router handles all raw words by valid finite
replacement formulas and preserves every promised sparse formula above the
chosen cutoff. Schedule, graph, table, midpoint and estimator are physically
computed. No correctness or finished-run certificate is an input. -/
namespace CurrentV43.TimeTradeoff
noncomputable section
open CurrentAdditive Paper2 EthInapproximability.CurrentPaper
open EncodedETHSource EncodedETHSourceComposition Unit4Shell.T10Finite
open V39FramedNumerical V39PermittedDeterministicExtraction
open V40DeterministicSourcePack
open scoped Classical
set_option maxHeartbeats 1500000
set_option maxRecDepth 65536

variable (Src : DinurReduction) (Bsrc : BOTReduction (booleanOccurrence Src))

def routedFormula (cs cutoff : ℕ) (hcut : 1 ≤ cutoff) (w : List Bool) : ValidFormula :=
  sparseFormula cs cutoff hcut w

def routedGap (G : CurrentV43.ParametricSource.Schedule)
    (cs cutoff : ℕ) (hcut : 1 ≤ cutoff) (w : List Bool) :=
  G.gap (routedFormula cs cutoff hcut w).val.variables

def routedGraphInput (G : CurrentV43.ParametricSource.Schedule)
    (cs cutoff : ℕ) (hcut : 1 ≤ cutoff) (w : List Bool) :=
  V42RuntimePrefix.input (EncodedGraph.encode (t10Graph Src Bsrc (routedFormula cs cutoff hcut w)))
    (routedGap G cs cutoff hcut w)

def routedFrontClock (G : CurrentV43.ParametricSource.Schedule)
    (cs cutoff : ℕ) (hcut : 1 ≤ cutoff) (w : List Bool) :=
  let route:=sparseRoute cs cutoff hcut
  let Φ:=routedFormula cs cutoff hcut w
  route.coefficient*(w.length+1)^route.degree+2*(EncodedCNF.encode Φ.val).length+2+
    (deterministicFront Src Bsrc G).clock (EncodedCNF.encode Φ.val)

def routedFront (G : CurrentV43.ParametricSource.Schedule)
    (cs cutoff : ℕ) (hcut : 1 ≤ cutoff) : PhysicalConcat.Producer where
  machine:=BitMachineComposition.composition (sparseRoute cs cutoff hcut).machine
    (deterministicFront Src Bsrc G).machine
  result:=routedGraphInput Src Bsrc G cs cutoff hcut
  clock:=routedFrontClock Src Bsrc G cs cutoff hcut
  outputs w:=by
    let Φ:=routedFormula cs cutoff hcut w
    have hr:=(sparseRoute cs cutoff hcut).outputs w
    change (sparseRoute cs cutoff hcut).machine.OutputsWithin w
      (AEth4.route3Out (cs+2) cutoff w) _ at hr
    rw [AEth4.route3Out_eq] at hr
    have hn:1 ≤ Φ.val.variables:=hcut.trans (AEth4.routed4_variables (cs+2) cutoff w)
    exact BitMachineComposition.composition_outputsWithin _ _ hr
      (deterministicFront_outputs Src Bsrc G Φ hn)

/-- A fixed actual request producer on every raw input. Its output is the
same table-only estimator request used by the mathematical gap theorem. -/
def routedRequest (G : CurrentV43.ParametricSource.Schedule)
    (cs cutoff : ℕ) (hcut : 1 ≤ cutoff) : PhysicalConcat.Producer where
  machine:=BitMachineComposition.composition (routedFront Src Bsrc G cs cutoff hcut).machine
    (CurrentV43.MixedCaller.requestMachine Src Bsrc)
  result:=fun w=>V42ActualSource.request Src Bsrc (routedFormula cs cutoff hcut w)
    (routedGap G cs cutoff hcut w)
  clock:=fun w=>(routedFront Src Bsrc G cs cutoff hcut).clock w+
    2*(routedGraphInput Src Bsrc G cs cutoff hcut w).length+2+
      CurrentV43.MixedCaller.requestTime Src Bsrc (routedFormula cs cutoff hcut w)
        (routedGap G cs cutoff hcut w)
  outputs w:=BitMachineComposition.composition_outputsWithin _ _
    ((routedFront Src Bsrc G cs cutoff hcut).outputs w)
    (CurrentV43.MixedCaller.request_outputs Src Bsrc (routedFormula cs cutoff hcut w)
      (routedGap G cs cutoff hcut w)).1

/-- The remaining deterministic comparator is itself an actual fixed
polynomial-time machine; every previous paid transition is retained. -/
def deterministicCaller (G : CurrentV43.ParametricSource.Schedule) (E : Estimator)
    (cs cutoff : ℕ) (hcut : 1 ≤ cutoff) : PhysicalConcat.Producer where
  machine:=BitMachineComposition.composition (routedRequest Src Bsrc G cs cutoff hcut).machine E.machine
  result:=fun w=>E.run ((routedRequest Src Bsrc G cs cutoff hcut).result w)
  clock:=fun w=>(routedRequest Src Bsrc G cs cutoff hcut).clock w+
    2*((routedRequest Src Bsrc G cs cutoff hcut).result w).length+2+
      E.clockCoefficient*(((routedRequest Src Bsrc G cs cutoff hcut).result w).length+1)^E.clockDegree
  outputs w:=BitMachineComposition.composition_outputsWithin _ _
    ((routedRequest Src Bsrc G cs cutoff hcut).outputs w) (machine_outputs E _)

/-- On the promised sparse large input, routing preserves the exact original
formula and hence its original variable count and supplied schedule. -/
theorem routedFormula_original (cs cutoff : ℕ) (hcut : 1 ≤ cutoff)
    (Φ : ValidFormula) (hsp : Φ.val.clauses.length ≤ cs*Φ.val.variables)
    (hN : cutoff ≤ Φ.val.variables) :
    routedFormula cs cutoff hcut (EncodedCNF.encode Φ.val)=Φ := by
  apply Subtype.ext
  exact AEth4.routed4_encode (cs+2) cutoff Φ.val Φ.property
    (hsp.trans (Nat.mul_le_mul_right _ (by omega))) hN

/-- Literal deterministic SAT execution for an arbitrary paid schedule.
The actual table's upper/lower bounds are the only size obligations; they
are supplied by SourceBounds rather than assumed SAT correctness. -/
theorem deterministic_caller_correct
    (G : CurrentV43.ParametricSource.Schedule)
    (A : PermittedDeterministicEstimator) (a : ℕ → ℝ) (ha : Monotone a)
    (T₀ S cs cutoff : ℕ) (hcut : 1 ≤ cutoff)
    (hA : DeterministicSquareAccuracy A a T₀)
    (Φ : ValidFormula) (hsp : Φ.val.clauses.length ≤ cs*Φ.val.variables)
    (hN : cutoff ≤ Φ.val.variables)
    (hT : T₀ ≤ V42ActualLower.entryCount (V42ActualSource.run Src Bsrc Φ (G.gap Φ.val.variables)))
    (hS : V42ActualLower.entryCount (V42ActualSource.run Src Bsrc Φ (G.gap Φ.val.variables)) ≤ S)
    (hgap : 2*a S < (G.gap Φ.val.variables:ℝ)) :
    (deterministicCaller Src Bsrc G (deterministicEstimator A) cs cutoff hcut).machine.OutputsWithin
      (EncodedCNF.encode Φ.val) [decide (EncodedCNF.Satisfiable Φ.val)]
      ((deterministicCaller Src Bsrc G (deterministicEstimator A) cs cutoff hcut).clock
        (EncodedCNF.encode Φ.val)) := by
  have hr:=(deterministicCaller Src Bsrc G (deterministicEstimator A) cs cutoff hcut).outputs
    (EncodedCNF.encode Φ.val)
  change (deterministicCaller Src Bsrc G (deterministicEstimator A) cs cutoff hcut).machine.OutputsWithin _ ((deterministicEstimator A).run (V42ActualSource.request Src Bsrc
    (routedFormula cs cutoff hcut (EncodedCNF.encode Φ.val))
    (G.gap (routedFormula cs cutoff hcut (EncodedCNF.encode Φ.val)).val.variables))) _ at hr
  rw [routedFormula_original cs cutoff hcut Φ hsp hN,
    deterministic_source_classification Src Bsrc A a ha T₀ S (G.gap Φ.val.variables) hA Φ hT hS hgap] at hr
  exact hr

#print axioms routedFront
#print axioms routedRequest
#print axioms deterministicCaller
#print axioms deterministic_caller_correct
end
end CurrentV43.TimeTradeoff

