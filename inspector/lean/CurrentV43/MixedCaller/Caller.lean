import CurrentV43.MixedCaller.Accounting
import CurrentV43.TimeTradeoff.DeterministicCaller

/-! The actual mixed deterministic-construction/randomized-estimator branch
of v43 Theorem 9.7. The request producer below is the concrete source compiler,
table constructor, and midpoint printer, with no completed-decider premise. -/
namespace CurrentV43.MixedCaller
noncomputable section
open CurrentAdditive Paper2 EthInapproximability.CurrentPaper
open EncodedETHSource EncodedETHSourceComposition Unit4Shell.T10Finite
open V39PermittedNumericalExtraction
set_option maxHeartbeats 2000000
set_option maxRecDepth 65536

variable (D : DinurReduction) (B : BOTReduction (booleanOccurrence D))

abbrev sourceRequest (G : ParametricSource.Schedule) (cs cutoff : ℕ) (hcut : 1≤cutoff) :=
  TimeTradeoff.routedRequest D B G cs cutoff hcut

def actualMachine (G : ParametricSource.Schedule) (A : PermittedEstimator)
    (cs cutoff : ℕ) (hcut : 1≤cutoff) :=
  finiteMachine (sourceRequest D B G cs cutoff hcut) (TimeTradeoff.randomEstimator A).classifier

def actualTapeLength (G : ParametricSource.Schedule) (A : PermittedEstimator)
    (cs cutoff : ℕ) (hcut : 1≤cutoff) :=
  tapeLength (sourceRequest D B G cs cutoff hcut) (TimeTradeoff.randomEstimator A).classifier

def actualTapeProducer (G : ParametricSource.Schedule) (A : PermittedEstimator)
    (cs cutoff : ℕ) (hcut : 1≤cutoff) :=
  tapeProducer (sourceRequest D B G cs cutoff hcut) (TimeTradeoff.randomEstimator A).classifier

def actualTime (G : ParametricSource.Schedule) (A : PermittedEstimator)
    (cs cutoff : ℕ) (hcut : 1≤cutoff) :=
  finiteTime (sourceRequest D B G cs cutoff hcut) (TimeTradeoff.randomEstimator A).classifier

def actualOutput (G : ParametricSource.Schedule) (A : PermittedEstimator)
    (cs cutoff : ℕ) (hcut : 1≤cutoff) :=
  finiteOutput (sourceRequest D B G cs cutoff hcut) (TimeTradeoff.randomEstimator A).classifier

theorem actual_runs (G : ParametricSource.Schedule) (A : PermittedEstimator)
    (cs cutoff : ℕ) (hcut : 1≤cutoff) (w : List Bool)
    (tape : Fin (actualTapeLength D B G A cs cutoff hcut w)→Bool) :
    (actualMachine D B G A cs cutoff hcut).OutputsWithin
      (EncodedComplexity.pair w (List.ofFn tape))
      (actualOutput D B G A cs cutoff hcut w (List.ofFn tape))
      (actualTime D B G A cs cutoff hcut w) :=
  finite_outputs_fixed_clock _ _ w tape

theorem actual_carrier (G : ParametricSource.Schedule) (A : PermittedEstimator)
    (cs cutoff : ℕ) (hcut : 1≤cutoff) (w : List Bool) :
    (actualTapeProducer D B G A cs cutoff hcut).machine.OutputsWithin w
      (List.replicate (actualTapeLength D B G A cs cutoff hcut w) true)
      ((actualTapeProducer D B G A cs cutoff hcut).clock w) :=
  tapeProducer_outputs _ _ w

/-- On every promised original sparse formula, the complete physical caller
has exactly the law of the amplified estimator on its actual deterministic
table and its actual midpoint. -/
theorem actual_law (G : ParametricSource.Schedule) (A : PermittedEstimator)
    (cs cutoff : ℕ) (hcut : 1≤cutoff)
    (Φ : ValidFormula) (hsp : Φ.val.clauses.length≤cs*Φ.val.variables)
    (hN : cutoff≤Φ.val.variables) (event : List Bool→Prop) :
    (Unit4Shell.Definitions.uniformTape
      (actualTapeLength D B G A cs cutoff hcut (EncodedCNF.encode Φ.val))).prob
      (fun tape=>event (actualOutput D B G A cs cutoff hcut (EncodedCNF.encode Φ.val)
        (List.ofFn tape))) =
    (TimeTradeoff.randomEstimator A).classifier.prob
      (V42ActualSource.request D B Φ (G.gap Φ.val.variables)) event := by
  rw [actualTapeLength,actualOutput,finite_law]
  change (TimeTradeoff.randomEstimator A).classifier.prob
    (V42ActualSource.request D B (TimeTradeoff.routedFormula cs cutoff hcut (EncodedCNF.encode Φ.val))
      (G.gap (TimeTradeoff.routedFormula cs cutoff hcut (EncodedCNF.encode Φ.val)).val.variables)) event=_
  rw [TimeTradeoff.routedFormula_original cs cutoff hcut Φ hsp hN]

/-- Success law of the same fixed finite machine just executed above. The
only hypotheses beyond the ordinary estimator guarantee are the actual
table bounds and the requested strict midpoint separation. -/
theorem actual_correct (G : ParametricSource.Schedule) (A : PermittedEstimator)
    (a : ℕ→ℝ) (ha : Monotone a) (T₀ S cs cutoff : ℕ) (hcut : 1≤cutoff)
    (hA : TimeTradeoff.RandomizedSquareAccuracy A a T₀)
    (Φ : ValidFormula) (hsp : Φ.val.clauses.length≤cs*Φ.val.variables)
    (hN : cutoff≤Φ.val.variables) (hu : 0≤a S)
    (hT : T₀≤V42ActualLower.entryCount (V42ActualSource.run D B Φ (G.gap Φ.val.variables)))
    (hS : V42ActualLower.entryCount (V42ActualSource.run D B Φ (G.gap Φ.val.variables))≤S)
    (hgap : 2*a S<(G.gap Φ.val.variables:ℝ)) :
    let p := (Unit4Shell.Definitions.uniformTape
      (actualTapeLength D B G A cs cutoff hcut (EncodedCNF.encode Φ.val))).prob
      (fun tape=>actualOutput D B G A cs cutoff hcut (EncodedCNF.encode Φ.val)
        (List.ofFn tape)=[true])
    (EncodedCNF.Satisfiable Φ.val→(99:ℝ)/100<p) ∧
    (¬EncodedCNF.Satisfiable Φ.val→p<(1:ℝ)/100) := by
  dsimp only
  rw [actual_law D B G A cs cutoff hcut Φ hsp hN (fun out=>out=[true])]
  exact TimeTradeoff.randomized_estimator_deterministic_source D B A a ha T₀ S
    (G.gap Φ.val.variables) hA Φ hu hT hS hgap

/-- The exact caller and physically printed carrier inherit a fixed
polynomial bound from the actual request construction, without imposing
a polynomial bound on the schedule's values or random-tape length. -/
theorem actual_paid (G : ParametricSource.Schedule) (A : PermittedEstimator)
    (cs cutoff : ℕ) (hcut : 1≤cutoff) (sz : List Bool→ℕ)
    (hi : Unit4Shell.Poly.PolyIn sz List.length)
    (ht : Unit4Shell.Poly.PolyIn sz (sourceRequest D B G cs cutoff hcut).clock) :
    Unit4Shell.Poly.PolyIn sz
      (fun w=>(actualTapeProducer D B G A cs cutoff hcut).clock w+
        actualTime D B G A cs cutoff hcut w) :=
  full_cost_poly sz _ _ hi ht

#print axioms actual_runs
#print axioms actual_carrier
#print axioms actual_law
#print axioms actual_correct
#print axioms actual_paid
end
end CurrentV43.MixedCaller
