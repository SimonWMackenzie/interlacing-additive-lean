import CurrentV43.MixedCaller.Sparse
import CurrentV43.Parametric.Algorithm
import CurrentAdditive.V40DeterministicRoutedLaw

namespace CurrentV43.MixedCaller
noncomputable section
open CurrentAdditive Paper2 EthInapproximability.CurrentPaper
open EncodedETHSource EncodedETHSourceComposition Unit4Shell.T10Finite
open V39PermittedNumericalExtraction
set_option maxHeartbeats 3000000
set_option maxRecDepth 65536

variable (D : DinurReduction) (B : BOTReduction (booleanOccurrence D))

/-- One actual uniform fair-bit algorithm: source routing, arbitrary paid
schedule, graph, table, midpoint, then the common amplified estimator. -/
def algorithm (G : ParametricSource.Schedule) (A : PermittedEstimator)
    (cs cutoff : ℕ) (hcut : 1≤cutoff) : FairBitAlgorithm.Algorithm where
  carrier:=actualTapeProducer D B G A cs cutoff hcut
  tapeLength:=actualTapeLength D B G A cs cutoff hcut
  carrier_result w:=ParametricSource.carrier_result _ w
  machine:=actualMachine D B G A cs cutoff hcut
  output:=actualOutput D B G A cs cutoff hcut
  time:=actualTime D B G A cs cutoff hcut
  runs:=actual_runs D B G A cs cutoff hcut

theorem algorithm_prob (G : ParametricSource.Schedule) (A : PermittedEstimator)
    (cs cutoff : ℕ) (hcut : 1≤cutoff) (w : List Bool) (event : List Bool→Prop) :
    (algorithm D B G A cs cutoff hcut).prob w event=
      (TimeTradeoff.randomEstimator A).classifier.prob
        ((sourceRequest D B G cs cutoff hcut).result w) event :=
  finite_law _ _ w event

/-- The complete fair-bit charge includes carrier printing, one transition
per random bit, source/tape framing, and every actual caller transition. -/
theorem algorithm_clock_sparse (G : ParametricSource.Schedule) (A : PermittedEstimator)
    (cs cutoff : ℕ) (hcut : 1≤cutoff) :
    ∃ c d N₀ : ℕ, ∀ Φ : ValidFormula,
      Φ.val.clauses.length≤cs*Φ.val.variables → N₀≤Φ.val.variables →
      (algorithm D B G A cs cutoff hcut).totalTime (EncodedCNF.encode Φ.val)≤
        c*(declaredSize D B G Φ.val.variables)^d := by
  obtain ⟨c,d,N₀,h⟩:=actual_clock_sparse D B G A cs cutoff hcut
  let p:=(actualTapeProducer D B G A cs cutoff hcut).machine.pushBound
  refine ⟨(1+5*p)*c+9*(14*cs+3)+4,d+2,N₀,fun Φ hsp hN=>?_⟩
  let S:=declaredSize D B G Φ.val.variables
  let w:=EncodedCNF.encode Φ.val
  have hS:1≤S:=declaredSize_pos D B G _
  have hcost:=h Φ hsp hN
  have hinput:=source_input_charge D B G cs Φ hsp
  have hbits:=BitMachine.output_length_bound (actualTapeProducer D B G A cs cutoff hcut).machine
    (actual_carrier D B G A cs cutoff hcut w)
  rw [List.length_replicate] at hbits
  have hd:S^d≤S^(d+2):=Nat.pow_le_pow_right hS (by omega)
  have h2:S^2≤S^(d+2):=Nat.pow_le_pow_right hS (by omega)
  have h1:1≤S^(d+2):=Nat.one_le_pow _ _ hS
  have hc:=Nat.mul_le_mul_left c hd
  have hi:=Nat.mul_le_mul_left (14*cs+3) h2
  change _≤c*S^d at hcost
  change w.length≤(14*cs+3)*S^2 at hinput
  change actualTapeLength D B G A cs cutoff hcut w≤w.length+
    (actualTapeProducer D B G A cs cutoff hcut).clock w*p at hbits
  change (actualTapeProducer D B G A cs cutoff hcut).clock w+
      actualTapeLength D B G A cs cutoff hcut w+
      4*(w.length+actualTapeLength D B G A cs cutoff hcut w+1)+
      actualTime D B G A cs cutoff hcut w≤((1+5*p)*c+9*(14*cs+3)+4)*S^(d+2)
  nlinarith

def completionCutoff (cs T₀ Ngap : ℕ) :=
  max 1 (max Ngap (max (B.degreeBound*T₀)
    (max (DeterministicETHSourceBridge.graphPolynomialCutoff D B (cs+2))
      (max 16 (2^(4*V42ActualSource.k0 D B))))))

theorem completionCutoff_pos (cs T₀ Ngap : ℕ) : 1≤completionCutoff D B cs T₀ Ngap :=
  le_max_left _ _

/-- The finite small-input table in the actual router preserves SAT. Thus
the same one fixed algorithm is correct for every sparse original formula,
including every size below the eventual accuracy and gap cutoffs. -/
theorem algorithm_correct_all (G : ParametricSource.Schedule) (A : PermittedEstimator)
    (a : ℕ→ℝ) (ha : Monotone a) (T₀ cs Ngap : ℕ)
    (hA : TimeTradeoff.RandomizedSquareAccuracy A a T₀)
    (hgap : ∀ N,Ngap≤N→2*a (declaredSize D B G N)<(G.gap N:ℝ))
    (Φ : ValidFormula) (hsp : Φ.val.clauses.length≤cs*Φ.val.variables) :
    let cutoff:=completionCutoff D B cs T₀ Ngap
    let F:=algorithm D B G A cs cutoff (completionCutoff_pos D B cs T₀ Ngap)
    (EncodedCNF.Satisfiable Φ.val→(2:ℝ)/3≤F.prob (EncodedCNF.encode Φ.val) (·=[true])) ∧
    (¬EncodedCNF.Satisfiable Φ.val→F.prob (EncodedCNF.encode Φ.val) (·=[true])≤(1:ℝ)/3) := by
  let cutoff:=completionCutoff D B cs T₀ Ngap
  have hc:1≤cutoff:=completionCutoff_pos D B cs T₀ Ngap
  let Ψ:=TimeTradeoff.routedFormula cs cutoff hc (EncodedCNF.encode Φ.val)
  have hlarge:cutoff≤Ψ.val.variables:=AEth4.routed4_variables _ _ _
  have hsparse:Ψ.val.clauses.length≤(cs+2)*Ψ.val.variables:=
    V40DeterministicETHEndpoint.routed_sparse cs cutoff hc _
  have hNgap:Ngap≤Ψ.val.variables:=by dsimp [cutoff,completionCutoff] at hlarge;omega
  have hT₀:B.degreeBound*T₀≤Ψ.val.variables:=by dsimp [cutoff,completionCutoff] at hlarge;omega
  have hgraph:DeterministicETHSourceBridge.graphPolynomialCutoff D B (cs+2)≤Ψ.val.variables:=by
    dsimp [cutoff,completionCutoff] at hlarge;omega
  have h16:16≤Ψ.val.variables:=by dsimp [cutoff,completionCutoff] at hlarge;omega
  have hbase:2^(4*V42ActualSource.k0 D B)≤Ψ.val.variables:=by
    dsimp [cutoff,completionCutoff] at hlarge;omega
  have hT:=TimeTradeoff.deterministic_source_entries_large D B Ψ T₀ (G.gap Ψ.val.variables) hT₀
  have hS:=TimeTradeoff.deterministic_source_size D B (cs+2) Ψ (G.gap Ψ.val.variables)
    hsparse hgraph h16 hbase
  have hu:=TimeTradeoff.randomized_stored_error_nonnegative A a ha T₀
    (declaredSize D B G Ψ.val.variables) hA _ hT hS
  have hsource:=TimeTradeoff.randomized_estimator_deterministic_source D B A a ha T₀
    (declaredSize D B G Ψ.val.variables) (G.gap Ψ.val.variables) hA Ψ hu hT hS
    (hgap _ hNgap)
  have hsat:EncodedCNF.Satisfiable Ψ.val↔EncodedCNF.Satisfiable Φ.val:=
    V40DeterministicETHEndpoint.routed_sat_iff cs cutoff hc Φ hsp
  dsimp only
  rw [algorithm_prob D B G A cs cutoff hc (EncodedCNF.encode Φ.val) (fun out=>out=[true])]
  change (EncodedCNF.Satisfiable Φ.val→(2:ℝ)/3≤
      (TimeTradeoff.randomEstimator A).classifier.prob
        (V42ActualSource.request D B Ψ (G.gap Ψ.val.variables)) (·=[true])) ∧
    (¬EncodedCNF.Satisfiable Φ.val→(TimeTradeoff.randomEstimator A).classifier.prob
        (V42ActualSource.request D B Ψ (G.gap Ψ.val.variables)) (·=[true])≤(1:ℝ)/3)
  constructor
  · intro hs
    have h:=hsource.1 (hsat.mpr hs)
    linarith
  · intro hs
    have h:=hsource.2 (fun ht=>hs (hsat.mp ht))
    linarith

/-- v43 Theorem 9.7, deterministic construction and randomized estimator.
The source constants in declaredSize precede the density, estimator, and
arbitrary paid schedule. All original sparse inputs are decided, and the
full actual fair-bit runtime is S(N,k(N))^O(1) in the original variables. -/
theorem mixed_algorithmic_implication (G : ParametricSource.Schedule) (A : PermittedEstimator)
    (a : ℕ→ℝ) (ha : Monotone a) (T₀ cs : ℕ)
    (hA : TimeTradeoff.RandomizedSquareAccuracy A a T₀)
    (hgap : ∃ Ngap,∀ N,Ngap≤N→2*a (declaredSize D B G N)<(G.gap N:ℝ)) :
    ∃ F : FairBitAlgorithm.Algorithm,
      (∀ Φ : ValidFormula,Φ.val.clauses.length≤cs*Φ.val.variables →
        (EncodedCNF.Satisfiable Φ.val→(2:ℝ)/3≤F.prob (EncodedCNF.encode Φ.val) (·=[true])) ∧
        (¬EncodedCNF.Satisfiable Φ.val→F.prob (EncodedCNF.encode Φ.val) (·=[true])≤(1:ℝ)/3)) ∧
      (∃ c d N₀ : ℕ,∀ Φ : ValidFormula,
        Φ.val.clauses.length≤cs*Φ.val.variables → N₀≤Φ.val.variables →
        F.totalTime (EncodedCNF.encode Φ.val)≤c*(declaredSize D B G Φ.val.variables)^d) := by
  obtain ⟨Ngap,hgap⟩:=hgap
  let cutoff:=completionCutoff D B cs T₀ Ngap
  have hc:1≤cutoff:=completionCutoff_pos D B cs T₀ Ngap
  refine ⟨algorithm D B G A cs cutoff hc,?_,algorithm_clock_sparse D B G A cs cutoff hc⟩
  exact fun Φ hsp=>algorithm_correct_all D B G A a ha T₀ cs Ngap hA hgap Φ hsp

#print axioms algorithm
#print axioms algorithm_clock_sparse
#print axioms algorithm_correct_all
#print axioms mixed_algorithmic_implication
end
end CurrentV43.MixedCaller
