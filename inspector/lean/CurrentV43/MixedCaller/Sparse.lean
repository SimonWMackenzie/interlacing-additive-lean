import CurrentV43.MixedCaller.Bounds
import CurrentV43.TimeTradeoff.RequestClock

namespace CurrentV43.MixedCaller
noncomputable section
open CurrentAdditive Paper2 EthInapproximability.CurrentPaper
open EncodedETHSource EncodedETHSourceComposition Unit4Shell.T10Finite
open V39PermittedNumericalExtraction
set_option maxHeartbeats 2500000
set_option maxRecDepth 65536

variable (D : DinurReduction) (B : BOTReduction (booleanOccurrence D))

def declaredSize (G : ParametricSource.Schedule) (N : ℕ) :=
  TimeTradeoff.deterministicSize (V42ETHPhysical.amplification D B)
    (TimeTradeoff.deterministicSourceConstant D B) N (G.gap N)

theorem declaredSize_pos (G : ParametricSource.Schedule) (N : ℕ) :
    1≤declaredSize D B G N :=
  Nat.one_le_pow _ _ (by omega)

/-- The entire random-carrier printer and fixed mixed caller have a common
S-polynomial bound for all sufficiently large original sparse formulas.
The construction's size constant precedes the estimator and schedule. -/
theorem actual_clock_sparse (G : ParametricSource.Schedule) (A : PermittedEstimator)
    (cs cutoff : ℕ) (hcut : 1≤cutoff) :
    ∃ c d N₀ : ℕ, ∀ Φ : ValidFormula,
      Φ.val.clauses.length≤cs*Φ.val.variables → N₀≤Φ.val.variables →
      (actualTapeProducer D B G A cs cutoff hcut).clock (EncodedCNF.encode Φ.val)+
        actualTime D B G A cs cutoff hcut (EncodedCNF.encode Φ.val)≤
          c*(declaredSize D B G Φ.val.variables)^d := by
  obtain ⟨cr,dr,Nr,hr⟩:=TimeTradeoff.request_clock_sparse D B G cs cutoff hcut
  obtain ⟨c,d,h⟩:=actual_cost_charge D B G A cs cutoff hcut (14*cs+3) 2 (cr*2^dr) dr
  refine ⟨c,d,Nr,fun Φ hsp hN=>?_⟩
  have hS:=declaredSize_pos D B G Φ.val.variables
  apply h (EncodedCNF.encode Φ.val) (declaredSize D B G Φ.val.variables) hS
    (source_input_charge D B G cs Φ hsp)
  exact (hr Φ hsp hN).trans (TimeTradeoff.polynomial_charge hS (le_refl _) cr dr)

/-- Accuracy applies to the actual table, and the required midpoint
separation is the manuscript's sole error-size condition. -/
theorem actual_correct_sparse (G : ParametricSource.Schedule) (A : PermittedEstimator)
    (a : ℕ→ℝ) (ha : Monotone a) (T₀ cs cutoff : ℕ) (hcut : 1≤cutoff)
    (hA : TimeTradeoff.RandomizedSquareAccuracy A a T₀) :
    ∃ N₀ : ℕ, ∀ Φ : ValidFormula,
      Φ.val.clauses.length≤cs*Φ.val.variables → N₀≤Φ.val.variables →
      2*a (declaredSize D B G Φ.val.variables)<(G.gap Φ.val.variables:ℝ) →
      let p := (Unit4Shell.Definitions.uniformTape
        (actualTapeLength D B G A cs cutoff hcut (EncodedCNF.encode Φ.val))).prob
        (fun tape=>actualOutput D B G A cs cutoff hcut (EncodedCNF.encode Φ.val)
          (List.ofFn tape)=[true])
      (EncodedCNF.Satisfiable Φ.val→(99:ℝ)/100<p) ∧
      (¬EncodedCNF.Satisfiable Φ.val→p<(1:ℝ)/100) := by
  let N₀:=max cutoff (max (DeterministicETHSourceBridge.graphPolynomialCutoff D B cs)
    (max 16 (max (2^(4*V42ActualSource.k0 D B)) (B.degreeBound*T₀))))
  refine ⟨N₀,fun Φ hsp hN hgap=>?_⟩
  have hcutoff:cutoff≤Φ.val.variables:=by dsimp [N₀] at hN;omega
  have hgraph:DeterministicETHSourceBridge.graphPolynomialCutoff D B cs≤Φ.val.variables:=by
    dsimp [N₀] at hN;omega
  have hn:16≤Φ.val.variables:=by dsimp [N₀] at hN;omega
  have hb:2^(4*V42ActualSource.k0 D B)≤Φ.val.variables:=by dsimp [N₀] at hN;omega
  have ht:B.degreeBound*T₀≤Φ.val.variables:=by dsimp [N₀] at hN;omega
  exact actual_correct_from_accuracy D B G A a ha T₀ (declaredSize D B G Φ.val.variables)
    cs cutoff hcut hA Φ hsp hcutoff
    (TimeTradeoff.deterministic_source_entries_large D B Φ T₀ (G.gap Φ.val.variables) ht)
    (TimeTradeoff.deterministic_source_size D B cs Φ (G.gap Φ.val.variables) hsp hgraph hn hb) hgap

/-- Complete physical large-input mixed branch. One fixed machine computes
the actual table and midpoint, uses exactly its physically printed finite
fair carrier, halts on every carrier tape within S^O(1), and has amplified
error below 1/100. No completed decider, run or success premise occurs. -/
theorem actual_mixed_large (G : ParametricSource.Schedule) (A : PermittedEstimator)
    (a : ℕ→ℝ) (ha : Monotone a) (T₀ cs cutoff : ℕ) (hcut : 1≤cutoff)
    (hA : TimeTradeoff.RandomizedSquareAccuracy A a T₀) :
    ∃ c d N₀ : ℕ, ∀ Φ : ValidFormula,
      Φ.val.clauses.length≤cs*Φ.val.variables → N₀≤Φ.val.variables →
      2*a (declaredSize D B G Φ.val.variables)<(G.gap Φ.val.variables:ℝ) →
      (actualTapeProducer D B G A cs cutoff hcut).machine.OutputsWithin
        (EncodedCNF.encode Φ.val)
        (List.replicate (actualTapeLength D B G A cs cutoff hcut (EncodedCNF.encode Φ.val)) true)
        (c*(declaredSize D B G Φ.val.variables)^d) ∧
      (∀ tape : Fin (actualTapeLength D B G A cs cutoff hcut (EncodedCNF.encode Φ.val))→Bool,
        (actualMachine D B G A cs cutoff hcut).OutputsWithin
          (EncodedComplexity.pair (EncodedCNF.encode Φ.val) (List.ofFn tape))
          (actualOutput D B G A cs cutoff hcut (EncodedCNF.encode Φ.val) (List.ofFn tape))
          (c*(declaredSize D B G Φ.val.variables)^d)) ∧
      (let p := (Unit4Shell.Definitions.uniformTape
          (actualTapeLength D B G A cs cutoff hcut (EncodedCNF.encode Φ.val))).prob
          (fun tape=>actualOutput D B G A cs cutoff hcut (EncodedCNF.encode Φ.val)
            (List.ofFn tape)=[true]);
        (EncodedCNF.Satisfiable Φ.val→(99:ℝ)/100<p) ∧
        (¬EncodedCNF.Satisfiable Φ.val→p<(1:ℝ)/100)) := by
  obtain ⟨c,d,Nt,ht⟩:=actual_clock_sparse D B G A cs cutoff hcut
  obtain ⟨Nc,hc⟩:=actual_correct_sparse D B G A a ha T₀ cs cutoff hcut hA
  refine ⟨c,d,max Nt Nc,fun Φ hsp hN hgap=>?_⟩
  have htime:=ht Φ hsp ((le_max_left _ _).trans hN)
  refine ⟨BitMachine.outputsWithin_mono _
    (actual_carrier D B G A cs cutoff hcut (EncodedCNF.encode Φ.val)) (by omega),?_,
    hc Φ hsp ((le_max_right _ _).trans hN) hgap⟩
  intro tape
  exact BitMachine.outputsWithin_mono _
    (actual_runs D B G A cs cutoff hcut (EncodedCNF.encode Φ.val) tape) (by omega)

#print axioms actual_clock_sparse
#print axioms actual_correct_sparse
#print axioms actual_mixed_large
end
end CurrentV43.MixedCaller
