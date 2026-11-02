import CurrentV43.MixedCaller.Charge
import CurrentV43.TimeTradeoff.ErrorNonnegative

namespace CurrentV43.MixedCaller
noncomputable section
open CurrentAdditive Paper2 EthInapproximability.CurrentPaper
open EncodedETHSource EncodedETHSourceComposition Unit4Shell.T10Finite
open V39PermittedNumericalExtraction
set_option maxHeartbeats 2000000

theorem encoded_sparse_length (cs : ℕ) (Φ : ValidFormula)
    (hsp : Φ.val.clauses.length≤cs*Φ.val.variables) :
    (EncodedCNF.encode Φ.val).length≤(14*cs+3)*(Φ.val.variables+2)^2 := by
  have h:=EncodedCNF.encode_length_upper Φ.val Φ.property
  have hm:=Nat.mul_le_mul_right (6*Φ.val.variables+8) hsp
  have hn:Φ.val.variables+2≤(Φ.val.variables+2)^2:=Nat.le_self_pow (by decide : 2≠0) _
  have hp:Φ.val.variables*(6*Φ.val.variables+8)≤14*(Φ.val.variables+2)^2:=by nlinarith
  have hc:=Nat.mul_le_mul_left cs hp
  nlinarith

theorem source_input_charge (D : DinurReduction) (B : BOTReduction (booleanOccurrence D))
    (G : ParametricSource.Schedule) (cs : ℕ) (Φ : ValidFormula)
    (hsp : Φ.val.clauses.length≤cs*Φ.val.variables) :
    (EncodedCNF.encode Φ.val).length≤(14*cs+3)*
      (TimeTradeoff.deterministicSize (V42ETHPhysical.amplification D B)
        (TimeTradeoff.deterministicSourceConstant D B) Φ.val.variables (G.gap Φ.val.variables))^2 := by
  have hA:2≤V42ETHPhysical.amplification D B:=
    (by decide : 2≤2^64).trans (V42GraphRuntime.amplification_ge _)
  have hd:=TimeTradeoff.deterministicSize_dominates (V42ETHPhysical.amplification D B)
    (TimeTradeoff.deterministicSourceConstant D B) Φ.val.variables (G.gap Φ.val.variables)
    hA (TimeTradeoff.deterministicSourceConstant_pos D B)
  apply (encoded_sparse_length cs Φ hsp).trans
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) 2)

/-- On the original sparse input, correctness needs no separate
nonnegativity assumption: ordinary estimator accuracy already implies it. -/
theorem actual_correct_from_accuracy (D : DinurReduction)
    (B : BOTReduction (booleanOccurrence D)) (G : ParametricSource.Schedule)
    (A : PermittedEstimator) (a : ℕ→ℝ) (ha : Monotone a)
    (T₀ S cs cutoff : ℕ) (hcut : 1≤cutoff)
    (hA : TimeTradeoff.RandomizedSquareAccuracy A a T₀)
    (Φ : ValidFormula) (hsp : Φ.val.clauses.length≤cs*Φ.val.variables)
    (hN : cutoff≤Φ.val.variables)
    (hT : T₀≤V42ActualLower.entryCount (V42ActualSource.run D B Φ (G.gap Φ.val.variables)))
    (hS : V42ActualLower.entryCount (V42ActualSource.run D B Φ (G.gap Φ.val.variables))≤S)
    (hgap : 2*a S<(G.gap Φ.val.variables:ℝ)) :
    let p := (Unit4Shell.Definitions.uniformTape
      (actualTapeLength D B G A cs cutoff hcut (EncodedCNF.encode Φ.val))).prob
      (fun tape=>actualOutput D B G A cs cutoff hcut (EncodedCNF.encode Φ.val)
        (List.ofFn tape)=[true])
    (EncodedCNF.Satisfiable Φ.val→(99:ℝ)/100<p) ∧
    (¬EncodedCNF.Satisfiable Φ.val→p<(1:ℝ)/100) :=
  actual_correct D B G A a ha T₀ S cs cutoff hcut hA Φ hsp hN
    (TimeTradeoff.randomized_stored_error_nonnegative A a ha T₀ S hA _ hT hS)
    hT hS hgap

#print axioms source_input_charge
#print axioms actual_correct_from_accuracy
end
end CurrentV43.MixedCaller
