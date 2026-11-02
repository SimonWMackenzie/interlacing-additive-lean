import CurrentV43.MixedCaller.Endpoint

namespace CurrentV43.MixedCaller
noncomputable section
open CurrentAdditive Paper2 EthInapproximability.CurrentPaper
open EncodedETHSource EncodedETHSourceComposition
open V39PermittedNumericalExtraction

variable (D : DinurReduction) (B : BOTReduction (booleanOccurrence D))

theorem declaredSize_le (G : ParametricSource.Schedule) (C₀ N : ℕ)
    (hC : TimeTradeoff.deterministicSourceConstant D B≤C₀) :
    declaredSize D B G N≤TimeTradeoff.deterministicSize
      (V42ETHPhysical.amplification D B) C₀ N (G.gap N) :=
  Nat.pow_le_pow_right (by omega)
    (Nat.mul_le_mul_right ((V42ETHPhysical.amplification D B)^(G.gap N)) hC)

/-- The same actual mixed algorithm works with a larger size constant,
allowing one common C to be selected before choosing either construction. -/
theorem mixed_algorithmic_implication_at (C₀ : ℕ)
    (hC : TimeTradeoff.deterministicSourceConstant D B≤C₀)
    (G : ParametricSource.Schedule) (A : PermittedEstimator)
    (a : ℕ→ℝ) (ha : Monotone a) (T₀ cs : ℕ)
    (hA : TimeTradeoff.RandomizedSquareAccuracy A a T₀)
    (hgap : ∃ Ngap,∀ N,Ngap≤N→
      2*a (TimeTradeoff.deterministicSize (V42ETHPhysical.amplification D B) C₀ N (G.gap N))<
        (G.gap N:ℝ)) :
    ∃ F : FairBitAlgorithm.Algorithm,
      (∀ Φ : ValidFormula,Φ.val.clauses.length≤cs*Φ.val.variables →
        (EncodedCNF.Satisfiable Φ.val→(2:ℝ)/3≤F.prob (EncodedCNF.encode Φ.val) (·=[true])) ∧
        (¬EncodedCNF.Satisfiable Φ.val→F.prob (EncodedCNF.encode Φ.val) (·=[true])≤(1:ℝ)/3)) ∧
      (∃ c d N₀ : ℕ,∀ Φ : ValidFormula,
        Φ.val.clauses.length≤cs*Φ.val.variables → N₀≤Φ.val.variables →
        F.totalTime (EncodedCNF.encode Φ.val)≤c*
          (TimeTradeoff.deterministicSize (V42ETHPhysical.amplification D B) C₀
            Φ.val.variables (G.gap Φ.val.variables))^d) := by
  have hsmall:∃ Ngap,∀ N,Ngap≤N→
      2*a (declaredSize D B G N)<(G.gap N:ℝ) := by
    obtain ⟨Ngap,hg⟩:=hgap
    refine ⟨Ngap,fun N hN=>?_⟩
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left (ha (declaredSize_le D B G C₀ N hC))
      (by norm_num : (0:ℝ)≤2)) (hg N hN)
  obtain ⟨F,hcorrect,c,d,N₀,hclock⟩:=
    mixed_algorithmic_implication D B G A a ha T₀ cs hA hsmall
  refine ⟨F,hcorrect,c,d,N₀,fun Φ hsp hN=>?_⟩
  exact (hclock Φ hsp hN).trans (Nat.mul_le_mul_left c
    (Nat.pow_le_pow_left (declaredSize_le D B G C₀ Φ.val.variables hC) d))

#print axioms mixed_algorithmic_implication_at
end
end CurrentV43.MixedCaller
