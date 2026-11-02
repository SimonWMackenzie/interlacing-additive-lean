import CurrentV43.TimeTradeoff.DeterministicEndpoint

/-! Checked enlargement to the common displayed construction constant C
of v43 `thm:time-tradeoff`. Constants are selected before either estimator
and the arbitrary paid gap schedule. -/
namespace CurrentV43.TimeTradeoff
noncomputable section
open CurrentAdditive Paper2 EthInapproximability.CurrentPaper
open EncodedETHSource EncodedETHSourceComposition Unit4Shell.T10Finite
open V39PermittedDeterministicExtraction
open scoped Classical

 theorem randomizedSize_mono_constant {C₁ C₂ : ℕ} (hC : C₁ ≤ C₂) (N K : ℕ) :
    randomizedSize C₁ N K ≤ randomizedSize C₂ N K :=
  Nat.pow_le_pow_right (by omega) (Nat.mul_le_mul_right (K+1) hC)

 theorem deterministicSize_mono_constant (Amp : ℕ) {C₁ C₂ : ℕ} (hC : C₁ ≤ C₂) (N K : ℕ) :
    deterministicSize Amp C₁ N K ≤ deterministicSize Amp C₂ N K :=
  Nat.pow_le_pow_right (by omega) (Nat.mul_le_mul_right (Amp^K) hC)

 theorem gap_of_larger_size (a : ℕ → ℝ) (ha : Monotone a) {T S K : ℕ}
    (hsize : T ≤ S) (hgap : 2*a S < (K:ℝ)) : 2*a T < (K:ℝ) := by
  have h:=ha hsize
  linarith

/-- The deterministic branch with any larger common construction constant.
Its physical program is unchanged, and every original-N runtime is charged. -/
 theorem deterministic_time_tradeoff_at
    (Src : DinurReduction) (Bsrc : BOTReduction (booleanOccurrence Src))
    (C : ℕ) (hC : deterministicSourceConstant Src Bsrc ≤ C)
    (cs : ℕ) (G : CurrentV43.ParametricSource.Schedule)
    (A : PermittedDeterministicEstimator) (a : ℕ → ℝ) (ha : Monotone a)
    (T₀ : ℕ) (hA : DeterministicSquareAccuracy A a T₀)
    (hgap : ∃ N₁ : ℕ, ∀ N, N₁ ≤ N →
      2*a (deterministicSize (V42ETHPhysical.amplification Src Bsrc) C N (G.gap N)) < (G.gap N:ℝ)) :
    ∃ M : PhysicalConcat.Producer,
      (∀ Φ : ValidFormula, Φ.val.clauses.length ≤ cs*Φ.val.variables →
        M.result (EncodedCNF.encode Φ.val)=[decide (EncodedCNF.Satisfiable Φ.val)]) ∧
      ∃ c d N₀ : ℕ, ∀ Φ : ValidFormula,
        Φ.val.clauses.length ≤ cs*Φ.val.variables → N₀ ≤ Φ.val.variables →
        M.clock (EncodedCNF.encode Φ.val) ≤
          c*(deterministicSize (V42ETHPhysical.amplification Src Bsrc)
            C Φ.val.variables (G.gap Φ.val.variables))^d := by
  have hsmall:∃ N₁:ℕ,∀ N,N₁ ≤ N →
      2*a (deterministicSize (V42ETHPhysical.amplification Src Bsrc)
        (deterministicSourceConstant Src Bsrc) N (G.gap N)) < (G.gap N:ℝ) := by
    obtain ⟨N₁,h⟩:=hgap
    exact ⟨N₁,fun N hN=>gap_of_larger_size a ha
      (deterministicSize_mono_constant _ hC N (G.gap N)) (h N hN)⟩
  obtain ⟨M,hcorrect,c,d,N₀,htime⟩:=
    deterministic_time_tradeoff Src Bsrc cs G A a ha T₀ hA hsmall
  exact ⟨M,hcorrect,c,d,N₀,fun Φ hsp hN=>(htime Φ hsp hN).trans
    (Nat.mul_le_mul_left c (Nat.pow_le_pow_left
      (deterministicSize_mono_constant _ hC Φ.val.variables (G.gap Φ.val.variables)) d))⟩

#print axioms deterministic_time_tradeoff_at
end
end CurrentV43.TimeTradeoff
