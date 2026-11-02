import EthInapproximability.CurrentPaper.U4ArmClock

/-!
# `thm:main` against the ETH consumer, with only hETH and H-B2 (lane owner:b-unit4-shell-4)

Source: frozen v8 `06-eth.tex:204-243` (proof of `thm:main`): "Let `δ_ETH > 0` be the exponent
in the fixed-model form of ETH, choose a rational `0 < ε < δ_ETH`, and then fix the resulting
source algorithms, repetition function `L`, construction, and `α`. Suppose a truth-table
polynomial-time algorithm always returns an integer within `α(T)` …".

Quantified choices in that order: `δ` (from `hETH`, through the admitted
`ETHTailActualContradiction.eth_forbids_actual_source_table_solver` via the admitted
`Unit4Shell.eth_forbids_main_arm`, which also discharges malformed and small inputs); the
rational `η` with `0 < η < δ` (`ε = η`); the cited source records `S D B` (parametric: D-B1/D-B2
stay open author decisions); the constant `c` (hence `L = ETHTailGrowth.repetitions c (2^e) e`);
H-B2 (`PhysicalLevelRun.HB2Physical`, exact form, the one named table-side hypothesis); the
allowance `α = FinalPadding.allowance L` is fixed before the hypothetical estimator; then the
actual `EncodedETHTail.PolynomialApproximation α` is refuted. The small-`n` / `L n = 0` inputs
are handled by the shell's threshold `N0 = max 1 Nr`, with `Nr` from the admitted
`SlowClock.repetitions_unbounded` on the admitted `CutoffBitMachine.actualClock_terminates`.
-/

namespace EthInapproximability.CurrentPaper.Unit4Clock

open EncodedETHSource EncodedETHSourceComposition EffectiveIteration

/-- **`thm:main` (CP-ETH), consumer form, hypotheses hETH and H-B2 only** (plus the choice
condition `hsource` on `c`). -/
theorem eth_forbids_approximation (hETH : EncodedETHTail.ETH) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ η : ℚ, 0 < η → (η : ℝ) < δ →
      ∀ (S : Sparsification η) (D : DinurReduction)
        (B : BOTReduction (booleanOccurrence D)) (c : ℕ),
        2 ^ 44 * (B.degreeBound : ℚ) / sourceGap D B ≤ c →
        PhysicalLevelRun.HB2Physical c (2 ^ sourceSizeExponent S D B)
          (sourceSizeExponent S D B) B.degreeBound (sourceGap D B) →
        ¬ EncodedETHTail.PolynomialApproximation
          (FinalPadding.allowance (ETHTailGrowth.repetitions c (2 ^ sourceSizeExponent S D B)
            (sourceSizeExponent S D B))) := by
  obtain ⟨δ, hδ, hforbid⟩ := Unit4Shell.eth_forbids_main_arm hETH
  refine ⟨δ, hδ, fun η hη hηδ S D B c hsource hB2 happrox => ?_⟩
  obtain ⟨Mmain, C, Bx, Dx, harm⟩ := main_arm_budget S D B c hsource hB2 happrox
  obtain ⟨Nr, hNr⟩ := SlowClock.repetitions_unbounded
    (CutoffBitMachine.actualClock c (2 ^ sourceSizeExponent S D B) (sourceSizeExponent S D B))
    (CutoffBitMachine.actualClock_terminates c (2 ^ sourceSizeExponent S D B)
      (sourceSizeExponent S D B)) 1
  have hη0 : (0 : ℝ) ≤ (η : ℝ) := by exact_mod_cast hη.le
  apply hforbid (η : ℝ) hη0 hηδ c (2 ^ sourceSizeExponent S D B) (sourceSizeExponent S D B)
    (max 1 Nr) Bx C Dx Mmain (le_max_left _ _)
  intro f hf hN
  have hn : 1 ≤ f.variables := le_trans (le_max_left _ _) hN
  have hk : 1 ≤ ETHTailGrowth.repetitions c (2 ^ sourceSizeExponent S D B)
      (sourceSizeExponent S D B) f.variables := hNr _ (le_trans (le_max_right _ _) hN)
  exact harm ⟨f, hf⟩ hn hk

/-- The same with `c` chosen (as in the source, "fix the resulting … repetition function"):
only hETH and H-B2 remain as hypotheses. -/
theorem eth_forbids_approximation_choose_c (hETH : EncodedETHTail.ETH) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ η : ℚ, 0 < η → (η : ℝ) < δ →
      ∀ (S : Sparsification η) (D : DinurReduction)
        (B : BOTReduction (booleanOccurrence D)),
        ∃ c : ℕ, 2 ^ 44 * (B.degreeBound : ℚ) / sourceGap D B ≤ c ∧
          (PhysicalLevelRun.HB2Physical c (2 ^ sourceSizeExponent S D B)
            (sourceSizeExponent S D B) B.degreeBound (sourceGap D B) →
          ¬ EncodedETHTail.PolynomialApproximation
            (FinalPadding.allowance (ETHTailGrowth.repetitions c
              (2 ^ sourceSizeExponent S D B) (sourceSizeExponent S D B)))) := by
  obtain ⟨δ, hδ, h⟩ := eth_forbids_approximation hETH
  exact ⟨δ, hδ, fun η hη hηδ S D B =>
    ⟨⌈2 ^ 44 * (B.degreeBound : ℚ) / sourceGap D B⌉₊, Nat.le_ceil _,
      h η hη hηδ S D B _ (Nat.le_ceil _)⟩⟩

end EthInapproximability.CurrentPaper.Unit4Clock
