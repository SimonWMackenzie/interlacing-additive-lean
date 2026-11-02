import EthInapproximability.CurrentPaper.U4EthMain
import EthInapproximability.CurrentPaper.ClockedPadding
import EthInapproximability.CurrentPaper.CutoffBitMachine

/-!
# `thm:main` of lock v8, assembled from `U4EthMain` (lane owner:b-eth-endpoint-1, segment 1)

Lock v8 (`papers/interlacing-np-eth/versions/2026-09-22-complete-replacement-v8/source/sections/`,
MANIFEST SHA-256 of `01-introduction.tex` = `B195A0B0…2AC0`, of `06-eth.tex` = `3907A08E…64C5`).

`01-introduction.tex:71-81`, verbatim:

    \begin{theorem}[ETH inapproximability]
    \label{thm:main}
    Assume the Exponential Time Hypothesis. There is a total computable,
    nondecreasing function \(\alpha:\mathbb N\to\mathbb N\), with
    \(\alpha(N)\to\infty\), for which no algorithm running in time polynomial
    in \(\abs{\TT(f)}\) always outputs an integer \(A(f)\) satisfying
    \[
      \abs{A(f)-\comp f}
         \le \alpha\!\left(\abs{\TT(f)}\right).
    \]
    \end{theorem}

`06-eth.tex:190-196` fixes `α(T) = ⌊L(⌊log₂ max{T,2}⌋)/4⌋`, which is literally the admitted
`FinalPadding.allowance L T = L (Nat.log 2 (max T 2)) / 4`, with `L` the admitted
`ETHTailGrowth.repetitions c A d` (= `SlowClock.repetitions (CutoffBitMachine.actualClock c A d)`).
`06-eth.tex:204-207` fixes the order of choices: `δ_ETH` from ETH, a rational `0 < ε < δ_ETH`,
then the source algorithms (the cited records `S D B`), `L`, the construction and `α`, all before
the hypothetical approximation algorithm.

The reading of "no algorithm running in time polynomial in `|TT(f)|` always outputs …" is the
admitted `EncodedETHTail.PolynomialApproximation` (one polytime bit machine on raw square
row-major tables of length `2^(2p)`), negated.

Author decisions kept OPEN (never chosen here):
* D-B1 (the formal meaning of "total computable"): a predicate parameter `Computable` with the
  hypothesis `hComp` that it holds of every allowance of the admitted family; `thm_main_core`
  states the endpoint without it, exposing the literal formula of `α`.
* D-B2 (the binder shape of the cited-source hypotheses): `thm_main` takes the records as data
  (`Srec : ∀ η, 0 < η → Sparsification η`, `D`, `B`); `thm_main_nonempty` takes the unit-4 map's
  proposed `Nonempty` shape. Both are offered; the author selects.

H-B2 is the ONE named table-side hypothesis, `HB2Supply S D B`: for every `c` meeting the
source's choice condition `2^44 Δ / γ ≤ c`, the admitted interface
`PhysicalLevelRun.HB2Physical c (2^e) e Δ γ` (`Δ = B.degreeBound`, `γ = sourceGap D B`,
`e = sourceSizeExponent S D B`). This is the conclusion shape of the level lanes' composed
theorem (`ClockB.hb2_physical_source` of lane level-10 concludes `HB2Physical c A d Δ γ` from
`hΔ hγ hγone hsource` and per-instance premises; its `hΔ hγ hγone` are discharged here by
`B.degreeBound_pos`, `source_gap_pos`, `source_gap_le_one`, see segment 3).
-/

namespace EthInapproximability.CurrentPaper.BEthEndpoint

open EncodedETHSource EncodedETHSourceComposition

/-- **H-B2** at fixed cited records: `HB2Physical` at the fixed records for every source constant
`c` meeting the choice condition of the source. -/
def HB2Supply {η : ℚ} (S : Sparsification η) (D : DinurReduction)
    (B : BOTReduction (booleanOccurrence D)) : Prop :=
  ∀ c : ℕ, 2 ^ 44 * (B.degreeBound : ℚ) / sourceGap D B ≤ c →
    PhysicalLevelRun.HB2Physical c (2 ^ sourceSizeExponent S D B) (sourceSizeExponent S D B)
      B.degreeBound (sourceGap D B)

/-- The allowance is nondecreasing (admitted `ClockedPadding.allowance_monotone` on the actual
clock; `ETHTailGrowth.repetitions c A d` is definitionally its `SlowClock.repetitions`). -/
theorem allowance_monotone (c A d : ℕ) :
    Monotone (FinalPadding.allowance (ETHTailGrowth.repetitions c A d)) :=
  ClockedPadding.allowance_monotone (CutoffBitMachine.actualClock c A d)

/-- The allowance tends to infinity (admitted `ClockedPadding.allowance_tendsto_atTop` with the
admitted termination `CutoffBitMachine.actualClock_terminates`). -/
theorem allowance_tendsto (c A d : ℕ) :
    Filter.Tendsto (FinalPadding.allowance (ETHTailGrowth.repetitions c A d))
      Filter.atTop Filter.atTop :=
  ClockedPadding.allowance_tendsto_atTop (CutoffBitMachine.actualClock c A d)
    (CutoffBitMachine.actualClock_terminates c A d)

/-- Explicit form, choices in source order: `δ` from ETH (inside `U4EthMain`), a rational
`0 < η < δ`, the records `Srec η`, `D`, `B`, then `c` (hence `L`), then the allowance; the actual
`PolynomialApproximation` at that allowance is refuted. -/
theorem thm_main_explicit (hETH : EncodedETHTail.ETH)
    (Srec : ∀ η : ℚ, 0 < η → Sparsification η) (D : DinurReduction)
    (B : BOTReduction (booleanOccurrence D))
    (hB2 : ∀ (η : ℚ) (hη : 0 < η), HB2Supply (Srec η hη) D B) :
    ∃ (η : ℚ) (hη : 0 < η) (c : ℕ),
      2 ^ 44 * (B.degreeBound : ℚ) / sourceGap D B ≤ c ∧
      ¬ EncodedETHTail.PolynomialApproximation
        (FinalPadding.allowance (ETHTailGrowth.repetitions c
          (2 ^ sourceSizeExponent (Srec η hη) D B) (sourceSizeExponent (Srec η hη) D B))) := by
  obtain ⟨δ, hδ, h⟩ := Unit4Clock.eth_forbids_approximation_choose_c hETH
  obtain ⟨η, hη0, hηδ⟩ := exists_rat_btwn hδ
  have hη : (0 : ℚ) < η := by exact_mod_cast hη0
  obtain ⟨c, hc, hnot⟩ := h η hη hηδ (Srec η hη) D B
  exact ⟨η, hη, c, hc, hnot (hB2 η hη c hc)⟩

/-- **`thm:main` without D-B1**: the allowance is literally the paper's formula
`FinalPadding.allowance (ETHTailGrowth.repetitions c A d)` for constants fixed before any
estimator; it is nondecreasing, unbounded, and no truth-table-polynomial algorithm approximates
communication complexity within it. -/
theorem thm_main_core (hETH : EncodedETHTail.ETH)
    (Srec : ∀ η : ℚ, 0 < η → Sparsification η) (D : DinurReduction)
    (B : BOTReduction (booleanOccurrence D))
    (hB2 : ∀ (η : ℚ) (hη : 0 < η), HB2Supply (Srec η hη) D B) :
    ∃ α : ℕ → ℕ, (∃ c A d : ℕ, α = FinalPadding.allowance (ETHTailGrowth.repetitions c A d)) ∧
      Monotone α ∧ Filter.Tendsto α Filter.atTop Filter.atTop ∧
      ¬ EncodedETHTail.PolynomialApproximation α := by
  obtain ⟨η, hη, c, _, hnot⟩ := thm_main_explicit hETH Srec D B hB2
  exact ⟨_, ⟨c, _, _, rfl⟩, allowance_monotone _ _ _, allowance_tendsto _ _ _, hnot⟩

/-- **`thm:main` (lock v8, `01-introduction.tex:71-81`)**, D-B1 as the predicate parameter
`Computable` (with `hComp` on the admitted allowance family), D-B2 in the records-as-data shape,
H-B2 the one named table-side hypothesis. -/
theorem thm_main (Computable : (ℕ → ℕ) → Prop)
    (hComp : ∀ c A d : ℕ, Computable (FinalPadding.allowance (ETHTailGrowth.repetitions c A d)))
    (hETH : EncodedETHTail.ETH)
    (Srec : ∀ η : ℚ, 0 < η → Sparsification η) (D : DinurReduction)
    (B : BOTReduction (booleanOccurrence D))
    (hB2 : ∀ (η : ℚ) (hη : 0 < η), HB2Supply (Srec η hη) D B) :
    ∃ α : ℕ → ℕ, Computable α ∧ Monotone α ∧ Filter.Tendsto α Filter.atTop Filter.atTop ∧
      ¬ EncodedETHTail.PolynomialApproximation α := by
  obtain ⟨α, ⟨c, A, d, rfl⟩, hmono, htend, hnot⟩ := thm_main_core hETH Srec D B hB2
  exact ⟨_, hComp c A d, hmono, htend, hnot⟩

/-- **`thm:main`**, D-B2 in the unit-4 map's proposed `Nonempty` binder shape (records chosen by
`Classical.choice` inside the proof, after `δ` and `η`); H-B2 for every record triple. -/
theorem thm_main_nonempty (Computable : (ℕ → ℕ) → Prop)
    (hComp : ∀ c A d : ℕ, Computable (FinalPadding.allowance (ETHTailGrowth.repetitions c A d)))
    (hIPZ : ∀ η : ℚ, 0 < η → Nonempty (Sparsification η))
    (hDinur : Nonempty DinurReduction)
    (hBOT : ∀ k : ℕ, Nonempty (BOTReduction k))
    (hB2 : ∀ (η : ℚ) (S : Sparsification η) (D : DinurReduction)
      (B : BOTReduction (booleanOccurrence D)), HB2Supply S D B)
    (hETH : EncodedETHTail.ETH) :
    ∃ α : ℕ → ℕ, Computable α ∧ Monotone α ∧ Filter.Tendsto α Filter.atTop Filter.atTop ∧
      ¬ EncodedETHTail.PolynomialApproximation α :=
  thm_main Computable hComp hETH (fun η hη => (hIPZ η hη).some) hDinur.some
    (hBOT (booleanOccurrence hDinur.some)).some
    (fun η _ => hB2 η _ hDinur.some (hBOT (booleanOccurrence hDinur.some)).some)

end EthInapproximability.CurrentPaper.BEthEndpoint
