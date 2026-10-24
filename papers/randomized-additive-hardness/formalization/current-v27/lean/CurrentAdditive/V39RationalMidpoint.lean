import CurrentAdditive.GeneralRationalEndpoint

/-!
Selected v39, `models.tex:20-25` and `alternation.tex:yao:comparison`.
The threshold is a binary rational; the estimator's numerical output need
not be dyadic, computably decoded, or comparable with another output.
The inherited RationalComparator and RationalCodeAdapter physically compare
every output word on valid threshold headers, with all-word polynomial time.
This file reuses their fixed 147-comparison machine without changing it.
-/

noncomputable section

open Classical

namespace CurrentAdditive.V39RationalMidpoint

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedCommunication
open CurrentAdditive.ModelEndpointReview
open CurrentAdditive.ModelEndpointReview.RationalEndpoint
open Paper2 Paper2.Yao Paper2.YaoBppDraft

/-- The four measures are the actual strict protocol costs, not four
unconstrained cost functions. Validity supplies nonempty indexed inputs. -/
theorem four_model_comparison (μ : YaoMeasure) (i : Instance) (_hi : i.Valid) :
    |(μ.eval i : ℝ) - (Dalt .alice
      (ProtocolVerifier.tableGame i.rows i.cols i.table) : ℝ)| ≤ 2 := by
  obtain ⟨hl, hr⟩ := measure_window μ i
  have hlR : (Dalt .alice
      (ProtocolVerifier.tableGame i.rows i.cols i.table) : ℝ) ≤ (μ.eval i : ℝ) + 2 := by
    exact_mod_cast hl
  have hrR : (μ.eval i : ℝ) ≤ (Dalt .alice
      (ProtocolVerifier.tableGame i.rows i.cols i.table) : ℝ) + 1 := by
    exact_mod_cast hr
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- At the exact fixed midpoint B+k/2, the existing physical machine gives
error at most 1/100 for every permitted numerical output representation.
The only numerical operation is comparison with that same rational.
The all-output comparator clock is inherited from E.comparator.physical. -/
theorem fixed_midpoint_law {μ : YaoMeasure} {u : ℝ}
    (E : AllRationalEstimator μ u) (hu : 0 ≤ u)
    (i : Instance) (hi : i.Valid) (B k : ℕ)
    (hgap : 2 * (u + 2) < (k : ℝ)) :
    (Dalt .alice (ProtocolVerifier.tableGame i.rows i.cols i.table) ≤ B →
      99 / 100 ≤ E.classifier.prob
        (natField (2 * B + k) ++ AModel.matrixWord i.rows i.cols i.table) (· = [true])) ∧
    (B + k ≤ Dalt .alice (ProtocolVerifier.tableGame i.rows i.cols i.table) →
      E.classifier.prob
        (natField (2 * B + k) ++ AModel.matrixWord i.rows i.cols i.table) (· = [true]) ≤ 1 / 100) := by
  let rest := AModel.matrixWord i.rows i.cols i.table
  let w := natField (2 * B + k) ++ rest
  let c := μ.eval i
  have hk : 4 ≤ k := by
    have h : (4 : ℝ) ≤ k := by linarith
    exact_mod_cast h
  have hgap' : 2 * u < ((k - 4 : ℕ) : ℝ) := by
    rw [Nat.cast_sub hk]
    push_cast
    linarith
  have hmid : ((2 * B + k : ℕ) : ℝ) / 2 =
      ((B + 2 : ℕ) : ℝ) + ((k - 4 : ℕ) : ℝ) / 2 := by
    rw [Nat.cast_sub hk]
    push_cast
    ring
  have hjudge : ∀ out, E.comparator.judgeBit w out =
      decide (MedianOwner.Below (fun out => some (E.value out))
        (((B + 2 : ℕ) : ℝ) + ((k - 4 : ℕ) : ℝ) / 2) out) := by
    intro out
    have h := E.comparator.judge_header (2 * B + k) rest out
    rw [hmid] at h
    simpa [w, MedianOwner.Below] using h
  have hacc := E.header_accuracy (2 * B + k) rest c
    (YaoSelected.target_matrix μ i hi)
  obtain ⟨hl, hr⟩ := measure_window μ i
  constructor
  · intro hD
    have hc : c ≤ B + 2 := by dsimp [c]; omega
    rw [E.classifier_prob]
    apply medAlgJudge_yes (dec := fun out => some (E.value out))
      (c := c) (a := u) (B := B + 2) (k := k - 4)
    · exact hgap'
    · exact hjudge
    · exact hacc
    · exact hc
  · intro hD
    have hc : B + 2 + (k - 4) ≤ c := by dsimp [c]; omega
    rw [E.classifier_prob]
    apply medAlgJudge_no (dec := fun out => some (E.value out))
      (c := c) (a := u) (B := B + 2) (k := k - 4)
    · exact hgap'
    · exact hjudge
    · exact hacc
    · exact hc

/-- Literal monomial tape length for the already constructed 147-run
machine; a deterministic table map can use SelectedTape.pullback. -/
theorem comparison_tape {μ : YaoMeasure} {u : ℝ}
    (E : AllRationalEstimator μ u) (n : ℕ) :
    E.median.tapeLength n =
      (147 * (HeaderStrip.selectedEstimator E.estimator).cR) *
        (n + 1) ^ (HeaderStrip.selectedEstimator E.estimator).dR := by
  simpa [Unit4Shell.Amplification.reps] using E.median_tape n

#print axioms four_model_comparison
#print axioms fixed_midpoint_law
#print axioms comparison_tape

end CurrentAdditive.V39RationalMidpoint
