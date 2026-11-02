import Paper2.A4T10Finite
import Paper2.A4ClassLemmas

/-!
# Unit 4 (Paper A): accurate restatements for reviewer findings D-1 and D-2
# (owner lane `owner:a-unit4-shell-3`)

Private, 26 September 2026. Production universe. The admitted modules `Paper2.A4T10Finite`
and `Paper2.A4ClassLemmas` are NOT edited. Their affected declarations are restated here with
accurate docstrings and proved by exact reuse of the admitted declarations (term-mode
applications of the admitted names; no new mathematics).

* **D-1** (`A4T10Finite.t01_finite_core`, docstring lines 79-84): its NO clause bounds
  `EncodedSelectedOutput.noLanguageProbability`, the probability that the printed instance is
  NOT in `EncodedCommunication.Language`, i.e. (banked `outputBits_language_iff`) the
  probability of `D(M) > budget`. It is NOT the probability of `D(M) ≥ budget + k`, which is
  strictly stronger for `k ≥ 2`, and it does not give the T01 NO clause. The exact T01 NO form
  `Pr[D(M) = budget + k] ≥ 981/1000` is `TotalFiniteConstructorScratch.successProbability`,
  restated below as `t01_finite_no_exact` from the banked `selected_no_success`.
* **D-2** (`A4ClassLemmas` module docstring, lines 15-16): it claims the banked lemma
  `ComplexityReductionClosure.reduces_trans` is reused; no declaration of that module uses it.
  The class lemmas are restated with docstrings that name exactly what each proof uses.

**None of these statements closes a ledger row.**
-/

namespace Paper2.Unit4Shell.DocFix

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedETHSource
open EthInapproximability.CurrentPaper.EncodedETHSourceComposition
open EthInapproximability.CurrentPaper.EncodedComplexity
open Paper2.Unit4Shell.T10Finite

section D1

variable (D : DinurReduction) (B : BOTReduction (booleanOccurrence D))

/-- **Fixed-k T01 finite core (D-1 corrected docstring), HYP on the cited records `D`, `B`.**
For every valid `Φ` and `k ≥ 1`, with the T10 graph of `Φ`, degree bound `B.degreeBound` and
gap `sourceGap D B`: if `Φ` is satisfiable then on EVERY tape of the selected output the
printed instance `outputBits` is in `EncodedCommunication.Language` (equivalently, by the
banked `EncodedSelectedOutput.outputBits_language_iff`, `D(M) ≤ budget`); if `Φ` is
unsatisfiable then `EncodedSelectedOutput.noLanguageProbability ≥ 981/1000`, where
`noLanguageProbability` is the probability, under the experiment's tape law, that the printed
instance is NOT in the language, i.e. that `D(M) > budget`. This NO clause is weaker than
`Pr[D(M) ≥ budget + k]` for `k ≥ 2` and is NOT the T01 NO clause; for the exact form see
`t01_finite_no_exact`. Proof: the admitted `T10Finite.t01_finite_core`, by exact reuse.
Does not close a ledger row. -/
theorem t01_finite_core (Φ : ValidFormula) (k : ℕ) (hk : 1 ≤ k) :
    (EncodedCNF.Satisfiable Φ.val →
      ∀ t : (TotalFiniteConstructorScratch.select (t10_vertices_pos D B Φ)
          (CanonicalEdgeTape.graphEdge (t10Graph D B Φ) (t10Graph_valid D B Φ))
          B.degreeBound (sourceGap D B) k).Tape,
        EncodedSelectedOutput.outputBits (t10_vertices_pos D B Φ)
          (CanonicalEdgeTape.graphEdge (t10Graph D B Φ) (t10Graph_valid D B Φ))
          B.degreeBound (sourceGap D B) k t ∈ EncodedCommunication.Language) ∧
    (¬ EncodedCNF.Satisfiable Φ.val →
      (981 / 1000 : ℝ) ≤ EncodedSelectedOutput.noLanguageProbability (t10_vertices_pos D B Φ)
          (CanonicalEdgeTape.graphEdge (t10Graph D B Φ) (t10Graph_valid D B Φ))
          B.degreeBound (sourceGap D B) k) :=
  T10Finite.t01_finite_core D B Φ k hk

/-- **Exact T01 NO clause on the T10 source (finite), HYP on `D`, `B`.** For every
unsatisfiable valid `Φ` and `k ≥ 1`, the probability that the communication complexity of the
selected table equals `budget + k` exactly
(`TotalFiniteConstructorScratch.successProbability`) is at least `981/1000`. Proof: the
admitted `T10Finite.t10_source` and the banked
`TotalFiniteConstructorScratch.selected_no_success` (the same steps as the NO part of the
admitted `Shells.T01_of_interfaces`). Does not close a ledger row. -/
theorem t01_finite_no_exact (Φ : ValidFormula) (k : ℕ) (hk : 1 ≤ k)
    (hunsat : ¬ EncodedCNF.Satisfiable Φ.val) :
    (981 / 1000 : ℝ) ≤ TotalFiniteConstructorScratch.successProbability
      (t10_vertices_pos D B Φ)
      (CanonicalEdgeTape.graphEdge (t10Graph D B Φ) (t10Graph_valid D B Φ))
      B.degreeBound (sourceGap D B) k := by
  obtain ⟨hm, _, _, hdeg, hloop, _, hno⟩ := t10_source D B Φ
  have h := TotalFiniteConstructorScratch.selected_no_success (t10_vertices_pos D B Φ)
    (CanonicalEdgeTape.graphEdge (t10Graph D B Φ) (t10Graph_valid D B Φ))
    B.degreeBound (sourceGap D B) k hk hloop hdeg (source_gap_pos D B) B.degreeBound_pos hm
    (hno hunsat)
  have hnum : (981 / 1000 : ℝ) ≤ 1 - (1 / 2 : ℝ) ^ 11 := by norm_num
  linarith

end D1

section D2

open Paper2.Unit4Shell.ClassLemmas

/-- **`NP ⊆ C` (D-2 corrected docstring).** For every class `C` closed under the banked
many-one reductions (`ClassLemmas.ReductionClosed C`, a DRAFT definition, D-A4 open) that
contains an NP-hard language `K` (banked `EncodedComplexity.NPHard`), every language in the
banked `EncodedComplexity.InNP` is in `C`. The proof applies the closure hypothesis to the
reduction supplied by `NPHard`; it uses no transitivity lemma (in particular not
`ComplexityReductionClosure.reduces_trans`). Proof: the admitted
`ClassLemmas.np_subset_of_hard_mem`, by exact reuse. Does not close a ledger row. -/
theorem np_subset_of_hard_mem (C : BinaryLanguage → Prop) (hC : ReductionClosed C)
    {K : BinaryLanguage} (hK : NPHard K) (hmem : C K) :
    ∀ L, InNP L → C L :=
  ClassLemmas.np_subset_of_hard_mem C hC hK hmem

/-- **Closure transfers from `NP` to `coNP` (D-2 corrected docstring).** If `InNP` is closed
under the banked reductions then so is the DRAFT `ClassLemmas.InCoNP`; the proof applies the
`NP` closure to the complement reduction `ClassLemmas.reduces_compl` (same function). No
transitivity lemma is used. Proof: the admitted `ClassLemmas.coNP_closed_of_NP_closed`.
Does not close a ledger row. -/
theorem coNP_closed_of_NP_closed (hNP : ReductionClosed InNP) : ReductionClosed InCoNP :=
  ClassLemmas.coNP_closed_of_NP_closed hNP

/-- **`NP = coNP` from an NP-hard language in `coNP` (D-2 corrected docstring).** Given that
`InNP` is closed under the banked reductions (a named machine-level hypothesis, not proved),
an NP-hard `K` in the DRAFT `InCoNP` gives the DRAFT `NPEqCoNP`. The proof uses only
`np_subset_of_hard_mem`, `coNP_closed_of_NP_closed` and `compl_compl`; no transitivity lemma.
Proof: the admitted `ClassLemmas.np_eq_coNP_of_hard_mem_coNP`. Does not close a ledger row. -/
theorem np_eq_coNP_of_hard_mem_coNP (hNP : ReductionClosed InNP)
    {K : BinaryLanguage} (hK : NPHard K) (hmem : InCoNP K) : NPEqCoNP :=
  ClassLemmas.np_eq_coNP_of_hard_mem_coNP hNP hK hmem

/-- **`coRP ⊆ coNP` in the option-generic normal form (D-2 corrected docstring).** The
rejecting tape of the DRAFT `OneSidedRejectShape` is the NP witness for the complement.
Uses no transitivity lemma. Proof: the admitted `ClassLemmas.coNP_of_oneSided`. Does not close
a ledger row. -/
theorem coNP_of_oneSided {L : BinaryLanguage} (h : OneSidedRejectShape L) : InCoNP L :=
  ClassLemmas.coNP_of_oneSided h

end D2

#print axioms t01_finite_core
#print axioms t01_finite_no_exact
#print axioms np_subset_of_hard_mem
#print axioms coNP_closed_of_NP_closed
#print axioms np_eq_coNP_of_hard_mem_coNP
#print axioms coNP_of_oneSided

end Paper2.Unit4Shell.DocFix
