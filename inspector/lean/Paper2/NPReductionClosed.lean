import Paper2.NPTruncRun
import Paper2.A4ClassLemmas
import Paper2.A4DocFix
import Paper2.AEndpoint
import Paper2.AEndpointClass

/-!
# WP-NP (lane `owner:a-np-1`, private, 26 September 2026): `ReductionClosed InNP`

Ledger rows U18 (clause `I:125`, "ReductionClosed InNP") and X06 (clause `I:125`), work
package WP-NP of `ledger-audit-a/LEDGER_AUDIT.md`.

**Main theorem.** `inNP_reductionClosed :
Paper2.Unit4Shell.ClassLemmas.ReductionClosed EthInapproximability.CurrentPaper.EncodedComplexity.InNP`:
the admitted encoded class `InNP` (one fixed deterministic polynomial-time bit machine
checking `pair input witness`, witnesses of length `≤ c·(|input|+1)^d`) is closed under the
admitted polynomial-time many-one reductions `Reduces`.

Construction (no premise, no author decision): for `f : L ≤ K` and a verifier `verify` of `K`
with witness bound `c·(|y|+1)^d`, the new verifier of `L` is
`code ↦ verify (Trunc.result c d f code)`, i.e. on `pair x w` it checks
`verify (pair (f x) (take (c·(|f x|+1)^d) w))`. The truncation to the exact witness bound of
`K` is what makes soundness hold (a verifier of `K` may accept over-long witnesses of
non-members). It is ONE machine, charged on every word (`Trunc.polytime_result`, from the
private `Trunc.machine`), composed with `verify`'s machine by the admitted
`BitMachineComposition.polytime_comp`. The witness bound of `L` is
`c·(cf+1)^d·(|x|+1)^(df·d)`, transported through the admitted `polytime_output_length`
bound `|f x| ≤ cf·(|x|+1)^df`.

**Instantiations.** The admitted consumers `AEndpoint.T02_class_coNP`,
`AEndpoint.T02_coNP_of_U18`, `ClassLemmas.np_eq_coNP_of_hard_mem_coNP`,
`ClassLemmas.coNP_closed_of_NP_closed` (and the `DocFix` copies) are restated with the
`ReductionClosed InNP` premise discharged. The U18 contracts (`OneSidedRejectShape L`,
`U18OneSided`), `DA2 L`, the validity routing and the author decision D-A5 (`NPHard L`) stay
as hypotheses.
-/

namespace NPOwner1

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedComplexity

/-- The exact witness-bound transport through the reduction's output-length bound. -/
theorem bound_transport (c d cf df n m : ℕ) (hm : m ≤ cf * (n + 1) ^ df) :
    c * (m + 1) ^ d ≤ c * (cf + 1) ^ d * (n + 1) ^ (df * d) := by
  have h1 : m + 1 ≤ (cf + 1) * (n + 1) ^ df := by
    have : 1 ≤ (n + 1) ^ df := Nat.one_le_pow _ _ (by omega)
    nlinarith
  calc c * (m + 1) ^ d ≤ c * ((cf + 1) * (n + 1) ^ df) ^ d :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h1 d)
    _ = c * (cf + 1) ^ d * (n + 1) ^ (df * d) := by rw [mul_pow, ← pow_mul]; ring

/-- **WP-NP (U18 `I:125`, X06 `I:125`): `NP` is closed under the banked polynomial-time
many-one reductions.** No premise. -/
theorem inNP_reductionClosed :
    Paper2.Unit4Shell.ClassLemmas.ReductionClosed EncodedComplexity.InNP := by
  intro L K hLK hK
  obtain ⟨f, hf, hfc⟩ := hLK
  obtain ⟨verify, hv, c, d, hvK⟩ := hK
  obtain ⟨cf, df, hflen⟩ := ComplexityReductionClosure.polytime_output_length hf
  refine ⟨fun code => verify (Trunc.result c d f code),
    BitMachineComposition.polytime_comp (Trunc.polytime_result hf c d) hv,
    c * (cf + 1) ^ d, df * d, ?_⟩
  intro input
  rw [hfc input, hvK (f input)]
  constructor
  · rintro ⟨w, hw, hvw⟩
    refine ⟨w, hw.trans (bound_transport c d cf df input.length (f input).length
      (hflen input)), ?_⟩
    simp only [Trunc.result_pair, List.take_of_length_le hw]
    exact hvw
  · rintro ⟨w, -, hvw⟩
    refine ⟨w.take (c * ((f input).length + 1) ^ d), by simp [List.length_take], ?_⟩
    simp only [Trunc.result_pair] at hvw
    exact hvw

/-- `coNP` closure, premise discharged. -/
theorem inCoNP_reductionClosed :
    Paper2.Unit4Shell.ClassLemmas.ReductionClosed Paper2.Unit4Shell.ClassLemmas.InCoNP :=
  Paper2.Unit4Shell.ClassLemmas.coNP_closed_of_NP_closed inNP_reductionClosed

/-- `NP = coNP` from an NP-hard language in `coNP`, premise `ReductionClosed InNP`
discharged (admitted `ClassLemmas.np_eq_coNP_of_hard_mem_coNP`). -/
theorem np_eq_coNP_of_hard_mem_coNP_closed {K : BinaryLanguage} (hK : NPHard K)
    (hmem : Paper2.Unit4Shell.ClassLemmas.InCoNP K) : Paper2.Unit4Shell.ClassLemmas.NPEqCoNP :=
  Paper2.Unit4Shell.ClassLemmas.np_eq_coNP_of_hard_mem_coNP inNP_reductionClosed hK hmem

/-- **T02, class level (second clause), `ReductionClosed InNP` discharged.** From the
one-sided normal form (U18 contract) and `NPHard L` (D-A5): `NPEqCoNP`. Exact reuse of the
admitted `AEndpoint.T02_class_coNP`. -/
theorem T02_class_coNP_closed (L : BinaryLanguage) (hCL : NPHard L)
    (hU18 : Paper2.Unit4Shell.ClassLemmas.OneSidedRejectShape L) :
    Paper2.Unit4Shell.ClassLemmas.NPEqCoNP :=
  Paper2.AEndpoint.T02_class_coNP L inNP_reductionClosed hCL hU18

open EthInapproximability.CurrentPaper.EncodedETHSource
open EthInapproximability.CurrentPaper.EncodedETHSourceComposition

/-- **T02 (second clause) at class level modulo the one-sided U18 contract, with
`ReductionClosed InNP` discharged.** Exact reuse of the admitted `AEndpoint.T02_coNP_of_U18`;
the remaining hypotheses are exactly its own (D-A2 `DA2 L`, validity of members, `a ≥ 0`, the
OPEN `U18OneSided` contract) and D-A5 (`NPHard L`). -/
theorem T02_coNP_of_U18_closed (D : DinurReduction) (B : BOTReduction (booleanOccurrence D))
    (L : BinaryLanguage) (hDA2 : Paper2.AEndpoint.DA2 L)
    (hLvalid : ∀ input ∈ L, ∃ Φ : ValidFormula, EncodedCNF.encode Φ.val = input)
    (a : ℝ) (ha : 0 ≤ a)
    (hU18 : ∃ A reject, Paper2.AEndpoint.U18OneSided D B a (Paper2.AEndpoint.gapOf a) A reject) :
    Paper2.Unit4Shell.ClassLemmas.OneSidedRejectShape L ∧
      (NPHard L → Paper2.Unit4Shell.ClassLemmas.NPEqCoNP) := by
  obtain ⟨h1, h2⟩ := Paper2.AEndpoint.T02_coNP_of_U18 D B L hDA2 hLvalid a ha hU18
  exact ⟨h1, h2 inNP_reductionClosed⟩

end NPOwner1

#print axioms NPOwner1.Trunc.polytime_result
#print axioms NPOwner1.inNP_reductionClosed
#print axioms NPOwner1.inCoNP_reductionClosed
#print axioms NPOwner1.np_eq_coNP_of_hard_mem_coNP_closed
#print axioms NPOwner1.T02_class_coNP_closed
#print axioms NPOwner1.T02_coNP_of_U18_closed
