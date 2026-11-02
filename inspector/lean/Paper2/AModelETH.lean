import Paper2.AModelPrefix
import EthInapproximability.CurrentPaper.EncodedETHTail
import EthInapproximability.CurrentPaper.EncodedETHSource

/-!
# Paper A (lock v12), lane `owner:a-model-1`, segment 3: randomized sparse ETH (D-A6) in the prefix model

Author decisions of 27 September 2026 (`AUTHOR_DECISIONS_2026-09-27.md`):
* **D-A6**: "The DRAFT `RandomizedSparseETH` shape: exists c_s; no randomized decider with error
  <= 1/3 on well-formed 3-CNF inputs with clauses <= c_s N, with time <= 2^(eps N) (|input| + 1)^(O(1))
  for every eps > 0 eventually (promise form, explicit polynomial factor)."
* **D-A2**: "(a) Paper B's `EncodedCNF.Language`."
* **D-A1 (c)**: the prefix model (`AModelPrefix.PrefixAlgorithm`).

Lock v12 text (`versions/2026-09-22-protocol-labels-v12/source/sections/06-reduction.tex:95-102`):
"Randomized sparse ETH asserts that, for some fixed constant $c_s$, there is no bounded-error
randomized algorithm deciding $3$-SAT on $N$ variables and at most $c_sN$ clauses in worst-case
time $2^{o(N)}$. ... The sparse source assumption is made directly; no deterministic ETH assumption
is being silently extended to randomized algorithms."

Formal reading (D-A6 sub-choices a1-a4 of BRIEF section 2): `N` is the unary variable count
`EncodedETHTail.variableCount`; the clause count is the decoded clause-list length; the promise is
"a valid-formula encoding with at most `c_s N` clauses" (the well-formedness predicate of the
admitted consumer `AEndpoint.T24_class_of_U18`); error `1/3`; "time `2^{o(N)}`" is ONE algorithm
with, for every `ε > 0`, constants `C, d, N₀` and worst-case time
`≤ C·⌈2^{εN}⌉·(|input|+1)^d` for `N ≥ N₀` (explicit polynomial factor). The density constant is
a natural number; since the assumption for `c_s` implies it for every larger constant, this is
equivalent to a real constant (observation, not a Lean theorem).

Relation to the DRAFT shape: `draft_implies_prefix` (the admitted DRAFT
`Definitions.RandomizedSparseETH` at `EncodedCNF.Language`, error `1/3`, `withPoly = true`
implies the prefix-model assumption, since every prefix algorithm is a DRAFT algorithm), and
`prefix_implies_draft_lengthTape` (the prefix-model assumption excludes every DRAFT algorithm whose
tape length is a function of the input length). No ledger row is closed.
-/

namespace Paper2.AModel

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedComplexity
open Paper2 Paper2.FiniteLaw
open Paper2.Unit4Shell.Definitions

/-- D-A6 clause count: the length of the decoded clause list (`0` off the codec). -/
def cnfClauseCount (input : List Bool) : ℕ :=
  match EncodedCNF.decode input with
  | none => 0
  | some f => f.clauses.length

/-- D-A6/D-A2 promise: the input is the encoding of a valid formula (the well-formedness
predicate of the admitted consumer `AEndpoint.T24_class_of_U18`). -/
def WellFormedCNF (input : List Bool) : Prop :=
  ∃ Φ : EncodedETHSource.ValidFormula, EncodedCNF.encode Φ.val = input

theorem wellFormedCNF_iff (input : List Bool) :
    WellFormedCNF input ↔ ∃ f, EncodedCNF.decode input = some f := by
  constructor
  · rintro ⟨Φ, rfl⟩
    exact ⟨Φ.val, EncodedCNF.decode_encode Φ.val Φ.property⟩
  · rintro ⟨f, hf⟩
    exact ⟨⟨f, EncodedCNF.decode_valid hf⟩, EncodedCNF.decode_sound hf⟩

/-- **D-A6, randomized sparse ETH in the D-A1 prefix model** (lock `06-reduction.tex:95-98`,
"for some fixed constant $c_s$, there is no bounded-error randomized algorithm deciding $3$-SAT on
$N$ variables and at most $c_sN$ clauses in worst-case time $2^{o(N)}$"): there is `c_s` such that
no prefix algorithm (a) decides `EncodedCNF.Language` with error `1/3` on every valid-formula
encoding with at most `c_s·N` clauses (promise form) and (b) for every `ε > 0` has worst-case
every-tape time `≤ C·⌈2^{εN}⌉·(|input|+1)^d` on those inputs with `N ≥ N₀`. -/
def RandomizedSparseETH : Prop :=
  ∃ cs : ℕ, ¬ ∃ A : PrefixAlgorithm,
    (∀ input, WellFormedCNF input →
      cnfClauseCount input ≤ cs * EncodedETHTail.variableCount input →
      (input ∈ EncodedCNF.Language → 1 - 1 / 3 ≤ A.prob input (· = [true])) ∧
      (input ∉ EncodedCNF.Language → A.prob input (· = [true]) ≤ 1 / 3)) ∧
    ∀ ε : ℝ, 0 < ε → ∃ C d N₀ : ℕ, ∀ input, WellFormedCNF input →
      cnfClauseCount input ≤ cs * EncodedETHTail.variableCount input →
      N₀ ≤ EncodedETHTail.variableCount input →
      A.time input ≤ C * ⌈(2 : ℝ) ^ (ε * EncodedETHTail.variableCount input)⌉₊ *
        (input.length + 1) ^ d

/-- The admitted DRAFT shape at the D-A2/D-A6 parameters implies the prefix-model assumption. -/
theorem draft_implies_prefix
    (h : Paper2.Unit4Shell.Definitions.RandomizedSparseETH EncodedCNF.Language WellFormedCNF
      EncodedETHTail.variableCount cnfClauseCount (1 / 3) true) :
    RandomizedSparseETH := by
  obtain ⟨cs, hno⟩ := h
  refine ⟨cs, ?_⟩
  rintro ⟨A, hcorr, htime⟩
  apply hno
  refine ⟨A.toDraft, hcorr, fun ε hε => ?_⟩
  obtain ⟨C, d, N₀, hC⟩ := htime ε hε
  refine ⟨C, d, N₀, fun input h1 h2 h3 => ?_⟩
  rw [if_pos rfl]
  exact hC input h1 h2 h3

/-- The prefix-model assumption excludes every DRAFT algorithm whose tape length is a function
of the input length (via `ofDraft`, same machine, time and probabilities). -/
theorem prefix_implies_draft_lengthTape (h : RandomizedSparseETH) :
    ∃ cs : ℕ, ¬ ∃ A : RandomizedAlgorithm,
      (∃ R : ℕ → ℕ, ∀ input, A.tapeLength input = R input.length) ∧
      (∀ input, WellFormedCNF input →
        cnfClauseCount input ≤ cs * EncodedETHTail.variableCount input →
        (input ∈ EncodedCNF.Language → 1 - 1 / 3 ≤ A.prob input (· = [true])) ∧
        (input ∉ EncodedCNF.Language → A.prob input (· = [true]) ≤ 1 / 3)) ∧
      ∀ ε : ℝ, 0 < ε → ∃ C d N₀ : ℕ, ∀ input, WellFormedCNF input →
        cnfClauseCount input ≤ cs * EncodedETHTail.variableCount input →
        N₀ ≤ EncodedETHTail.variableCount input →
        A.time input ≤ C * ⌈(2 : ℝ) ^ (ε * EncodedETHTail.variableCount input)⌉₊ *
          (input.length + 1) ^ d := by
  obtain ⟨cs, hno⟩ := h
  refine ⟨cs, ?_⟩
  rintro ⟨A, ⟨R, hR⟩, hcorr, htime⟩
  apply hno
  refine ⟨ofDraft A R hR, fun input h1 h2 => ?_, htime⟩
  simp only [prob_ofDraft]
  exact hcorr input h1 h2

end Paper2.AModel

#print axioms Paper2.AModel.wellFormedCNF_iff
#print axioms Paper2.AModel.draft_implies_prefix
#print axioms Paper2.AModel.prefix_implies_draft_lengthTape
