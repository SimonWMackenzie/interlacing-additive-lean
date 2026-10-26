import Paper2.SubexpTape
import Paper2.AModelETH

/-!
# Paper A (lock v12), lane `owner:a-eth-1`, segment 2: randomized sparse ETH in the effective carrier

Lock v12 `sections/06-reduction.tex:95-102` (`def:reth`):
"Randomized sparse ETH asserts that, for some fixed constant $c_s$, there is no bounded-error
randomized algorithm deciding $3$-SAT on $N$ variables and at most $c_sN$ clauses in worst-case
time $2^{o(N)}$. The sparse source assumption is made directly; no deterministic ETH assumption
is being silently extended to randomized algorithms."

Author decisions (`AUTHOR_DECISIONS_2026-09-27.md`):
* **D-A6**: "The DRAFT `RandomizedSparseETH` shape: exists c_s; no randomized decider with error
  <= 1/3 on well-formed 3-CNF inputs with clauses <= c_s N, with time <= 2^(eps N) (|input| + 1)^(O(1))
  for every eps > 0 eventually (promise form, explicit polynomial factor)."
* **D-A2**: "(a) Paper B's `EncodedCNF.Language`."
* **D-A1** with ROOT DECISION R19: the carrier is the effective `SubexpTape.Algorithm`.

The formal reading is literally the admitted `AModel.RandomizedSparseETH` (lane a-model-1) with
the carrier replaced: `N` = `EncodedETHTail.variableCount`, clauses = `AModel.cnfClauseCount`,
promise = `AModel.WellFormedCNF`, error `1/3`, and for every `ε > 0` constants `C d N₀` with
worst-case (every-tape) time `≤ C·⌈2^{εN}⌉·(|input|+1)^d` for `N ≥ N₀` on the promise inputs.

Relations proved here:
* `prefix_implies_effective`: the admitted prefix-model assumption `AModel.RandomizedSparseETH`
  implies the effective one (every effective algorithm is a prefix algorithm, `toPrefix`, same
  machine, clock and probabilities);
* `draft_implies_effective`: the admitted DRAFT shape implies it (via `AModel.draft_implies_prefix`);
* `not_prefix_of_not_effective`, `not_draft_of_not_effective`: the contrapositives, i.e. refuting
  the effective assumption refutes both older ones. A class-level T24/T03 conclusion
  `¬ RandomizedSparseETH_effective` is therefore the STRONGEST of the three.

The converse directions (effective ⇒ prefix, effective ⇒ DRAFT) are NOT proved and are not
expected to be provable: the older carriers allow tape lengths that are arbitrary (possibly
uncomputable) functions of the input length (prefix) or of the whole input (DRAFT). By R19 the
DRAFT class `InBPP` contains every language; such advice-bearing algorithms are excluded by the
older assumptions but not by the effective one, so the effective assumption is logically weaker.
No Lean refutation of the converse is claimed.

No ledger row is closed.
-/

noncomputable section

namespace Paper2.AEth

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedComplexity

/-- The D-A6 promise at density `cs`: a valid-formula encoding with at most `cs·N` clauses. -/
def SparsePromise (cs : ℕ) (input : List Bool) : Prop :=
  Paper2.AModel.WellFormedCNF input ∧
    Paper2.AModel.cnfClauseCount input ≤ cs * EncodedETHTail.variableCount input

/-- **D-A6 decision at density `cs` in the effective carrier** (lock `def:reth`, "a bounded-error
randomized algorithm deciding $3$-SAT on $N$ variables and at most $c_sN$ clauses in worst-case
time $2^{o(N)}$"): error `1/3` on every promise input, and for every `ε > 0` the worst-case clock
is `≤ C·⌈2^{εN}⌉·(|input|+1)^d` on the promise inputs with `N ≥ N₀`. -/
def SparseDecider (cs : ℕ) (A : SubexpTape.Algorithm) : Prop :=
  (∀ input, Paper2.AModel.WellFormedCNF input →
    Paper2.AModel.cnfClauseCount input ≤ cs * EncodedETHTail.variableCount input →
    (input ∈ EncodedCNF.Language → 1 - 1 / 3 ≤ A.prob input (· = [true])) ∧
    (input ∉ EncodedCNF.Language → A.prob input (· = [true]) ≤ 1 / 3)) ∧
  ∀ ε : ℝ, 0 < ε → ∃ C d N₀ : ℕ, ∀ input, Paper2.AModel.WellFormedCNF input →
    Paper2.AModel.cnfClauseCount input ≤ cs * EncodedETHTail.variableCount input →
    N₀ ≤ EncodedETHTail.variableCount input →
    A.time input ≤ C * ⌈(2 : ℝ) ^ (ε * EncodedETHTail.variableCount input)⌉₊ *
      (input.length + 1) ^ d

/-- **D-A6, randomized sparse ETH in the effective carrier** (lock `06-reduction.tex:95-98`,
"for some fixed constant $c_s$, there is no bounded-error randomized algorithm deciding $3$-SAT on
$N$ variables and at most $c_sN$ clauses in worst-case time $2^{o(N)}$"; R19 effective tape). -/
def RandomizedSparseETH_effective : Prop :=
  ∃ cs : ℕ, ¬ ∃ A : SubexpTape.Algorithm, SparseDecider cs A

/-- Unfolded, the definition is the admitted `AModel.RandomizedSparseETH` shape with the
carrier `SubexpTape.Algorithm`. -/
theorem effective_iff :
    RandomizedSparseETH_effective ↔ ∃ cs : ℕ, ¬ ∃ A : SubexpTape.Algorithm,
      (∀ input, Paper2.AModel.WellFormedCNF input →
        Paper2.AModel.cnfClauseCount input ≤ cs * EncodedETHTail.variableCount input →
        (input ∈ EncodedCNF.Language → 1 - 1 / 3 ≤ A.prob input (· = [true])) ∧
        (input ∉ EncodedCNF.Language → A.prob input (· = [true]) ≤ 1 / 3)) ∧
      ∀ ε : ℝ, 0 < ε → ∃ C d N₀ : ℕ, ∀ input, Paper2.AModel.WellFormedCNF input →
        Paper2.AModel.cnfClauseCount input ≤ cs * EncodedETHTail.variableCount input →
        N₀ ≤ EncodedETHTail.variableCount input →
        A.time input ≤ C * ⌈(2 : ℝ) ^ (ε * EncodedETHTail.variableCount input)⌉₊ *
          (input.length + 1) ^ d := Iff.rfl

/-- **The admitted prefix-model assumption implies the effective one.** -/
theorem prefix_implies_effective (h : Paper2.AModel.RandomizedSparseETH) :
    RandomizedSparseETH_effective := by
  obtain ⟨cs, hno⟩ := h
  refine ⟨cs, ?_⟩
  rintro ⟨A, hcorr, htime⟩
  exact hno ⟨A.toPrefix, hcorr, htime⟩

/-- **The admitted DRAFT shape (D-A2/D-A6 parameters) implies the effective assumption.** -/
theorem draft_implies_effective
    (h : Paper2.Unit4Shell.Definitions.RandomizedSparseETH EncodedCNF.Language
      Paper2.AModel.WellFormedCNF EncodedETHTail.variableCount Paper2.AModel.cnfClauseCount
      (1 / 3) true) :
    RandomizedSparseETH_effective :=
  prefix_implies_effective (Paper2.AModel.draft_implies_prefix h)

/-- Refuting the effective assumption refutes the prefix-model one. -/
theorem not_prefix_of_not_effective (h : ¬ RandomizedSparseETH_effective) :
    ¬ Paper2.AModel.RandomizedSparseETH :=
  fun h' => h (prefix_implies_effective h')

/-- Refuting the effective assumption refutes the DRAFT one. -/
theorem not_draft_of_not_effective (h : ¬ RandomizedSparseETH_effective) :
    ¬ Paper2.Unit4Shell.Definitions.RandomizedSparseETH EncodedCNF.Language
      Paper2.AModel.WellFormedCNF EncodedETHTail.variableCount Paper2.AModel.cnfClauseCount
      (1 / 3) true :=
  fun h' => h (draft_implies_effective h')

/-- The shape of a refutation: `¬ RandomizedSparseETH_effective` holds iff for EVERY density
`cs` there is an effective sparse decider. -/
theorem not_effective_iff :
    ¬ RandomizedSparseETH_effective ↔ ∀ cs : ℕ, ∃ A : SubexpTape.Algorithm, SparseDecider cs A := by
  unfold RandomizedSparseETH_effective
  constructor
  · intro h cs
    by_contra hc
    exact h ⟨cs, hc⟩
  · rintro h ⟨cs, hc⟩
    exact hc (h cs)

/-- A decider at a larger density is a decider at every smaller density. -/
theorem sparseDecider_mono {cs cs' : ℕ} (h : cs ≤ cs') {A : SubexpTape.Algorithm}
    (hA : SparseDecider cs' A) : SparseDecider cs A := by
  obtain ⟨hcorr, htime⟩ := hA
  refine ⟨fun input h1 h2 => hcorr input h1 (le_trans h2 (Nat.mul_le_mul_right _ h)),
    fun ε hε => ?_⟩
  obtain ⟨C, d, N₀, hC⟩ := htime ε hε
  exact ⟨C, d, N₀, fun input h1 h2 h3 =>
    hC input h1 (le_trans h2 (Nat.mul_le_mul_right _ h)) h3⟩

end Paper2.AEth

end

#print axioms Paper2.AEth.effective_iff
#print axioms Paper2.AEth.prefix_implies_effective
#print axioms Paper2.AEth.draft_implies_effective
#print axioms Paper2.AEth.not_prefix_of_not_effective
#print axioms Paper2.AEth.not_draft_of_not_effective
#print axioms Paper2.AEth.not_effective_iff
#print axioms Paper2.AEth.sparseDecider_mono
