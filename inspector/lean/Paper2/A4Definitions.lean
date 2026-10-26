import Paper2.A4ClassLemmas
import EthInapproximability.CurrentPaper.EncodedCNF
import EthInapproximability.CurrentPaper.BitMachine

/-!
# Unit 4 (Paper A), segment A4-S1: DRAFT definitions package

Owner lane `owner:a-unit4-shell` (private, 25 September 2026).

**Every definition in this file is a DRAFT.** D-A1 (randomized model), D-A2 (the 3-CNF
language), D-A3 (estimator input/output format), D-A4 (class definitions) and D-A6 (the shape of
randomized sparse ETH, `def:reth`) are AUTHOR decisions; none is chosen here. Each definition is
parametrized so that every option listed in the unit-4 map stays available:

* D-A1: a randomized algorithm is a fixed deterministic `BitMachine.Machine` run on
  `EncodedComplexity.pair input tape`, with tape length `tapeLength input` and the uniform law on
  exact-length tapes; a "reads a prefix of a longer tape" option is the special case of a machine
  that ignores a suffix. Worst-case time is quantified over every tape.
* D-A2: the language, variable count and clause count are parameters (`EncodedCNF.Language`,
  `EncodedETHTail.variableCount`, … are candidates).
* D-A3: the numeric output decoder `decode : List Bool → Option ℝ` and the estimated quantity
  `target : List Bool → Option ℕ` (the cost of the encoded matrix, `none` off the domain) are
  parameters; signed-integer and dyadic-rational decoders are both instances.
* D-A4: the error bound `err` is a parameter (`1/3` is the recommendation, not fixed).
* D-A6: the density constant is existential, the sub-exponential bound is `∀ ε > 0` with an
  explicit Boolean switch for an extra `(|input|+1)^d` factor, and a cutoff `N₀`.

**Nothing here closes a ledger row** (D04, U18, T02, T24 stay open).
-/

namespace Paper2.Unit4Shell.Definitions

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedComplexity

/-- DRAFT (D-A1): uniform law on exact-length tapes. -/
noncomputable def uniformTape (r : ℕ) : Paper2.FiniteLaw (Fin r → Bool) where
  weight _ := (1 / 2 : ℝ) ^ r
  nonneg _ := by positivity
  total := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_bool,
      Fintype.card_fin, nsmul_eq_mul]
    push_cast
    rw [← mul_pow]
    norm_num

/-- DRAFT (D-A1): a randomized algorithm in the fixed bit-machine model. `output input tape` is
the word it prints on `pair input tape`, within `time input` steps, on EVERY tape of the
prescribed length (worst-case, every-tape time; expected time is not used). -/
structure RandomizedAlgorithm where
  machine : BitMachine.Machine
  tapeLength : List Bool → ℕ
  time : List Bool → ℕ
  output : List Bool → List Bool → List Bool
  runs : ∀ input (tape : Fin (tapeLength input) → Bool),
    machine.OutputsWithin (pair input (List.ofFn tape)) (output input (List.ofFn tape))
      (time input)

namespace RandomizedAlgorithm

variable (A : RandomizedAlgorithm)

/-- DRAFT: polynomial tape length and polynomial every-tape time. -/
def Polynomial : Prop :=
  ∃ c d : ℕ, ∀ input, A.tapeLength input ≤ c * (input.length + 1) ^ d ∧
    A.time input ≤ c * (input.length + 1) ^ d

/-- DRAFT: probability of an event of the printed word under the uniform tape law. -/
noncomputable def prob (input : List Bool) (E : List Bool → Prop) : ℝ :=
  (uniformTape (A.tapeLength input)).prob (fun tape => E (A.output input (List.ofFn tape)))

/-- DRAFT (D-A4, error `err`): two-sided bounded-error decision of `L` (accept = `[true]`). -/
def Decides (L : BinaryLanguage) (err : ℝ) : Prop :=
  ∀ input, (input ∈ L → 1 - err ≤ A.prob input (· = [true])) ∧
    (input ∉ L → A.prob input (· = [true]) ≤ err)

/-- DRAFT (D-A4): one-sided (`coRP`-type) decision: members accepted on every tape,
non-members rejected with probability at least `1/2`. -/
def DecidesOneSided (L : BinaryLanguage) : Prop :=
  ∀ input, (input ∈ L → ∀ tape : Fin (A.tapeLength input) → Bool,
      A.output input (List.ofFn tape) = [true]) ∧
    (input ∉ L → 1 / 2 ≤ A.prob input (· ≠ [true]))

/-- DRAFT (D-A3): additive-error-`a` estimator of `target` with success probability `≥ 2/3` on
every input in the domain (`target input = some _`), for a parameter output decoder. -/
def Estimates (target : List Bool → Option ℕ) (decode : List Bool → Option ℝ) (a : ℝ) : Prop :=
  ∀ input c, target input = some c →
    2 / 3 ≤ A.prob input (fun out => ∃ v, decode out = some v ∧ |v - c| ≤ a)

end RandomizedAlgorithm

/-- DRAFT (D-A4 with error parameter): `BPP`. -/
def InBPP (err : ℝ) (L : BinaryLanguage) : Prop :=
  ∃ A : RandomizedAlgorithm, A.Polynomial ∧ A.Decides L err

/-- DRAFT (D-A4): `coRP` in the one-sided form above. -/
def InCoRP (L : BinaryLanguage) : Prop :=
  ∃ A : RandomizedAlgorithm, A.Polynomial ∧ A.DecidesOneSided L

/-- DRAFT (D-A6, `def:reth`): randomized sparse ETH for a parameter language with parameter
variable/clause counts. `∃ c_s`, and no bounded-error (error `err`) randomized algorithm decides
the language on every well-formed input with at most `c_s·N` clauses within `2^{εN}` (times
`(|input|+1)^d` when `withPoly`) beyond some `N₀`, for every `ε > 0`. -/
def RandomizedSparseETH (L : BinaryLanguage) (wellFormed : List Bool → Prop)
    (varCount clauseCount : List Bool → ℕ) (err : ℝ) (withPoly : Bool) : Prop :=
  ∃ cs : ℕ, ¬ ∃ A : RandomizedAlgorithm,
    (∀ input, wellFormed input → clauseCount input ≤ cs * varCount input →
      (input ∈ L → 1 - err ≤ A.prob input (· = [true])) ∧
      (input ∉ L → A.prob input (· = [true]) ≤ err)) ∧
    ∀ ε : ℝ, 0 < ε → ∃ C d N₀ : ℕ, ∀ input, wellFormed input →
      clauseCount input ≤ cs * varCount input → N₀ ≤ varCount input →
      A.time input ≤ C * ⌈(2 : ℝ) ^ (ε * varCount input)⌉₊ *
        (if withPoly then (input.length + 1) ^ d else 1)

/-- The uniform tape law gives every tape positive weight (used to pass from probability to
witness tapes). Does not close a ledger row. -/
theorem uniformTape_weight_pos (r : ℕ) (t : Fin r → Bool) : 0 < (uniformTape r).weight t := by
  simp [uniformTape]

/-- Bridge from the DRAFT one-sided decision to the option-generic witness shape of A4-S6,
given a polytime rejection indicator for the algorithm's printed word (a per-option machine
obligation, named here). Does not close a ledger row. -/
theorem oneSided_shape_of_decides {L : BinaryLanguage} (A : RandomizedAlgorithm)
    (hpoly : A.Polynomial) (hA : A.DecidesOneSided L)
    (reject : List Bool → Bool) (hrej : BitMachine.Polytime (fun code => [reject code]))
    (hrejSpec : ∀ input (tape : Fin (A.tapeLength input) → Bool),
      reject (pair input (List.ofFn tape)) = true ↔ A.output input (List.ofFn tape) ≠ [true])
    (hlong : ∀ input tape, tape.length ≠ A.tapeLength input →
      reject (pair input tape) = false) :
    ClassLemmas.OneSidedRejectShape L := by
  obtain ⟨c, d, hcd⟩ := hpoly
  refine ⟨reject, hrej, c, d, fun input => ⟨?_, ?_⟩⟩
  · intro hmem tape _
    by_cases hlen : tape.length = A.tapeLength input
    · have hof : tape = List.ofFn (fun i : Fin (A.tapeLength input) =>
          tape.get (Fin.cast hlen.symm i)) := by
        apply List.ext_get
        · simp [hlen]
        · intro i h1 h2; simp; try rfl
      rw [hof]
      have hacc := (hA input).1 hmem (fun i => tape.get (Fin.cast hlen.symm i))
      cases hr : reject (pair input (List.ofFn fun i => tape.get (Fin.cast hlen.symm i)))
      · rfl
      · exact absurd hacc ((hrejSpec input _).mp hr)
    · exact hlong input tape hlen
  · intro hnot
    have hpos : 0 < A.prob input (· ≠ [true]) := by
      have := (hA input).2 hnot; linarith
    obtain ⟨tape, htape⟩ := ClassLemmas.exists_of_prob_pos _ _ hpos
    refine ⟨List.ofFn tape, by simpa using (hcd input).1, ?_⟩
    exact (hrejSpec input tape).mpr htape

end Paper2.Unit4Shell.Definitions
