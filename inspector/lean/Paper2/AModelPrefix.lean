import Paper2.AModelTape
import Paper2.A4ClassLemmas

/-!
# Paper A (lock v12), lane `owner:a-model-1`, segment 1: the D-A1 prefix model and the D-A4 classes

Author decisions of 27 September 2026 (`AUTHOR_DECISIONS_2026-09-27.md`):
* **D-A1 (c)**: "prefix model: a deterministic `BitMachine` on `pair input tape`; the tape is uniform
  over a fixed polynomial length R(|input|), and the machine reads a prefix."
* **D-A4 (a)**: "the DRAFT definitions over `EncodedComplexity.BinaryLanguage`, error 1/3,
  polynomial tape."

Lock v12 text implemented (file:line, `versions/2026-09-22-protocol-labels-v12/source/sections/`):
* `01-introduction.tex:73-74`: "A randomized estimator must succeed with probability at least $2/3$
  on every input."
* `01-introduction.tex:90-91`: "Time, random-bit count, and output length are polynomial in the
  encoding length of $\Phi$ on every tape."
* `01-introduction.tex:112-114`: "a bounded-error polynomial-time additive-error-$a$ estimator for
  $\D$ implies $\NP\subseteq\BPP$. An always-correct deterministic polynomial-time estimator also
  implies $\NP=\coNP$."
* `01-introduction.tex:122-125`: "giving a BPP algorithm for satisfiability. If the estimator is
  always correct, the composed algorithm never rejects a satisfiable formula and rejects an
  unsatisfiable one with constant probability. Hence $\SAT\in\coRP\subseteq\coNP$ and $\NP=\coNP$."

**Reading a prefix.** The tape handed to the machine is a FULL word of length `R(|input|)`
(`List.ofFn tape`, `tape : Fin (R |input|) → Bool`), and the machine runs on
`EncodedComplexity.pair input (List.ofFn tape)` within the every-tape time bound. "Reads a prefix of
length `ℓ input`" (`ReadsPrefix`) is the semantic statement that the printed word depends only on
`(List.ofFn tape).take (ℓ input)`; `prob_of_readsPrefix` proves that then only the prefix law
matters and it is the uniform law on length-`ℓ input` words. Every prefix algorithm reads the prefix
`ℓ = R` (`readsPrefix_full`). No physical statement about which cells the TM2 program pops is made.

**Relation to the DRAFT classes.** `toDraft` turns a prefix algorithm into a DRAFT
`RandomizedAlgorithm` with tape length `R ∘ length`, the same machine, time and output; the
acceptance probabilities are definitionally equal (`prob_toDraft`), so `Decides`, `DecidesOneSided`,
`Estimates`, `InBPP`, `InCoRP` transfer (`inBPP_toDraft`, `inCoRP_toDraft`), and the admitted class
lemmas (`np_subset_of_hard_mem`, `coNP_of_oneSided` via `oneSided_shape_of_decides`) apply. A DRAFT
algorithm whose tape length is a function of the input length is a prefix algorithm (`ofDraft`,
same probabilities). The converse for a DRAFT tape length that depends on the whole word is NOT
claimed: the DRAFT machine expects the exact-length tape and may read to its end, so a prefix
version needs a physical machine that computes the length and truncates the tape.

No ledger row is closed.
-/

namespace Paper2.AModel

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedComplexity
open Paper2 Paper2.FiniteLaw
open Paper2.Unit4Shell.Definitions
open Paper2.Unit4Shell.ClassLemmas

/-- **D-A1 (c), the prefix model** (lock `01-introduction.tex:90-91`, "Time, random-bit count, and
output length are polynomial in the encoding length of $\Phi$ on every tape"). A randomized
algorithm is ONE fixed deterministic `BitMachine.Machine` run on `pair input tape`, where the tape
is a word of the fixed length `tapeLength |input|` (the decision's `R(|input|)`, a function of the
input LENGTH only). `output input tape` is the word it prints within `time input` steps, on EVERY
tape of that length (worst-case every-tape time). The law of the tape is `uniformTape`. -/
structure PrefixAlgorithm where
  machine : BitMachine.Machine
  tapeLength : ℕ → ℕ
  time : List Bool → ℕ
  output : List Bool → List Bool → List Bool
  runs : ∀ input (tape : Fin (tapeLength input.length) → Bool),
    machine.OutputsWithin (pair input (List.ofFn tape)) (output input (List.ofFn tape))
      (time input)

namespace PrefixAlgorithm

variable (A : PrefixAlgorithm)

/-- D-A1/D-A4: polynomial tape length `R` and polynomial every-tape time (lock
`01-introduction.tex:90-91`). -/
def Polynomial : Prop :=
  ∃ c d : ℕ, ∀ input : List Bool, A.tapeLength input.length ≤ c * (input.length + 1) ^ d ∧
    A.time input ≤ c * (input.length + 1) ^ d

/-- D-A1: acceptance/event probability of the printed word under the uniform law on tapes of
length `R(|input|)` (lock `01-introduction.tex:73-74`, "with probability at least $2/3$"). -/
noncomputable def prob (input : List Bool) (E : List Bool → Prop) : ℝ :=
  (uniformTape (A.tapeLength input.length)).prob (fun tape => E (A.output input (List.ofFn tape)))

/-- D-A1 (c) "the machine reads a prefix": the printed word depends only on the first
`ℓ input ≤ R(|input|)` tape bits. -/
def ReadsPrefix (ℓ : List Bool → ℕ) : Prop :=
  ∀ input, ℓ input ≤ A.tapeLength input.length ∧
    ∀ t t' : Fin (A.tapeLength input.length) → Bool,
      (List.ofFn t).take (ℓ input) = (List.ofFn t').take (ℓ input) →
        A.output input (List.ofFn t) = A.output input (List.ofFn t')

/-- Every prefix algorithm reads the full prefix `ℓ = R`. -/
theorem readsPrefix_full : A.ReadsPrefix (fun input => A.tapeLength input.length) := by
  intro input
  refine ⟨le_rfl, fun t t' h => ?_⟩
  have ht : (List.ofFn t).take (A.tapeLength input.length) = List.ofFn t :=
    List.take_of_length_le (by simp)
  have ht' : (List.ofFn t').take (A.tapeLength input.length) = List.ofFn t' :=
    List.take_of_length_le (by simp)
  rw [← ht, h, ht']

/-- The canonical full-length tape extending a prefix `s` of length `ℓ ≤ R` by `false` bits. -/
def padTape {ℓ R : ℕ} (s : Fin ℓ → Bool) : Fin R → Bool :=
  fun i => if h : i.val < ℓ then s ⟨i.val, h⟩ else false

theorem take_ofFn_padTape {ℓ R : ℕ} (h : ℓ ≤ R) (s : Fin ℓ → Bool) :
    (List.ofFn (padTape (R := R) s)).take ℓ = List.ofFn s := by
  apply List.ext_getElem
  · simp [h]
  · intro i h1 h2
    simp only [List.getElem_take, List.getElem_ofFn, padTape]
    have hi : i < ℓ := by simpa using h2
    simp [hi]

/-- **Reading a prefix, only the prefix law matters, and it is uniform** (D-A1 (c) with the tape
lemma `uniformTape_take_prob`): the event probability of an algorithm that reads the prefix
`ℓ input` equals the probability under the uniform law on length-`ℓ input` prefixes, the rest of
the tape being filled by `false`. -/
theorem prob_of_readsPrefix {ℓ : List Bool → ℕ} (hA : A.ReadsPrefix ℓ) (input : List Bool)
    (E : List Bool → Prop) :
    A.prob input E = (uniformTape (ℓ input)).prob
      (fun s => E (A.output input (List.ofFn (padTape (R := A.tapeLength input.length) s)))) := by
  obtain ⟨hle, hdep⟩ := hA input
  let G : List Bool → Prop := fun w =>
    ∃ t : Fin (A.tapeLength input.length) → Bool,
      (List.ofFn t).take (ℓ input) = w ∧ E (A.output input (List.ofFn t))
  have hG : ∀ t : Fin (A.tapeLength input.length) → Bool,
      E (A.output input (List.ofFn t)) ↔ G ((List.ofFn t).take (ℓ input)) := by
    intro t
    constructor
    · intro h; exact ⟨t, rfl, h⟩
    · rintro ⟨t', ht', h⟩
      rwa [hdep t' t ht'] at h
  have hG' : ∀ s : Fin (ℓ input) → Bool,
      G (List.ofFn s) ↔
        E (A.output input (List.ofFn (padTape (R := A.tapeLength input.length) s))) := by
    intro s
    rw [← take_ofFn_padTape hle s, ← hG]
  unfold prob
  have h1 : (fun tape : Fin (A.tapeLength input.length) → Bool =>
      E (A.output input (List.ofFn tape))) =
      (fun tape => G ((List.ofFn tape).take (ℓ input))) := by
    funext t; exact propext (hG t)
  rw [h1, uniformTape_take_prob hle G]
  congr 1
  funext s
  exact propext (hG' s)

/-- **D-A4 (a) with error `err`** (lock `01-introduction.tex:112-113`, "bounded-error"):
two-sided bounded-error decision of `L` in the prefix model (accept = printed word `[true]`). -/
def Decides (L : BinaryLanguage) (err : ℝ) : Prop :=
  ∀ input, (input ∈ L → 1 - err ≤ A.prob input (· = [true])) ∧
    (input ∉ L → A.prob input (· = [true]) ≤ err)

/-- **D-A4 (a), one-sided (`coRP`) decision** (lock `01-introduction.tex:123-125`, "never rejects a
satisfiable formula and rejects an unsatisfiable one with constant probability"; the DRAFT constant
is `1/2`): members accepted on every tape of length `R(|input|)`, non-members rejected with
probability at least `1/2`. -/
def DecidesOneSided (L : BinaryLanguage) : Prop :=
  ∀ input, (input ∈ L → ∀ tape : Fin (A.tapeLength input.length) → Bool,
      A.output input (List.ofFn tape) = [true]) ∧
    (input ∉ L → 1 / 2 ≤ A.prob input (· ≠ [true]))

/-- D-A1 → DRAFT: the same machine, time and output, with DRAFT tape length `R ∘ length`. -/
def toDraft : RandomizedAlgorithm where
  machine := A.machine
  tapeLength := fun input => A.tapeLength input.length
  time := A.time
  output := A.output
  runs := A.runs

/-- The DRAFT probability of `toDraft` is the prefix-model probability (definitional). -/
theorem prob_toDraft (input : List Bool) (E : List Bool → Prop) :
    A.toDraft.prob input E = A.prob input E := rfl

theorem polynomial_toDraft (h : A.Polynomial) : A.toDraft.Polynomial := h

theorem decides_iff_toDraft (L : BinaryLanguage) (err : ℝ) :
    A.Decides L err ↔ A.toDraft.Decides L err := Iff.rfl

theorem decidesOneSided_iff_toDraft (L : BinaryLanguage) :
    A.DecidesOneSided L ↔ A.toDraft.DecidesOneSided L := Iff.rfl

end PrefixAlgorithm

/-- `List.ofFn` is invariant under reindexing along a length equality. -/
theorem ofFn_cast {n m : ℕ} (h : n = m) (f : Fin m → Bool) :
    List.ofFn (fun i : Fin n => f (Fin.cast h i)) = List.ofFn f := by
  subst h; rfl

/-- DRAFT → D-A1 when the DRAFT tape length is a function `R` of the input length: the same
machine, time and output. -/
def ofDraft (A : RandomizedAlgorithm) (R : ℕ → ℕ)
    (hR : ∀ input, A.tapeLength input = R input.length) : PrefixAlgorithm where
  machine := A.machine
  tapeLength := R
  time := A.time
  output := A.output
  runs := fun input tape => by
    have h := A.runs input (fun i => tape (Fin.cast (hR input) i))
    rwa [ofFn_cast (hR input) tape] at h

theorem prob_ofDraft (A : RandomizedAlgorithm) (R : ℕ → ℕ)
    (hR : ∀ input, A.tapeLength input = R input.length) (input : List Bool)
    (E : List Bool → Prop) : (ofDraft A R hR).prob input E = A.prob input E := by
  unfold PrefixAlgorithm.prob RandomizedAlgorithm.prob
  exact (uniformTape_prob_ofFn_congr (hR input) (fun w => E (A.output input w))).symm

/-- **D-A4 (a), `BPP` in the prefix model** (lock `01-introduction.tex:113`, "$\NP\subseteq\BPP$";
error `1/3`, polynomial tape and time). -/
def InBPP (L : BinaryLanguage) : Prop :=
  ∃ A : PrefixAlgorithm, A.Polynomial ∧ A.Decides L (1 / 3)

/-- **D-A4 (a), `coRP` in the prefix model** (lock `01-introduction.tex:125`,
"$\SAT\in\coRP\subseteq\coNP$"). -/
def InCoRP (L : BinaryLanguage) : Prop :=
  ∃ A : PrefixAlgorithm, A.Polynomial ∧ A.DecidesOneSided L

/-- **D-A4 (a), `coNP`** (lock `01-introduction.tex:125`): the admitted DRAFT
`ClassLemmas.InCoNP L := InNP Lᶜ` (verifier form in the same bit-machine model; no randomness,
so it is the same class in the prefix model). -/
abbrev InCoNP (L : BinaryLanguage) : Prop := Paper2.Unit4Shell.ClassLemmas.InCoNP L

/-- Prefix-model `BPP` is contained in the DRAFT `InBPP (1/3)`. -/
theorem inBPP_toDraft {L : BinaryLanguage} (h : InBPP L) : Paper2.Unit4Shell.Definitions.InBPP (1 / 3) L := by
  obtain ⟨A, hp, hd⟩ := h
  exact ⟨A.toDraft, hp, hd⟩

/-- Prefix-model `coRP` is contained in the DRAFT `InCoRP`. -/
theorem inCoRP_toDraft {L : BinaryLanguage} (h : InCoRP L) : Paper2.Unit4Shell.Definitions.InCoRP L := by
  obtain ⟨A, hp, hd⟩ := h
  exact ⟨A.toDraft, hp, hd⟩

/-- A DRAFT `BPP` algorithm whose tape length is a function of the input length gives
prefix-model `BPP` membership. -/
theorem inBPP_of_draft {L : BinaryLanguage} (A : RandomizedAlgorithm) (R : ℕ → ℕ)
    (hR : ∀ input, A.tapeLength input = R input.length) (hp : A.Polynomial)
    (hd : A.Decides L (1 / 3)) : InBPP L := by
  refine ⟨ofDraft A R hR, ?_, ?_⟩
  · obtain ⟨c, d, h⟩ := hp
    exact ⟨c, d, fun input => by
      refine ⟨?_, (h input).2⟩
      have := (h input).1
      rw [hR input] at this
      exact this⟩
  · intro input
    simp only [prob_ofDraft]
    exact hd input

/-- **T02 step "NP ⊆ BPP"** in the prefix model, from the admitted `np_subset_of_hard_mem`: an
NP-hard language (D-A5 hypothesis) in prefix-model `BPP` puts NP inside prefix-model `BPP`, given
the machine-level closure of prefix-model `BPP` under the banked reductions (a named obligation,
not proved here). -/
theorem np_subset_inBPP (hC : ReductionClosed InBPP) {K : BinaryLanguage} (hK : NPHard K)
    (hmem : InBPP K) : ∀ L, InNP L → InBPP L :=
  np_subset_of_hard_mem InBPP hC hK hmem

/-- **T02 step "coRP ⊆ coNP"** in the prefix model, from the admitted `oneSided_shape_of_decides`
and `coNP_of_oneSided`: a prefix-model one-sided decider with a polytime rejection indicator of its
printed word (the per-option machine obligation named by the admitted DRAFT lemma, not proved here)
puts `L` in `coNP`. -/
theorem inCoNP_of_prefix_oneSided {L : BinaryLanguage} (A : PrefixAlgorithm)
    (hpoly : A.Polynomial) (hA : A.DecidesOneSided L)
    (reject : List Bool → Bool) (hrej : BitMachine.Polytime (fun code => [reject code]))
    (hrejSpec : ∀ input (tape : Fin (A.tapeLength input.length) → Bool),
      reject (pair input (List.ofFn tape)) = true ↔ A.output input (List.ofFn tape) ≠ [true])
    (hlong : ∀ input tape, tape.length ≠ A.tapeLength input.length →
      reject (pair input tape) = false) :
    InCoNP L :=
  coNP_of_oneSided
    (oneSided_shape_of_decides A.toDraft hpoly hA reject hrej hrejSpec hlong)

end Paper2.AModel

#print axioms Paper2.AModel.PrefixAlgorithm.readsPrefix_full
#print axioms Paper2.AModel.PrefixAlgorithm.take_ofFn_padTape
#print axioms Paper2.AModel.PrefixAlgorithm.prob_of_readsPrefix
#print axioms Paper2.AModel.PrefixAlgorithm.prob_toDraft
#print axioms Paper2.AModel.prob_ofDraft
#print axioms Paper2.AModel.inBPP_toDraft
#print axioms Paper2.AModel.inCoRP_toDraft
#print axioms Paper2.AModel.inBPP_of_draft
#print axioms Paper2.AModel.np_subset_inBPP
#print axioms Paper2.AModel.inCoNP_of_prefix_oneSided
