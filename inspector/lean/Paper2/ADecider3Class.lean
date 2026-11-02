import Paper2.SelectedTape
import Paper2.NPReductionClosed
import Paper2.AEndpointClass

/-!
# T02 classes in the selected-tape carrier (lane owner:a-decider-3, segment 1)

Carrier: `Paper2.SelectedTape.Algorithm` (ROOT DECISION R19, `MODEL_REPAIR_2026-09-27.md`),
the literal implementation of the author's D-A1 ("fixed polynomial length"): fixed natural
constants `cR dR cT dT` and ONE finite machine chosen before the input; for every word `x`
and every tape of exactly `cR*(|x|+1)^dR` bits the machine runs on the actual pair encoding
within `cT*(|x|+1)^dT`. The class names below follow D-A4 read together with D-A1 (R19):
they are NOT the defective legacy `Unit4Shell.Definitions.InBPP` / `AModel.InBPP`.

Lock v12 `sections/01-introduction.tex:69-76` (the estimator model):
"An additive-error-$a$ estimator returns a number $\widehat D(M)$ with
$|\widehat D(M)-\D(M)|\le a$. A randomized estimator must succeed with probability at least
$2/3$ on every input."

Lock v12 `sections/01-introduction.tex:111-125` (`intro:corollary` and proof):
"For every fixed $a\ge0$, a bounded-error polynomial-time additive-error-$a$ estimator for
$\D$ implies $\NP\subseteq\BPP$. An always-correct deterministic polynomial-time estimator also
implies $\NP=\coNP$. ... If the estimator is always correct, the composed algorithm never
rejects a satisfiable formula and rejects an unsatisfiable one with constant probability.
Hence $\SAT\in\coRP\subseteq\coNP$ and $\NP=\coNP$."
-/

noncomputable section

namespace Paper2.ADecider3

open EthInapproximability.CurrentPaper
open EthInapproximability.CurrentPaper.EncodedComplexity

/-- Bounded-error decision (error `1/3`) in the selected carrier (D-A1, D-A4): exactly the
carrier's own `SelectedTape.Algorithm.Decides` at `1/3`. -/
abbrev Decides (A : SelectedTape.Algorithm) (L : BinaryLanguage) : Prop :=
  A.Decides L (1 / 3)

/-- One-sided (`coRP`-type) decision in the selected carrier (lock I:123-125, "never rejects a
satisfiable formula and rejects an unsatisfiable one with constant probability"; D-A4 constant
`1/2`): every member is accepted (printed word `[true]`) on EVERY selected tape, and every
non-member is rejected (printed word `≠ [true]`) with probability at least `1/2`. -/
def DecidesOneSided (A : SelectedTape.Algorithm) (L : BinaryLanguage) : Prop :=
  ∀ x, (x ∈ L → ∀ t : Fin (A.tapeLength x) → Bool, A.output x (List.ofFn t) = [true]) ∧
    (x ∉ L → (1 / 2 : ℝ) ≤ A.prob x (· ≠ [true]))

/-- `BPP` in the selected carrier (D-A1 + D-A4, R19): the carrier's `SelectedTape.InBPP`. -/
abbrev InBPP (L : BinaryLanguage) : Prop := SelectedTape.InBPP L

/-- `coRP` in the selected carrier (D-A1 + D-A4, R19). -/
def InCoRP (L : BinaryLanguage) : Prop :=
  ∃ A : SelectedTape.Algorithm, DecidesOneSided A L

/-- **Reduction closure of selected-carrier `BPP`** (physical: the reduction machine in front,
the outer tape truncated by the admitted `NPOwner1.Trunc` program, probabilities transported by
`AModel.uniformTape_take_prob`). Exact reuse of `SelectedTape.reductionClosed`. -/
theorem inBPP_reductionClosed :
    Paper2.Unit4Shell.ClassLemmas.ReductionClosed InBPP :=
  SelectedTape.reductionClosed

/-- Probability of the complement event in the selected carrier. -/
theorem prob_ne_true (A : SelectedTape.Algorithm) (x : List Bool) :
    A.prob x (· ≠ [true]) = 1 - A.prob x (· = [true]) := by
  unfold SelectedTape.Algorithm.prob
  exact Paper2.Unit4Shell.Amplification.prob_not _ _

/-- Acceptance on every selected tape gives acceptance probability `1` (the member clause of
`DecidesOneSided`, read as a probability). -/
theorem prob_accept_of_every_tape (A : SelectedTape.Algorithm) (x : List Bool)
    (h : ∀ t : Fin (A.tapeLength x) → Bool, A.output x (List.ofFn t) = [true]) :
    A.prob x (· = [true]) = 1 := by
  unfold SelectedTape.Algorithm.prob
  exact Paper2.AEndpoint.prob_of_forall _ _ h

end Paper2.ADecider3

#print axioms Paper2.ADecider3.inBPP_reductionClosed
#print axioms Paper2.ADecider3.prob_ne_true
#print axioms Paper2.ADecider3.prob_accept_of_every_tape
