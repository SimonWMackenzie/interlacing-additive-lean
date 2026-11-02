# Independent randomized support-closure review

On 2 November 2026 the ten frozen files listed in
`randomized-outer/RECEIPT.json` passed bounded independent semantic review
and a sequential private Lean 4.30.0 replay. This includes every new
randomized supporting module requested by the root: Source, Router,
Parameters, Clock, Algorithm, OuterClock, Concrete, the thin Probability
bridge, AlgorithmLaw, and ConcreteLaw. Exact file hashes and replay-log
paths are recorded in that receipt.

No blocking semantic defect was found. The concrete algorithm has
bounded-error correctness on every sparse formula, including the finite
prefix. The final exponential runtime corollary is reviewed separately;
these supporting-module passes do not replace its final statement audit.

## Replay boundary

The worker confirmed the ten sources frozen. They were copied into the
private `randomized-outer/` directory and compiled in dependency order,
including rebuilding the outer modules against the freshly replayed
Source/Router/Parameters/Clock objects. Every compiler invocation exited
successfully. The printed transitive axiom reports contain only
`propext`, `Classical.choice`, and `Quot.sound`.

The already reviewed arithmetic and PowerSchedule pair, common parametric
machine/model modules, SourceBounds, and ResourceFit remain external
dependencies of this new group. The root identified the existing
ResourceFit review and admission and separately assigned
ResourceClock/ResourceTotal review. Those are not duplicate admissions by
this reviewer. Existing production/package objects were reused; this is
not a clean rebuild or a production gate.

## Source and all-size correctness

The actual source graph has the inherited source-variable floor and
quasi-linear upper bound. `Source.source_law_all_large` discharges its
public tests and successful-NO cutoff, the estimator's actual entry-count
threshold, nonnegativity of the concrete error at those entries, and the
strict gap at the actual sample size. The construction and estimator
events concern the same literal table and public midpoint. YES correctness
uses the actual source coloring; NO correctness uses the actual source gap
and the rounded sampler's successful-NO probability. No final decision
probability is assumed.

The finite-prefix theorem applies those facts to the actual sparse routed
formula at density `cs+2`. The router is an actual charged finite machine.
It outputs a valid sufficiently large formula for every raw word, and
`routed4_sat_iff` proves that it preserves SAT on every promised sparse
formula, including sizes below the asymptotic cutoff. On large promised
formulas it is literally the identity, retaining the original variable
count and the rational gap schedule.

Parameters consists of definitions of the same actual source numerical
constants; it introduces no new hypothesis. RouterTape is an actual
`PairMap` execution that changes only the formula component and preserves
every random bit. The Algorithm and Concrete results therefore apply to
the same physically routed input and two blocks whose law was proved in
the common probability review.

`algorithm_probability` attaches the exact physical output law to the
concrete algorithm. `algorithm_correctness` then derives both acceptance
and rejection bounds on every promised sparse formula from the source-law
theorem and the SAT-preserving router. It has no final probability or
execution premise. The cutoff can depend on the estimator, error
coefficient, rational exponent, and density; it becomes part of the fixed
algorithm's program. The same single algorithm is used in both YES and NO
conclusions.

## Clock support and full charges

Clock bounds the original sparse CNF encoding by a fixed power of its
actual source graph size, then converts every fixed polynomial of the
input bytes and concrete resource word into a bound
`ceil(2^(K*N^alpha))`. Its hypotheses on the rational exponent and source
geometry are discharged for the actual source. It is a numerical
conversion lemma, not an assumed runtime of the final algorithm.

Algorithm exposes the exact large-input total charge, including the
physical carrier printer, two router executions, all random bits, input
framing, and the uniform worst-case caller clock. The uniform caller
clock depends only on fixed lengths, not on random values. OuterClock
absorbs the cubic router and its extra framing into a polynomial of an
already paid inner clock. Its algebra retains both router runs and all
carrier/bit terms. The final Runtime module must instantiate this with the
actual ResourceTotal theorem; it may not assume that desired clock bound.

The concrete resource exponent is allowed to depend on the estimator's
fixed tape polynomial. This only changes the runtime overhead. It does not
change the actual table, midpoint, or approximation-error argument.

## Source correspondence

The source comparison is to v43 `thm:quantitative` and proof, selected
`main.tex` SHA-256
`bfde23b90f50785939095a6d37b7b247965ee6c45beaca9011a8963dec3cc9d6`.
The supporting lemmas implement the rational-gap construction, actual
fair-bit algorithm, independent repeated comparison, finite-prefix
handling, and full clock conversion. The final universal choices of
`c`, `alpha`, the rational exponent, and the completed runtime are checked
in the separate final endpoint review.

Only the private review directory was written. Earlier reviews and frozen
snapshots were retained; no production, shared-build, Git, or manuscript
change was made by this reviewer.
