# Independent final deterministic implication review

The deterministic construction with a deterministic estimator passes this
bounded independent semantic review and private Lean 4.30.0 replay. It gives
one actual finite machine, exact on every formula satisfying the selected
clause-density bound, including all smaller sizes. Its actual clock is
eventually a fixed polynomial in the displayed size bound evaluated at the
original variable count and original supplied gap. No blocking defect was
found in the three frozen modules reviewed here.

This accepts the deterministic branch for root integration and shared gates.
It does not certify the other three randomness combinations, either concrete
rate corollary, a fresh production build, or publication readiness.

## Frozen source and independent replay

The paper source is
`papers/randomized-additive-hardness/versions/v43/source/main.tex`, SHA-256
`bfde23b90f50785939095a6d37b7b247965ee6c45beaca9011a8963dec3cc9d6`.
The reviewed anchor is Theorem 9.7, `thm:time-tradeoff`, theorem source
lines 3229--3256 and proof lines 3258--3280 (labels at 3230 and 3259).
The supplied 3238--3287 range is stale for this source hash; the complete
theorem and proof were read. The source has not been edited.

All ten general-module sources and their existing objects were copied into
the private `V43TimeTradeoff/` namespace directory. The following three
sources were independently elaborated serially, replacing only their private
objects. Their frozen hashes were asserted before replay:

| File | SHA-256 |
| --- | --- |
| RequestClock.lean | a252929ff7dc8d26c03fc67806320a5d2655a7013221a745c5ab1ea389f9f475 |
| DeterministicEndpoint.lean | 048a918dc0dac1d769393a7cab424ecb3b6196773d343563d6c79e0a957f2663 |
| CommonConstants.lean | 5bc57bc8b705afeefd273575bd03825c5ef3c869ed95c934e8dcc6a66a088774 |

The exact private-first import path is retained in `LEAN_PATH.txt`.
Production/package objects and earlier checked general-module objects were
reused; this is not a cold dependency rebuild. The external private dependency
sources `V43Parametric.Source` and `CurrentV43.MixedCaller.Request` were read,
hashed and copied as provenance. Their implementations agree with the earlier
component review. Source hashes are in `SOURCE_HASHES.json`; imported-object
hashes and inspected production-source hashes are in `DEPENDENCY_HASHES.json`.

`RequestClock.replay.log`, `DeterministicEndpoint.replay.log` and
`CommonConstants.replay.log` all record successful compilation.
`LiteralAudit.replay.log` independently records the two final literal types
and additional helper axiom audits. The compiler is Lean 4.30.0, commit
`d024af099ca4bf2c86f649261ebf59565dc8c622`.

## Literal mathematical and machine correspondence

`PhysicalConcat.Producer` contains a finite `BitMachine.Machine` and an
`OutputsWithin` proof on every raw word. The endpoint existential chooses one
such producer before any input formula. Its result is the SAT bit on every
valid `cs`-sparse formula; the correctness clause has no lower-size condition.
Malformed words still have actual terminating runs, with no correctness
claim needed for them.

The selected cutoff includes the eventual strict-gap threshold, the eventual
estimator-accuracy threshold after the proved entry-count lower bound, the
source graph cutoff at density `cs+2`, 16, and the fixed dyadic-base cutoff.
The actual sparse router always returns a valid formula at least this large
and of density at most `cs+2`. `routed_sat_iff` transfers its classifier answer
back to every original sparse formula. The small-input behavior uses the
inherited, physically charged finite-control router; it does not accept a
SAT answer or a final execution certificate as a premise.

For sufficiently large original formulas, `routedFormula_original` is literal
identity. Consequently both the variable count and `G.gap` used in the clock
are the original ones. The clock proof separately pays routing, source graph
and field production, execution of the gap program, unary-gap serialization,
the deterministic table/request constructor, all composition transfers, and
the extracted estimator/comparator machine. `requestTime_source_bound`
converts the actual graph-constructor clock to a fixed power of the displayed
deterministic size. The final theorem has the form `c*S(N,G.gap N)^d`, with
fixed `c,d` allowed to depend on the estimator and gap program.

`Schedule.paid` is a bound polynomial in `N+G.gap N`, separately at every fixed
clause density. There is no bound `G.gap N <= poly(N)`, and no monotonicity of
the gap is required. `deterministicSize_dominates` absorbs `N+gap+2`, so
superpolynomial gaps and their actual serialization remain permitted.

The error function is arbitrary and monotone. Accuracy is required only
eventually, on square tables with power-of-two side length; the actual
constructor's entry lower bound makes that premise applicable. The actual
table-size upper bound and monotonicity give the same strict midpoint gap
used by the exact source classifier. No ETH assumption, finished SAT clock,
SAT decider, desired output execution, or final correctness premise is added.

The amplification and native construction constant are explicit functions of
the fixed source reductions alone. `deterministic_time_tradeoff_at` accepts
any larger common `C` before the estimator and schedule. It transfers the
strict-gap hypothesis to the native smaller size by monotonicity, then
enlarges the very same machine's clock bound. Thus choosing a maximum across
the four construction/estimator cases is valid for this branch. The cutoff
and the runtime polynomial may depend on the estimator, error threshold and
schedule, as permitted by the paper.

## Accepted declarations and remaining boundaries

Under `CurrentV43.TimeTradeoff`, the accepted declarations are
`requestTime_source_bound`, `request_clock_poly`, `request_clock_sparse`,
`deterministic_caller_clock_poly`, `deterministic_caller_clock_sparse`,
`deterministic_time_tradeoff`, `randomizedSize_mono_constant`,
`deterministicSize_mono_constant`, `gap_of_larger_size`, and
`deterministic_time_tradeoff_at`.

All printed endpoint/clock axioms are exactly `propext`, `Classical.choice`,
and `Quot.sound`. The two pure size-monotonicity helpers use a subset of
these. The remaining audited helper uses the same allowlist. No `sorry`,
`admit`, new `axiom`, or opaque conclusion certificate occurs in the three
reviewed source files or in their transitive endpoint axiom reports.

The source-relative Dinur/BOT interfaces and inherited permitted-estimator
model remain explicit. This segment does not separately construct a schedule
from an arbitrary informal algorithm description; its schedule already
contains the actual finite implementation, literal unary-output correctness,
and paid clock. It proves the implication for every such schedule.

Root production integration, source-bound aggregate correspondence, shared
builds and transitive audits remain required before changing the paper's or
website's public formalization status. Only this private review directory
was written. No production source, manuscript, shared build, Git state,
website or other agent's files were changed.
