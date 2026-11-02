# Final arbitrary-gap randomized-construction endpoint review

The five frozen GeneralRandom modules pass independent semantic review and
private Lean 4.30.0 replay. Their final theorem closes the
**randomized-construction branch** of v43 `thm:time-tradeoff`, for either a
deterministic or randomized estimator, relative to the named approved
source interfaces and declared finite-machine models. It returns an actual
fair-bit algorithm, proves bounded-error correctness on every promised
sparse formula, and proves its complete charged worst-case runtime is
eventually a fixed polynomial in the manuscript's displayed `S(N,k)`.

It does not assume a final SAT success probability, execution, clock, or
finished decider. The deterministic-construction branches are separate
work; this review alone is not an all-four-case admission of the full
manuscript theorem.

## Frozen files and replay

Exact hashes and per-file replay logs are in `general-random/RECEIPT.json`.
The worker confirmed all five sources frozen before they were copied into
this private review tree. Estimator and Source were replayed after the new
supporting randomized dependency group, then Algorithm, Clock, and Endpoint
were replayed serially. Every invocation exited successfully. All eleven
printed theorem/definition axiom reports contain only `propext`,
`Classical.choice`, and `Quot.sound`.

Dependencies include the previously reviewed general accuracy/source
bounds, the freshly replayed randomized support closure, common parametric
machines, and the separately reviewed ResourceFit/ResourceTotal clock
theorems. Existing dependency objects were reused; this is not a clean
production replay. Root production admission remains a separate gate.

## Literal final statement and source comparison

The target is v43 `thm:time-tradeoff` at selected `main.tex:3230-3287`,
source SHA-256
`bfde23b90f50785939095a6d37b7b247965ee6c45beaca9011a8963dec3cc9d6`.

`randomized_construction_time_tradeoff` states:

- There exists one positive construction constant `C0`, before every
  estimator, error function, accuracy threshold, and implemented gap
  schedule.
- For either permitted numerical-estimator type, monotone real error
  `a`, sufficiently-large dyadic-square accuracy, and any implemented
  positive gap `G.gap`, an eventual strict bound
  `2*a((N+2)^(C0*(G.gap N+1))) < G.gap N` implies the endpoint.
- For every fixed sparse clause density it returns an actual
  `FairBitAlgorithm.Algorithm` that is correct with error at most `1/3`
  on **every** valid formula at that density, including all small sizes.
- For that same algorithm there are fixed `c,d,N1` such that, for every
  promised sparse input with original variable count at least `N1`, its
  complete `totalTime` is at most `c*S(N,G.gap N)^d`.

The runtime conclusion is an eventual worst-case bound, the ordinary
asymptotic meaning of `S^{O(1)}`. Correctness itself covers all input sizes.
The schedule is represented by `Schedule`, which supplies an actual finite
gap-printing machine, its exact unary value on canonical formulas, and the
required per-density polynomial bound in `N+gap(N)`. This is the
implementation form of the manuscript's paid gap-computation premise;
there is no polynomial upper bound on the gap and no old subexponential
random-tape restriction.

`time_tradeoff_of_larger_constant` proves the same result for every
`C0 >= sourceConstant D`. This permits the root to choose a common larger
constant for both constructions without making the error-size argument
depend on an estimator or schedule. Explicit deterministic-estimator and
randomized-estimator specializations are also proved.

## Constant order and actual source obligations

The constant is explicitly
`sourceConstant D=(D.sizeExponent+4)*randomizedGraphExponent`, and is proved
positive. It contains neither an estimator nor a schedule. The final
existential is outside their universal quantifiers; this rules out choosing
the construction size after seeing an estimator's runtime exponent.

`Source.source_all_large` proves the actual table's upper size bound from
the inherited sparse-source graph polynomial and the actual constructor
resource theorem. Its lower size bound follows from
`N >= degreeBound*T0` and the positive gap. Its source successful-NO cutoff
comes from the actual graph's source-variable floor. The remaining cutoff
is the given eventual strict error-gap hypothesis. These are all combined
into one finite original-variable cutoff; no desired source probability is
assumed in the final theorem.

The source-law correctness is derived from the real YES/NO source gap and
the original estimator accuracy. For randomized estimators, nonnegativity
of `a(S)` is derived from the accuracy event. No additional nonnegative
error hypothesis is silently inserted.

## Faithful deterministic-estimator specialization

`Estimator.deterministicActual` retains the original deterministic
estimator's actual output, physical machine implementation, value function,
and rational comparator. The inherited selected deterministic adapter has
zero estimator-tape length. Its classifier output equals the original
deterministic `E.run` on every tape; it is not replaced by an assumed
randomized accuracy certificate.

The deterministic source-correctness proof integrates out the independent
classifier tape with total mass one. It applies the actual deterministic
comparison theorem on every YES table and the actual `49/50` construction
NO gap event. This yields the required acceptance bounds. The estimator
contributes no randomness; any unused carrier bits are still charged in
the algorithm's total runtime.

## Same algorithm, all sizes, and full clock

Algorithm uses the already reviewed concrete resource printer and proves
both actual sampler and classifier prefixes fit. Its exact output law is
the physical routed algorithm law. The finite prefix is handled by the
charged SAT-preserving sparse router at density `cs+2`, not by an
unproved assertion that small inputs can be ignored. The proof invokes
`routed4_sat_iff` and the original encoded SAT language equivalence.

Clock consumes the actual ResourceTotal theorem, which in turn pays the
gap producer, source/front execution, resource/carrier generation, random
bits, sample table, estimator, rational comparison, transfers and framing.
It adds both router runs and bounds the result by a fixed polynomial in
the original manuscript `S`. Its runtime coefficients/exponent may depend
on the fixed estimator, schedule, density and finite cutoff, as permitted.
This dependence does not enter `C0` or alter the table/error bound.

The final Endpoint joins the correctness and clock of this **same**
algorithm. There is no existential switch to a different faster machine,
no expected-time substitution, and no final probability or runtime premise.

No blocking semantic defect was found in this randomized-construction
endpoint. Full theorem completion still requires the independently checked
deterministic-construction branches and the root's production/source-bound
gates. Earlier reports and snapshots were preserved; only this private
review directory was written.
