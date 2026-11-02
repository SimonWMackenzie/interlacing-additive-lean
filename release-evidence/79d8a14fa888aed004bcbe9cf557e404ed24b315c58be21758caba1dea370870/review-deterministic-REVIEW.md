# Independent review of the deterministic v43 runtime corollary

The two frozen candidate files are accepted at the scope stated below. They
prove that an estimator with the stated logarithmic-logarithmic error yields
one actual deterministic sparse-3-SAT machine, correct on every sparse input,
with an eventual quasipolynomial charged running time. Both files passed an
independent private Lean replay. This is an admission recommendation for the
root integrator, not a production build or release claim.

## Exact frozen inputs and replay

The selected manuscript is `papers/randomized-additive-hardness/versions/v43/source/main.tex`,
SHA256 `BFDE23B90F50785939095A6D37B7B247965EE6C45BEACA9011A8963DEC3CC9D6`.
The reviewed statement is `det:time`, lines 353--362; its proof is lines
2910--2952. The estimator convention is at lines 1008--1010, including
polynomial-time comparison with polynomial-length binary rationals.

The snapshots in this directory are independent copies of the worker files:

- `V43DeterministicRate.lean`, SHA256
  `0FCB84E9EB6B89BDB0061765ADC1B72013712C83BF9F71F82B5DAC30872EF624`.
- `V43DeterministicRateReal.lean`, SHA256
  `835E7D77CD6DE98ABA160036D8D586F4FF45E05F600B7F89500B88AE3B2DD05C`.

The core imports `CurrentAdditive.V42DeterministicETHEndpoint` and
`Paper2.A4T24RuntimeComposed`. The supplement imports this directory's frozen
`V43DeterministicRate` object. From the repository root, the reviewer ran
`lake env lean -o <private output> <private source>` for each file, setting
`LEAN_PATH` to this private directory for the supplement. Both exited 0.
The only diagnostic in the core is an unused `hM` argument in
`double_log_bound`. The supplement has no diagnostics.

The replay uses the repository's existing imported objects. It is not a cold
rebuild of all inherited dependencies. No production files, shared build,
Git operation, source lock, paper or publication were changed. There was at
most one private compiler process at a time.

## Endpoint and quantifier review

`deterministic_estimation_to_sparse3SAT` first takes the approved source
records `D : DinurReduction` and `B : BOTReduction (booleanOccurrence D)`.
It then proves an existential positive real constant before quantifying the
estimator, its eventual table cutoff, the fixed clause density, and the input.
For each such estimator and density it produces a
`DeterministicSparseETH.Algorithm`, whose record includes a single finite
Boolean-stack machine and a charged halting proof on every bit-string input.
Correctness holds on every valid canonical formula with at most `cs*N`
clauses. One constant and one input cutoff bound its charged time by
`2^(C*(Nat.clog 2 (N+2))^2)`.

`deterministic_estimation_to_sparse3SAT_real` accepts an estimator accurate on
all sufficiently large explicit total tables and proves the literal real-log
bound `2^(C*(Real.logb 2 N)^2)`. The core already establishes the stronger
square-power-of-two estimator restriction sufficient in the paper; the
generic checked `quasipoly_clock_real` converts that core clock too.

There is no ETH assumption, source-provided SAT algorithm, desired-output
certificate, successful-constructor-run supplier, or whole-algorithm clock
premise in either endpoint. The estimator's physical polynomial-time and
comparison requirements are the manuscript's estimator convention, not an
additional SAT-solving premise.

## Mathematical and physical checks

1. The constant is `1/(8*Nat.clog 2 A)`, with `A` the actual fixed source
   constructor's amplification. `V42GraphRuntime.amplification_power` makes
   `A` a power of two, and `amplification_ge` gives `A >= 2^64`.
   `coefficient_pos` proves positivity and `coefficient_eq_rational` identifies
   the coefficient with an explicit rational expression. The construction's
   numerical constant is fixed before the estimator and density. It is not
   asserted uniform over arbitrary alternative choices of upstream source
   implementations; the named source records are fixed external inputs.
2. The round count is computed by an actual unary producer from the original
   formula variable count, not the graph size or generated table length.
   `amplification_rounds_le` proves `A^k <= floor(log2 N)`. For large inputs,
   `numeric_gap` proves positive `k`, bounds `loglog T` by `3*k*clog2 A`, and
   proves the strict midpoint margin `2*c*loglog T < k`.
3. The estimator is applied to the very stored square word
   `V42ActualSource.word D B Phi K`. Accuracy, communication-cost bounds,
   public midpoint, request printer and machine result all use the same
   `V42ActualSource.run`, threshold and round count. The midpoint code is
   derived by the inherited `V42PermittedExtraction` provider, rather than
   assumed as a family-specific comparison oracle.
4. `outputs` composes the actual sparse router, actual source graph compiler,
   new round producer and existing physical constructor/estimator/comparator
   machine. `frontClock` pays source preparation and handoff, and
   `mainTime` pays the actual constructor and numerical consumer. The proof
   does not infer a machine clock merely from the table's size.
5. The finite-input branch is physical and charged. `AEth4.route3` first
   checks the sparse domain and uses the fixed finite router. Its result is
   always a valid sparse formula above the semantic cutoff, preserving
   satisfiability on each original sparse canonical formula. The chosen
   cutoff is fixed with the machine. Large formulas route identically, which
   permits the eventual clock estimate in the original variable count.
   Neither small formulas nor zero-variable formulas are excluded from the
   all-sparse correctness conclusion.
6. `physical_clock_all_large` absorbs the entire polynomial front and
   handoff into the quasipolynomial bound. It uses the sparse encoding bound
   in original variables and the graph's fixed polynomial upper bound.
   The supplement proves `clog2(N+2) <= 3*log2 N` for `N >= 2`, so replacing
   the integer logarithm costs only a factor nine in the exponent constant.

## Proof variation from the manuscript

The paper's proof chooses a public construction size above both the formula
variable count and the graph order, yielding `N^2 <= T`. The reused physical
implementation selects it above the graph order. The review confirmed the
candidate instead proves `N <= degree*|V(G)|` from the same graph's edge
lower bound and degree upper bound. Thus, once `N >= degree*T0`, the actual
square table has at least `T0` entries.

This weaker eventual lower bound is sufficient for the estimator's eventual
accuracy and leaves the quasipolynomial upper bound unchanged. It is a
valid proof variation for `det:time`; it does not certify the literal
intermediate inequality `N^2 <= T` for this physical construction. No change
to the manuscript is requested or made by this review.

## Axiom audit and remaining boundary

The core's eight printed declarations (`numeric_gap`,
`main_clock_quasipoly`, `outputs`, `classification_all_large`, `algorithm`,
`algorithm_correct`, `physical_clock_all_large`, and the endpoint) all depend
on exactly `propext`, `Classical.choice`, and `Quot.sound`. The supplement's
three printed declarations (`coefficient_eq_rational`,
`quasipoly_clock_real`, and the real-log endpoint) have the same standard
axiom surface. There is no `sorry`, `admit`, new axiom or opaque certificate
in the two files. See `replay.log` and `replay-real.log`.

These axiom lists do not remove the explicit upstream reduction records.
The result is relative to their existing approved mathematical and physical
interfaces and source-fidelity qualification. Independent statement review
and private replay are complete for these frozen files; production
integration, dependency/source-bound checks and release status remain with
the root integrator. This review does not establish the other pending v43
runtime statements.
