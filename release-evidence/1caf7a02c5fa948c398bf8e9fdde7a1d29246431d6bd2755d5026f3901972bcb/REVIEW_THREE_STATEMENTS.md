# Source correspondence for the three new v43 runtime statements

The three new runtime statements have matching algorithmic endpoints at the
scope described below. The unified four-case join passed independent private
replay and literal type audit. The deterministic corollary has this reviewer's
earlier independent replay; the randomized corollary and the other three
general branches have the separate independent reviews cited in the receipt.
No blocking source-correspondence defect was found.

This report concerns **only three new statement rows**. It neither replays
their already reviewed components nor re-reviews the 51 retained checked
correspondence rows. Those rows keep their separate evidence and authority.
Production integration, the aggregate build, source-bound coverage receipt,
and any public release remain the root integrator's responsibility.

## Exact source and anchors

The selected manuscript is `versions/v43/source/main.tex`, SHA256
`BFDE23B90F50785939095A6D37B7B247965EE6C45BEACA9011A8963DEC3CC9D6`.
An immutable copy is `source-main.tex`. `SOURCE_BLOCKS.json` independently
binds the literal statement and proof bodies, with explicit proof association:

| Statement | Statement lines | Proof lines | Recommended primary Lean declaration |
| --- | --- | --- | --- |
| Theorem 9.7, `thm:time-tradeoff` | 3229--3256 | 3258--3280 | `CurrentV43.General.time_tradeoff` |
| Corollary 1.4, `thm:quantitative` | 337--347 | 3306--3360 | `CurrentV43.RandomizedRate.quantitative_algorithm` |
| Corollary 1.5, `det:time` | 353--362 | 2910--2952 | `CurrentAdditive.V43DeterministicRate.deterministic_estimation_to_sparse3SAT_real` |

The natural square-table companion anchors are
`CurrentV43.RandomizedRate.quantitative_square_algorithm` and
`CurrentAdditive.V43DeterministicRate.deterministic_estimation_to_sparse3SAT`.
The generic theorem itself already requires accuracy only on square tables
of power-of-two side. The ordinary all-table premise implies that restriction.

The manuscript's estimator convention is at lines 1008--1012: worst-case
polynomial time, ordinary bounded-error accuracy, and polynomial-time
comparison with polynomial-length binary rationals. Sparse inputs, every-tape
worst-case time, and the allowed runtime-constant dependence are stated at
1034--1040. Logarithms are binary by line 1044. The formal endpoints use these
conventions; they do not assume arbitrary real outputs can be compared for free.

## Theorem 9.7: all four randomness combinations

The independently replayed join is `General/Main.lean`, frozen source SHA256
`4EBF10DBE0E84921C4FB281D0D0036E158804A0C248D8FF4BCDEECC21B6A1ADF`.
`time_tradeoff` proves the literal type
`exists Amp C, 2 <= Amp and 1 <= C and forall cs, FourCases Amp C cs`.
This chooses both constants before every estimator, error function, accuracy
cutoff, positive implemented gap schedule, and sparse density. Having `C`
independent even of the density is stronger than the manuscript's allowed
per-density constant. It introduces no extra premise.

`amplification` is the actual deterministic construction's fixed amplification.
`sizeConstant` is the maximum of the deterministic and randomized source-only
construction constants. It contains neither estimator nor schedule. The
enlarged-constant branch theorems use monotonicity of the error function to
transfer the strict error-gap condition down to the native table bound, and
then enlarge the same algorithm's clock upward. No estimator-dependent
resource exponent is substituted for the construction constant in the error
condition.

`FourCases` contains the following proved output statements:

| Construction | Estimator | Result |
| --- | --- | --- |
| Deterministic | Deterministic | One actual all-input finite producer, exactly correct on every sparse canonical formula |
| Deterministic | Randomized | One actual finite fair-tape algorithm, error at most one third on every sparse formula |
| Randomized | Deterministic | One actual finite fair-tape algorithm, error at most one third on every sparse formula |
| Randomized | Randomized | One actual finite fair-tape algorithm, error at most one third on every sparse formula |

Each result bounds that same algorithm's charged worst-case time eventually
by `c*S(N,gap(N))^d`, in original formula variables. The displayed sizes are
exactly `(N+2)^(C*(k+1))` and `(N+2)^(C*Amp^k)`. Correctness has no large-input
restriction. The charged, SAT-preserving finite router handles small sizes;
above the fixed cutoff it is literal identity, preserving the original gap
and variable count in the runtime conclusion.

The gap schedule contains an actual finite producer, its exact unary output,
and a paid polynomial bound in `N+gap(N)`. This is the implementation form of
the manuscript's gap-computation premise. There is no upper bound requiring
the gap to be polynomial in `N`, no hidden monotonicity of the gap, and no
assumed SAT algorithm, final probability, desired output, or whole-program
clock. `FourCases` is constructed from the four endpoint proofs; it is not
an opaque assumed conclusion certificate.

The branch evidence is the final deterministic review, mixed endpoint review,
and final arbitrary-gap randomized-construction review listed in the receipt.
The new join itself and `LiteralJoinAudit.lean` passed private Lean 4.30.0
replay, exit zero, with exactly the three standard axioms in their endpoint
audits. Only the join and literal audit were replayed for this final review;
existing branch objects were reused after checking their frozen provenance.

## Corollary 1.4: the complete coefficient and exponent range

The final endpoint source is `randomized/V43RandomizedEndpoint.lean`, SHA256
`9DD3EF4EA78FF2D55651A0E536ED84FF2DB5FA96FEBB4E27A491C4BAB99E703F`.
Its complete runtime join is `V43RandomizedRuntime.lean`, SHA256
`3B58FE48088297459EC39AD20C22732D23112875BC76FD0EB692B465E259A569`.

`quantitative_square_algorithm` and its unrestricted-table specialization
quantify over every real `0 <= c < 1/8`, every real `8*c < alpha < 1`, and
every fixed density. They return one actual all-input fair-tape algorithm,
correct with bounded error on every sparse formula, with its complete
`totalTime` eventually at most `ceil(2^(K*N^alpha))`. This is the stated
`2^{O(N^alpha)}` bound, with constants allowed to depend on the fixed data.
The case `c=0` and exponents arbitrarily close to `8*c` are included.

The final correctness is for the actual machine's exact finite output law,
not a separately supplied estimator/source success event. Its total clock
pays the same physically printed carrier, independent fair bits, source and
table construction, estimator/comparison, framing, and both router executions.
The final theorem has no source-correctness, probability or runtime conclusion
as a premise. The independent composition review of the final Runtime/Endpoint
pair closes the component-level qualifications in the earlier arithmetic and
construction reviews.

## Corollary 1.5: effective fixed constant and deterministic clock

The earlier independently replayed core and real-log supplement retain frozen
hashes `0FCB84E9EB6B89BDB0061765ADC1B72013712C83BF9F71F82B5DAC30872EF624`
and `835E7D77CD6DE98ABA160036D8D586F4FF45E05F600B7F89500B88AE3B2DD05C`.
They choose positive `c_*` before the estimator, its eventual accuracy cutoff,
and the density, then return one actual deterministic machine, correct on
every sparse formula, with eventual charged time `2^(C*(log2 N)^2)`.

The constant is the cast of the explicit rational `1/(8*clog2 Amp)`. The actual
amplification is a power of two, so this is the proof's `1/(8*log2 Amp)`.
The integer-log clock conversion is separately proved. No ETH assumption or
desired SAT machine appears. The square-only accuracy sufficiency is present
in the core, and the real-log theorem states the all-table specialization.

## Explicit proof variations and model boundary

The randomized corollary uses the physically implemented dyadic schedule
`2^floor(a*clog2(N)/b) / clog2(N)`, with positive rational `a/b` between
`8*c` and `alpha`. It generally differs from the manuscript's displayed
`floor(N^beta/ceil(log2 N))`. The proved dyadic bounds preserve the sharp
coefficient and the entire exponent range. This is a valid alternative proof
of the corollary, not an assertion that both integer schedules are identical.

The deterministic physical source chooses its public size above the graph
order, whereas the manuscript also includes the original variable count.
The formal source uses `N <= degree*vertices` and therefore eventual table
growth, rather than certifying the literal intermediate `N^2 <= T` for that
implementation. The weaker lower bound suffices for every estimator cutoff
and leaves the endpoint and runtime unchanged. The randomized analysis also
permits the weaker source floor `N <= degree*n` in place of `2*N <= degree*n`;
this changes no asymptotic coefficient or conclusion.

Randomized algorithms use the explicitly charged finite fair-tape convention:
a fixed actual machine physically prints the tape length, the tape is uniform
independent bits, and a fixed deterministic caller runs on the literal framed
input for every tape. The total time includes the printer, one operation per
fair bit, and the proved bound for writing every framed symbol. This is not
a claim that Lean constructs a separate monolithic probabilistic transition
kernel. The convention extends the inherited selected-tape model and has its
own reviewed initialization-cost evidence.

The approved `DinurReduction` and `BOTReduction (booleanOccurrence D)` records
remain explicit source interfaces, with their existing author-owned fidelity
qualification. Source-program constants are fixed before estimators and inputs;
no numerical uniformity over every alternative upstream implementation is
claimed. These three implications add no ETH, SAT lower-bound, optimality,
sparsification-cost or NP-hardness premise. This correspondence does not change
the manuscript or silently remove the inherited external source boundary.

## Admission recommendation

Recommend `verified_correspondence` for exactly `thm:time-tradeoff`,
`thm:quantitative`, and `det:time`, using the declarations above and the
source/proof body hashes in `SOURCE_BLOCKS.json`. Retain the prior 51 rows
through their existing separate evidence. Root production compilation,
transitive audit and source-bound final coverage are still required before a
release claim. If a later AI-methodology edit changes only surrounding prose,
root may retain this correspondence after explicitly verifying these exact
three statement and proof body hashes are unchanged; the whole-source hash
and any line locations must then be refreshed.

No production files, manuscript text, Git state, shared build or publication
were changed by this reviewer. Private compiler processes were serialized.
