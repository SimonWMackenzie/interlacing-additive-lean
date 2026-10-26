# Independent review: the final randomized growing-error endpoint

2026-10-26. Reviewer `v42_proof_review`. **Accept for integration at the exact
source-relative randomized growing-error endpoint scope described below.**

Statement, quantifier, actual-program, probability-law and source/ETH read-back
are complete without a mathematical repair finding. All eighteen frozen modules
independently replayed with exit 0, and the reviewer-authored proof-cone audit
passed. No source repair is required for acceptance.

## Frozen objects and exact claim

The worker's frozen manifest SHA256 is
`aae6f29246cf654352d9f2a23b468e1e099dc7ae1a061174107fc145e84b6932`.
It was copied to `randomized-endpoint-snapshots/WORKER_MANIFEST.json`; every one
of its eighteen module source hashes was independently checked before copying
the sources. That directory owns the private replay objects and logs, exact
compile order, independent source-hash list, and reviewer-authored audit.

The two principal source hashes are:

| File | SHA256 |
| --- | --- |
| `V42RandomizedClassEndpoint.lean` | `850fc484255ea276e117bd42fbff6c5086842b1602d52fa37d5e32057cf41e07` |
| `V42UniformReduction.lean` | `07ffca819b81f3de0bc45fa14aee8423a7b9ecb0a18318a2f4bcc6ea16e10a1c` |

The manuscript source reopened by label for this review is v42 `main.tex`,
SHA256 `1c7f0fedc92989087219c2773411a42f610503846c6cf1e2dea5ac18961684f7`:
`def:table-estimation`, `thm:uniform-reduction`, `thm:quantitative`, and its
proof `proof:thm:quantitative`.

The final square-table theorem states, literally, that for every fixed real
`0 <= c < 1/8`, under `AEth2.RandomizedSparseETH_R20`, there do not exist a
single permitted estimator and a natural size cutoff giving success at least
`2/3` within error

```text
c * log2(T) / log2(log2(T))
```

on every sufficiently large positive square Boolean table whose side is a
power of two. The unrestricted table theorem follows by restricting an
all-rectangle estimator to those square tables. Here `T` is the **number of
table entries**, not side length or the formula's variable count.

The theorem parameters explicitly retain the approved external
`DinurReduction` and `BOTReduction (booleanOccurrence D)` records. It does not
construct those cited source theorems or silently make them new project axioms.

## The permitted estimator and quantifier order

The actual `PermittedEstimator` structure and extraction proof were opened.
It contains one fixed raw estimator machine, one fixed rational-comparison
machine, a value interpretation, and uniform polynomial clocks on every valid
explicit table and every actual output/tape. The comparison clock may depend
on a fixed polynomial bound for rational code length, but not on the particular
table, midpoint, output or estimator tape. It is a restriction to positive
half-integer rational comparisons, sufficient for the paper's more general
permitted numerical convention. A hardness result for this weaker comparison
requirement applies in particular to the manuscript's permitted estimators.

`V42RandomPermittedFamily.extract_all` extracts **one** normalized estimator
and amplified classifier from `A`, before any graph, formula, number of rounds,
sampled matrix or construction tape is chosen. It proves the original event
law is preserved on every valid table, including inaccurate estimator outputs.
It does not condition on estimator success or allow a new estimator per table.

The request uses the literal table-only encoding of the sampled payload and
the numerator `2B+K`. Its threshold is exactly `(2B+K)/2 = B+K/2`. The rational
code bound is proved uniformly using the actual table entry count, so the
comparison-machine premise is discharged rather than assumed at the final
endpoint. The actual printed matrix word is projected without replacing its
payload, padding it again, or adding the public `B` field to the estimator's
matrix-only input.

`GrowingSquareAccuracy` quantifies all square Boolean payloads of the permitted
shape; `extracted_accuracy` transfers this property through the proved original
event-law identity. The final theorem does not require accuracy only on a
chosen family or only on successful construction tapes.

## Sharp `c<1/8` calculation

The new schedule has `h=L+36*(16+clog2(L+1))` and the exact current square sample
size, using `r=2^(B-1)` and `H=B+K`. The new
`V42PublicSize.sample_sharp` gives, beyond its explicit scalar cutoffs,

```text
clog2(T) <= (4+epsilon) K L.
```

`V42ETHArithmetic.gap_exceeds_twice_error` combines that **new** sample-size
estimate with both actual sparse-source relations

```text
N <= Delta*n,
n <= N*(clog2(N+2))^p,
K = floor(N/(clog2(N))^2),
```

and proves `2*error(T) < K` eventually for each fixed `0 <= c < 1/8`.
The first source inequality is weaker than the manuscript's displayed
`2N <= Delta*n`, so using it is safe. The second controls `L` from above; the
first ensures `L` eventually exceeds the sharp-size cutoff. The proof does
not assume a small-o table-size conclusion.

The inherited `V39ETHArithmetic.core` and `exists_accuracy` were inspected:
they are scalar lemmas with the exact coefficient-four condition
`2c(4+epsilon)(1+epsilon) < 1-epsilon` and the actual `c<1/8` premise. The new
proof supplies the changed size hypotheses to those generic scalar lemmas.
The coarse exponent `10000` appears only in resource estimates and does not
replace the leading coefficient four in the error calculation. Positive
denominators and `T>=4` are proved before applying the logarithmic error bound.

## The exact probability law of the printed table and classifier

`V42JointEstimatorLaw.independentLaw` is the actual finite product of the whole
construction fair-bit-block law and a new independent uniform classifier tape.
The classifier tape length is the same for all payloads at fixed dimensions,
proved from the exact request length. No desired final decision law is a
hypothesis.

The finite graph result used is the separately reviewed
`V42PrintedGraphGap.no_probability`: on the NO graph promise, the actual
new raw printer's matrix has exact cost `B+K` with probability at least
`49/50` under its fixed bit law. Every YES construction tape has cost at most
`B`. No rank certificate, good sample or assumed sampling-success event is
supplied to this result by the endpoint.

The amplified permitted classifier has conditional error at most `1/100` on
every fixed table whose midpoint gap holds. The joint YES acceptance is at
least `99/100`; the joint NO acceptance is at most `3/100`, charging both the
`1/50` construction failure and classifier failure. Construction failures and
inaccurate outputs remain in the original law. No table or event is
renormalized after retaining a successful sample.

`V42RandomizedETHEndpoint.machine_probability` was opened. It proves that the
**single physical uniform random tape** has this same construction/classifier
product law, using disjoint bounded tape segments, the literal bit-block
bijection, and the proved carrier-fit bounds. `actualAlgorithm_probability`
applies that identity to the actual program's `[true]` output event.

The exact new raw table/request identities were also opened in
`V42RawRequestSemantics`: the printed word is the instance encoding of the
same `V42RawRequestPacket.matrix`; the classifier request is the same midpoint
header followed by that printed word's matrix-only projection. The physical
caller uses `V42RawRequestPacket.classified_outputs`, so the law and actual
execution concern the same request and Boolean payload on every tape,
including fallback outcomes.

## Uniform physical program, packing, and paid running time

`V42RandomizedETHEndpoint.actualAlgorithm` uses the generic previously reviewed
effective-tape packaging helper, but supplies the **new actual**
`V42SourceClassifier.machine`, `time`, `output`, `runs_carrier`, and `extend`.
The helper's actual `AEth2.ETape.Algorithm` definition was inspected: it stores
a single fixed finite decision machine, a length-only effective random-tape
carrier with an actual length machine, every-carrier-tape execution, and
extension invariance under every unused suffix. It is not a structure carrying
SAT correctness or a subexponential decision conclusion as input.

The caller is a physical composition. Its source front constructs the routed
source graph, unary round count, bounded construction block and independent
classifier block, serializes the actual input bank, and only then invokes
the new raw table/request/classifier program. In particular, the theorem does
not start the final SAT algorithm from an assumed prepared graph bank.

The actual statements and bodies of `V42SourceClassifier.source_exists`,
`front_runs`, `machine`, `time`, `runs`, and `sourceClock_sparse` were opened.
`source_exists` chooses a fixed machine and constants **before** every input
word and random tape. Its proved source clock charges physical routing,
source compilation, tape cuts and bank framing. The complete caller's clock
adds the actual framed-word copy cost and `V42RawClassifierClock.cap` for
the raw printer, midpoint request, estimator/comparator and tape handling.

`V42RandomizedPhysicalClockFits.raw_clock_and_entries_fit` derives the actual
raw constructor clock and its actual entry count from
`V42FullTableClock.raw_table_pure` and the proved physical-clock identity.
`actual_size_caps_sparse` also pays the actual encoded graph bytes and the
framed bank lengths. `actual_time_sparse` proves subexponential time in the
**original formula's variable count**, with an explicit polynomial factor in
original encoded input length. It uses the proved polynomial closure of the
actual caller cap and the proved source-front clock. No completed run, target
clock, polynomial packing assumption or desired decision-time bound occurs
as a final hypothesis.

The separate uniform graph-printer theorem
`V42UniformReduction.uniform_reduction` fixes one `V42WRaw.finiteMachine`
independently of the graph, promise constants and round count. From the
literal packed encoding of graph/unary-`K`/fair bits it proves actual output
and decoding, square power-of-two dimensions, random-bit usage, every-tape YES
cost, and the `49/50` NO exact-cost event. Its time is bounded by
`(n+2)^(absoluteConstant*(K+1))` and random bits by
`(n+2)^(544*(K+1))`. The packet-clock proof includes actual input decoding and
output serialization and bounds the packed input's literal length. In the
final CNF algorithm, construction of that physical bank is additionally paid
by the source-front proof just described.

## Concrete uniform source and finite exceptional inputs

The actual source is `t10Graph D B Phi`, the same graph printed by the
approved fixed Dinur/Boolean/BOT source compiler. The external records were
opened: they contain fixed reduction maps, actual all-input bit functions,
polynomial machine implementations, completeness/soundness and the stated
source size/degree bounds. `DinurReduction` explicitly prevents a zero-size
NO constraint system; the local source bridge proves positive actual graphs,
looplessness, incidence/degree/count relations, the positive coloring gap,
and the original-variable edge floor. These are upstream cited inputs and
proved local transfers, not new source axioms.

`V42SourceGeometry.source_all_large` derives the new runtime tests and the
quasilinear graph-size bound from this same actual graph. The semantic source
cutoff is separately derived using the original-variable floor. The source-law
theorem then discharges the actual graph gap and degree premises of the new
printed-table result; it does not leave those graph promises as desired-output
certificates at the final class endpoint.

`permitted_routed_correctness` applies the physical sparse router with density
slack `cs+2`, so even `cs=0` has a valid fixed fallback. It preserves SAT on all
valid original `cs`-sparse formulas while routing finite small cases to a
sufficiently large fixed source. The old router's actual SAT-equivalence and
actual all-input physical source-front theorems are reused, not an old
randomized hardness theorem.

## Final quantifiers and ETH contradiction

For each fixed estimator `A`, eventual table threshold `T0`, fixed `c<1/8` and
sparse density `cs`, the proof chooses one sufficiently large **constant**
cutoff and one fixed actual program `M`. Correctness holds for every valid
`cs`-sparse input, including the finite exceptions. The same `M` satisfies

```text
for every epsilon>0, there exist C,d,N0 such that
time_M(input) <= C ceil(2^(epsilon*N)) (|input|+1)^d
```

beyond `N0`. The program is chosen before `epsilon`; no new algorithm is
chosen per accuracy exponent or input size. The clock is independent of the
random tape and is accompanied by actual runs on every prescribed tape and
every unused suffix.

`permitted_estimator_sparse_decider` therefore produces an actual
`AEth2.ETape.Algorithm` satisfying `SparseDeciderR20 cs`. The actual definitions
of `SparseDeciderR20`, `RandomizedSparseETH_R20` and `not_R20_iff` were opened:
ETH asserts that some fixed density has no such bounded-error sparse-SAT
algorithm. The new result produces one for every density, and the final
theorem applies that direct logical contradiction. Randomized sparse ETH is
an explicit premise; deterministic ETH is not silently used as a randomized
assumption. The model is the stated effective-tape R20 model, with the
existing proved links from the admitted prefix/draft ETH formulations.

The only final substantive inputs are the permitted-estimator accuracy
assumption, the fixed constant conditions `0<=c<1/8`, the two approved external
source records, and the named randomized sparse ETH assumption. There is no
final premise asserting a graph promise, good sample, physical execution,
event-law identity, packing/runtime bound, or SAT-decider correctness.

## Verification status and limits

Frozen private replay: all eighteen modules completed in dependency order,
exit 0, using one private compiler at a time. The principal final endpoints use
only `propext`, `Classical.choice`, and `Quot.sound`. No forbidden source
construct was found by the independent scan.

Independent reviewer-authored audit:
`randomized-endpoint-snapshots/EndpointProofReviewAudit.lean`. It checks actual
theorem types/proof values, standard axioms, rejection of old physical callers,
old full iteration/amplifier/incoming/sharp-size endpoints and old randomized
class proofs, while allowing only the generic old effective-tape packaging.
It separately requires the final square-class cone to include the new actual
caller/run/extension/clock/law, current printed YES/NO matrix gap, new full
iteration/weighted incoming and new sharp `c<1/8` arithmetic.

Audit result: exit 0. The six-root audit traversed 79,518 declarations and
found no forbidden old caller, final class, full iteration, incoming/alignment,
or sharp-size endpoint. The separate final square-class cone traversed 79,470
declarations and contains all required new actual run/extension/clock/law,
printed-matrix gap, full iteration/weighted incoming and sharp-size arithmetic
dependencies. See `EndpointProofReviewAudit.log` in the snapshot directory.
The reviewer-authored audit source SHA256 is
`7f739e4fcb1d13ea051744b709ecfb2d4288afabcd613fe325431f4045acab96`.

One nonblocking traceability cleanup: `V42ETHAsymptotics` still has two
unqualified inherited `#print axioms` commands for old scalar schedule names.
Its actual new gap proof calls the new public-size theorem; the independent
proof-cone audit checks that distinction. A later cleanup should qualify the
intended printed names and record the changed hash.

This independent review uses the previously reviewed frozen finite mathematics,
constructor, sampler/printing, compression and physical-caller dependency
interfaces. It does not freshly rebuild every inherited production dependency
or replace their separate independent reviews. Fresh production dependency
replay, final source lock, authoritative obligation records and paper-level
release gates remain root-owned. Production/manuscript files were read-only;
no shared build, Git operation or subdelegation was performed here.
