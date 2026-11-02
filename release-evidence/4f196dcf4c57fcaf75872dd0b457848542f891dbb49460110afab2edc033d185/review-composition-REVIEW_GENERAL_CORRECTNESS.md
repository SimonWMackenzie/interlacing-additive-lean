# General source correctness and deterministic caller review

Reviewed on 2 November 2026 for selected v43 `thm:time-tradeoff`. The four
frozen modules below pass bounded independent semantic review and private
Lean 4.30.0 replay. They prove actual source-gap classification, derive
nonnegative error from accuracy, and physically compose the arbitrary-gap
deterministic front, request constructor, and comparator. The final
runtime and finite-prefix endpoint remain separate obligations.

## Frozen inputs and replay

The worker confirmed the four files frozen before copying. Exact hashes:

| File under `general-revision3/V43TimeTradeoff/` | SHA-256 |
| --- | --- |
| `SourceCorrectness.lean` | `5b9b6eaa561664a310e585896ca49a27847017743b45663e383db45cf61ad9a8` |
| `DeterministicFront.lean` | `6a3bd915b95ee09913110934e0d4ba8b98f68de68ae112be41382c7d8e8cc80b` |
| `DeterministicCaller.lean` | `fc2032b1e7720eccf6b577a086e72a0dca848bd66142183ab63aae1dba2e19d3` |
| `ErrorNonnegative.lean` | `5690e1adc9e1a66321c41e565004f3fbb1085d823583226326ea7e5fbad85ee6` |

Replay reused the exact previously replayed Accuracy, Numerics,
SourceBounds, and revised ParametricSource objects. It also reused the
worker's compiled `CurrentV43.MixedCaller.Request` dependency and existing
production/package objects. The corresponding dependency source was read;
its SHA-256 is
`c3a3fb6174be302f4d83c02d56f8fde5d7ddf745a78ae46a34ba829f6d7be682`.

The first replay attempt stopped before elaboration because a private
`V43TimeTradeoff` directory shadows later roots for that namespace. The
already reviewed dependency sources and objects were copied into the same
private namespace directory. The second sequential replay passed for all
four modules; logs are `general-revision3/*.replay.log`. All thirteen
printed theorem/definition axiom reports contain only `propext`,
`Classical.choice`, and `Quot.sound`. There was one private compiler and
no shared build or clean dependency rebuild.

## Actual source law and same-table correctness

`sampledSource` is the actual `V42RawRequestPacket.matrix` of the inherited
source graph and rounded construction bits. The source graph is computed
by the fixed Dinur/Boolean/BOT source compiler. The numerical public tests
concern that exact graph. `sampledSource_yes` obtains its proper coloring
from source satisfiability and then applies the actual every-tape YES
theorem. `sampledSource_no` obtains the source gap from unsatisfiability,
transfers the same endpoints to the physical edge scan, and applies the
actual rounded-construction probability theorem.

Consequently the construction's `49/50` successful-NO probability is
proved from the source; it is not an assumed final answer certificate.
The same actual sampled table, square dimensions, communication cost, and
public midpoint appear in both the source theorem and the estimator
classifier theorem. `randomized_source_correctness` uses the independent
construction/classifier product law and gives YES acceptance at least
`99/100`, NO acceptance at most `3/100`. The deterministic-estimator
specialization gives every-tape YES correctness and NO rejection at least
`49/50`.

These theorems retain actual entry-count bounds, the public numerical tests,
the source cutoff, and the strict error-gap condition. These are genuine
consumer prerequisites. No fixed logarithmic round schedule, ETH claim,
assumed classifier execution, or finished SAT algorithm is introduced.

## Error nonnegativity is derived

`error_nonnegative_of_probability` proves that a nonnegative error random
variable cannot be at most a negative bound with probability `2/3`.
It identifies the putative event with the empty event and contradicts its
probability lower bound. The randomized square accuracy premise therefore
implies `0 <= a(S)` after the already proved monotone transfer from the
actual square entry count to `S`.

The sample specialization may use the all-false table of the same legal
dyadic square dimensions; global accuracy applies to this table and no
construction event is needed. The stored-table specialization uses the
actual padded square and its proved power-of-two side. Both retain only
the same actual upper/lower entry bounds already needed for applying
accuracy. Thus the earlier `hu` premise can be discharged without adding
an assumption to the manuscript theorem.

## Deterministic front and caller

`deterministicFront` is a fixed actual variable-clock producer. It prints
the source graph, a zero floor, and the exact unary gap produced by the
schedule. On a positive-variable canonical formula the output is the
literal `V42RuntimePrefix.input` consumed by the deterministic constructor.
It does not replace the arbitrary schedule by a fixed `rounds` function.

`deterministicFront_clock` correctly pays graph production, output-field
framing, copying, concatenation, and the actual schedule execution. Its
polynomial is in raw input length, actual unary output length, and actual
schedule clock. It imposes no input-polynomial bound on the gap itself.
It is a useful clock bound, but `Schedule.paid` still has to be consumed to
turn it into a polynomial of the displayed `S(N,k)`.

`routedFront` composes the actual sparse router with that front on every
raw word. `routedRequest` composes it with the fixed deterministic
graph-to-midpoint requester. The latter's execution and request-length
bounds are proved from the actual constructor, using the source-only
amplification and request exponent. `deterministicCaller` then runs the
single extracted deterministic estimator/comparator machine on that exact
request, retaining all previous clock terms and transfer costs.

All these machines are fixed by the source, schedule, cutoff/density, and
estimator before any particular input formula. In particular the
source-only construction constant and amplification from SourceBounds
remain independent of the estimator and schedule. The estimator and
schedule may affect the final fixed polynomial runtime exponent; that is
permitted by the manuscript statement.

## Finite-prefix boundary

`routedFormula_original` correctly states identity on valid `cs`-sparse
formulas above the cutoff, using the underlying router at density `cs+2`.
Thus the original variable count and original supplied gap are preserved
where `deterministic_caller_correct` is invoked. The latter proves literal
SAT-bit execution only for those sufficiently large formulas, with actual
table upper/lower bounds and the strict gap condition.

It does **not** yet prove all-small-size correctness or a total runtime
bound in the theorem's original `S(N,k(N))`. The inherited router does have
`AEth4.routed4_sat_iff` for every sparse valid input, so it can support a
finite-prefix completion: the final consumer must actually invoke that
equivalence or add a separate charged exact finite solver. For arbitrary
routed outputs the density is `cs+2`, and their variable counts are at
least the cutoff. Those facts must be used when choosing source cutoffs
and applying `Schedule.paid`. A theorem only about original formulas above
the cutoff is insufficient by itself to mark the complete endpoint done.

No blocking semantic defect was found at the four modules' stated scopes.
The remaining final consumer must assemble source-only `C/A`, actual
clock absorption, all eventual hypotheses, finite-prefix correctness and
runtime, and all four estimator/construction cases. Root production
admission remains separate. Earlier reviews and snapshots were retained;
only this private review directory was written.
