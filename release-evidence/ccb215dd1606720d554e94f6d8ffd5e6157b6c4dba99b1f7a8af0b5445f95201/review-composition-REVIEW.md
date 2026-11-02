# Independent composition review, 2 November 2026

The three frozen candidate modules pass private Lean 4.30.0 replay and a
bounded independent semantic review. They establish valid estimator
classification/probability results, elementary resource absorption, and a
fixed source-preprocessing machine. They do **not** alone establish the full
`thm:time-tradeoff` SAT algorithm or its runtime. No production admission or
public correspondence promotion is claimed.

## Frozen inputs and replay

Target: selected `papers/randomized-additive-hardness/versions/v43/source/main.tex`,
SHA-256 `bfde23b90f50785939095a6d37b7b247965ee6c45beaca9011a8963dec3cc9d6`,
`thm:time-tradeoff` and proof, lines 3230-3287. This source identity was
rechecked directly during this review.

The authors of the candidate modules confirmed that these files were frozen
before they were copied here. Hashes were recomputed on the private copies:

| Private input | SHA-256 |
| --- | --- |
| `V43TimeTradeoff/Accuracy.lean` | `3ea2a6304d863ae1d0ea5c506e2070e07a6146cdcd2328526e3fc9ff4579615a` |
| `V43TimeTradeoff/Numerics.lean` | `6acb56159c5ffce9b01cb67dda09963945f703fafea4080e1fe87469d3ff5d4e` |
| `V43Parametric/Source.lean` | `51248906443499f7a04d6b72ec66629e5e69e49d86a633d61b9876163ef0c15d` |

Replay used this private directory first on `LEAN_PATH`, the existing
`.lake/build/lib/lean` second, and each package's existing compiled object
directory after that. `Numerics`, `Accuracy`, and `Source` were compiled in
that order with one sequential compiler. There was no shared Lake build.
All three exited successfully. Logs are the adjacent `*.replay.log` files.
The ten printed theorem axiom reports contain only `propext`,
`Classical.choice`, and `Quot.sound`. The private sources contain no
`sorry`, `admit`, new `axiom`, `unsafe`, or `native_decide`.

The replay relies on already compiled production dependencies. It is not a
clean rebuild or a source-bound production release gate.

## Estimator correctness and literal identity

`Accuracy.lean:27-36` states accuracy only for positive square tables with a
power-of-two side, on or above an arbitrary entry-count threshold. The
error function is arbitrary and monotone. There is no logarithmic error
specialization, ETH premise, or conclusion-bearing SAT certificate.

`Request` at line 61 is the sum of both complete request families. Both
extracted estimators depend on the permitted estimator alone; they are
chosen before the graph, gap, payload, and random tapes. Validity and the
single polynomial midpoint-length bound are proved for both request
families. The preexisting extraction contracts retain one estimator
machine and one rational-comparison machine, with coefficients independent
of the particular request. The random normalization preserves the raw
output law on every valid word; the deterministic extraction preserves its
actual output there.

For the deterministic construction, the accuracy predicate is instantiated
with the actual `R.square` matrix and its row-major `squareWord`.
`StoredMatrix.square_cost` identifies its communication cost with
`D R.entry`. The comparison request is the actual source request, with
numerator `2*threshold+K`, hence midpoint `threshold+K/2`.
`V42ActualSource.run_yes/run_no` provide the source gap for this same `R`.
There is no substituted table or independently chosen threshold.

For the randomized construction, `f x` is a table at the actual fixed
sample dimensions. The accuracy word is exactly its row-major matrix
word. Its public numerator is `2*B L K+K`, and its cost in both accuracy and
gap assertions is the same `D (f x)`.

The monotonicity step correctly moves the allowed error from actual entry
count `T` to the upper bound `S` using `T <= S`. The strict condition
`2*a S < K` correctly separates both sides of the midpoint, including the
strict comparator convention.

## All four randomness cases

| Construction / estimator | Proven conclusion | Remaining construction premise |
| --- | --- | --- |
| Deterministic / deterministic | Literal classifier output equals the SAT truth bit | Source table is sufficiently large and has at most `S` entries |
| Deterministic / randomized | YES acceptance above `99/100`; NO acceptance below `1/100` | Same entry bounds and nonnegative `a S` |
| Randomized / deterministic | Every YES construction tape accepts; NO rejection probability at least `49/50` | Every-tape YES cost and actual-law NO gap probability |
| Randomized / randomized | YES acceptance at least `99/100`; NO acceptance at most `3/100` | Same construction gap assertions and nonnegative `a S` |

The randomized/randomized theorem uses
`V42JointEstimatorLaw.independentLaw`, which is the product of the complete
construction law with a fresh uniform classifier tape. The second tape
length is common to all payloads because all corresponding request words
have exactly the same length; `conditional_probability` equates the
resulting conditional law with the actual classifier law. Thus the proof
does not silently reuse construction randomness for estimator repetition.
The `3/100` NO error is the sum of `1/50` construction failure and `1/100`
conditional classification failure. Weak versus strict bounds are all
well below `1/3`.

The generic finite law `mu` and table map `f` are deliberate interfaces,
not assumed final decisions. A final caller must instantiate them with the
actual fair-bit construction carrier, output map, and gap theorem. These
modules do not yet prove that caller identity.

## General gap computation and physical source front

`Numerics.lean` proves that the displayed randomized size with `C >= 1`,
and the deterministic size with `A >= 2, C >= 1`, dominate `N+k+2` for
arbitrary natural `k`. It imposes no polynomial upper bound on `k(N)`.
`charged_composition` is a correct arithmetic implication from four actual
clock bounds to a polynomial in `S`. It does not supply those clocks or a
machine by itself.

`Source.lean:18` packages an actual finite gap-printing machine, its exact
unary output, and a per-density polynomial bound in `N+gap(N)+1`. Its
`paid` constants precede every formula of that density. This is a valid
implementation premise for the theorem's paid schedule. It is not a
certificate of SAT correctness.

`kFront_outputs` puts the computed gap alongside the original formula and
preserves the supplied construction tape. `uniformMachine` is chosen once
from `FrontUniform.front_uniform_raw D B`, before the formula, gap, and
tape. `source_outputs` feeds that same word to the fixed source graph
machine and the same typed bank-frame formatter as the production
constructor. The result contains the actual `t10Graph D B Phi`, the exact
unary schedule gap, and the unchanged construction tape.

`front_outputs` adds a `PairMap` wrapper, preserving the separate classifier
stream. This fixed machine is independent of the particular formula,
construction tape, and classifier tape. It has an explicit execution
clock. The proof does not inspect either stream to choose a machine.

No artificial restriction to an old subexponential `ETape` carrier is
needed for this general theorem. Input-dependent finite fair-bit carriers
are legitimate provided the final fixed machine receives those tapes and
their actual lengths and generation/reading costs are charged.

## Obligations still belonging to the final consumer

1. Choose one effective absolute amplification constant and, for every
   fixed density, a constant `C` that bounds the **actual** source
   preparation, construction time, table entry count, and paid tape lengths
   by the corresponding displayed `S(N,k)` for every relevant gap.
2. Derive eventual `T >= T0` for these actual outputs as `N` tends to
   infinity. The current accuracy theorems rightly take this as `hT`.
3. Use `Schedule.paid` and the source/formula encoding bounds to dominate
   the actual `sourceClock/frontClock`. `paid` is not yet consumed in any
   theorem of the frozen `Source.lean`.
4. Connect the physical table-producing/request-producing tail, the
   estimator/comparator/majority tail, and the independent tape splitting
   to these exact words, thresholds, and laws, with one machine per fixed
   source, schedule, and estimator. Supply the actual-law premises in the
   randomized construction rows above.
5. For randomized estimators, discharge the explicitly retained
   `0 <= a S` premise from the error convention or the nonempty successful
   accuracy event and monotonicity. This is a small logical obligation,
   but is not silently proved in the candidate statements.
6. Produce the total SAT algorithm, including exhaustive-search handling
   of the finitely many sizes before the eventual hypotheses hold, and
   then establish its `S(N,k(N))^{O(1)}` bound. Merely applying
   `charged_composition` is insufficient without those physical runs.

No blocking semantic defect was found in the three frozen modules at
their stated scopes. Admission is appropriate as independently reviewed
components, subject to root production compilation, transitive axiom
audit, exact source correspondence, and the remaining consumer work.

Only files in this private review directory were written. No production
source, shared build products, manuscript, Git state, or public inspector
was changed by this review.
