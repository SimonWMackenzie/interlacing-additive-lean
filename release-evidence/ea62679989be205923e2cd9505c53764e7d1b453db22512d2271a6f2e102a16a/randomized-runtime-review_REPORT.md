# Independent review of the v42 randomized runtime packet

26 October 2026. Reviewer: `v42_runtime_review`.

The source read-back finds no blocking defect in the packet's actual
graph-to-sampled-matrix execution, new threshold, output law, and complete
resource claim. A single fixed finite machine starts with graph bytes, a unary
round count, and the reserved fair-bit tape. It prints the new square table and
its actual new threshold. This is not a proof of the communication gap, source
compiler, estimator comparison, NP consequence, or ETH consequence.

**Accept for integration in this bounded scope.** All thirty frozen sources
compiled afresh with exit zero. The independent statement checks passed. The
all-declaration audit checked **894 declarations**, including private and
generated declarations, with only `propext`, `Classical.choice`, `Quot.sound`
or a subset. It inspected the one opaque value and found no new axiom, unsafe
declaration, partial declaration, or `sorryAx`. Original and replay source
hashes, the manuscript hash, and the project dependency hashes were rechecked
at completion. See [RECEIPT.json](RECEIPT.json).

Only `private-provenance-refs/3b7ed875b78f9c22a31c2240c74035119f5bed66aaf24d9e19ef76d4a666247b/randomized-runtime-review` was changed. No
Git operation, shared build, production edit, manuscript edit, worker launch,
or external model call was performed. At most one reviewer-owned compiler ran
at a time.

## Frozen sources and dependency evidence

The producer manifest SHA256 is
`8b22e47c99ba5cd395c03f3e7555e1ba3558a36d76aa2a4ec4786117dde075e6`;
the producer verification SHA256 is
`fa3f04478646cc2583439011343b9fa0349c74b2014f67fb254305c8201bb0b3`.
Copies are retained as [PRODUCER_MANIFEST.json](PRODUCER_MANIFEST.json) and
[PRODUCER_VERIFICATION.md](PRODUCER_VERIFICATION.md). All 26 source hashes
were checked against that manifest before copying. [FREEZE.json](FREEZE.json)
pins the 26 packet modules and all four new transitive numeric dependencies:
`V42Schedule`, `V42PublicSchedule`, `V42PublicCutoff`, and `V42PublicSize`.

Every new source is compiled into the reviewer's [replay/](replay/) directory
using Lean 4.30.0, commit `d024af099ca4bf2c86f649261ebf59565dc8c622`.
[REPLAY.json](REPLAY.json) records per-file exit codes, times, source hashes,
and private object hashes. [LEAN_PATH.json](LEAN_PATH.json) has only that
private directory and the root/package library caches: no producer private
objects supply a new module. The exact compiler version is in
[LEAN_VERSION.txt](LEAN_VERSION.txt).

[DEPENDENCIES.json](DEPENDENCIES.json) traces all 1,399 project-owned source
modules in the textual import closure: the 30 fresh snapshots plus 1,369
cached production dependencies. It pins the source and existing object hashes
of every cached production dependency, with zero missing project sources or
objects. Its 106 external-library import boundaries are explicit and are
qualified by the package-manifest, lakefile, toolchain, and compiler executable
hashes. Those external libraries and the entire production source closure
were not rebuilt by this reviewer. Root-owned fresh production gates remain
necessary after integration.

The frozen packet's original manuscript source SHA256 is
`1c7f0fedc92989087219c2773411a42f610503846c6cf1e2dea5ac18961684f7`.
Relevant anchors are `def:amplification-parameters`, `lem:full-schedule`,
`lem:sample-access`, `thm:uniform-reduction`, and `sec:sampling-algorithm`.
The canonical source lock was not changed.

During this review the root made the user's requested formal-verification
paragraph and bibliography edit. The final `main.tex` SHA256 became
`ec8af5767eccc1184e7a1b5f88979ab0a7ee9be60d91be4e61ec80aa66861f78`.
[SOURCE_COMPARE.json](SOURCE_COMPARE.json) independently compares a preserved
snapshot matching the original hash with the final source. The complete text
diff is [source-change.diff](source-change.diff): only the formal-verification
paragraph changed in `main.tex`. Nine runtime-relevant mathematical statement
and proof blocks, including the new recipe, full schedule, sample access,
randomized reduction and generated schedule, are exactly equal after line
ending normalization only. No notation, label or whitespace normalization was
used. This review's runtime conclusion therefore applies to those unchanged
mathematics in the final source; it does not separately certify the new
paragraph's whole-paper formalization claim or the bibliography edit.

## Exact new arithmetic and machine input

Let `n` be the graph's vertex count, `K` the supplied number of rounds,
`L=clog 2 n`, `ell=clog 2 (L+1)`, and `a=16+ell`. The packet physically
computes the following expressions from the parsed graph and unary `K`:

```
s  = 2^a                 q1 = s-2
q2 = 2^(L+2*a)           w  = 2^(8*a)
Q  = 2^(24*a)            h  = L+36*a
p0 = 2^(6+ell)           d0 = ell+7
B  = d0+K*h              H  = B+K
r  = 2^(B-1)
m  = 2^(clog 2 (16*(r+1)*clog 2 (r+2)*2^H))
```

`V42FullScheduleExpressions` contains literal finite arithmetic programs and
the exact evaluation equalities. `V42FullScheduleBatch` installs nineteen
actual results into the generator/printer bank. `V42RawGraphParameters`
first obtains `n` from the physical canonical-graph parser, constructs the
ordinary arithmetic input `(n,K)`, and runs that batch. A bank called
`prepared` or `expected` in a local proof is an intermediate state proved to
be reached; it is not externally supplied.

The complete external input of `CurrentAdditive.V42WRaw.finiteMachine` is

```
encode [EncodedGraph.encode g, replicate K true, tapeWord b N bits].
```

No public width, threshold, sample label, generator program, prepared bank,
per-entry evaluator, desired output, or runtime certificate is an input field.
The machine and `packetExponent` take no source constants, graph, or round
count as parameters. The numerical source constants occur only in proofs of
the public guards. An independent definitional check verifies that changing
those constants and guard proofs does not change `outputWord` for the same
graph, rounds, and bit blocks.

## Exact printed matrix, threshold, and probability event

The closed `packet_outputs` theorem prints exactly

```
encodeInstance <m,m,B, rowMajor (fun i j => R_K (xs i) (ys j))>.
```

Here `R_K` is `V39RecursiveTable.matrix` at the new widths and the actual
edge-only activity computed from the graph and exact repetition count.
`xs,ys` are the actual rounded sampler's labels, not an assumed sample.
Their complete recursive labels and repeated indexed positions are retained.

The physical path was traced below the wrapper names:

| Stage | Actual program and identity | Review finding |
| --- | --- | --- |
| Parse and compile public values | `V42RawGraphParameters.run`, `V42FullScheduleBatch.run`, exact expression evaluations | New widths and new `B` are physically produced from graph bytes and unary rounds. |
| Construct the sample generator | The actual `V39DeadSampleJoin`/`V39PhysicalSample` constructor at the supplied new widths | The finite generator is constructed; it is not included as advice in the input. |
| Interpret fixed-bit choices | `V39PhysicalShapeSample` and `V39PhysicalSample.sampleAtBudget`, with the proved draw cap | All reserved bit blocks are genuine fair-bit inputs; no success-conditioned tape is assumed. |
| Compute graph repetitions | `V42RawPublicRepeat.run_final` and `width_eq` | The actual edge count, padded width, and quotient are computed and retained. Only the unchanged `s,q2` source-width arithmetic is reused through `fullQ2_eq_old`. |
| Route printer fields | `V42WRaw.source_fields`, `threshold_field`, `printer_ready` | Every source field and the new threshold comes from the actual terminal bank; all printer work cells are blank initially. |
| Evaluate and serialize | `V39WEncodedTable.physical_from_bank`, consumed in `V42WRaw.physical_encoded_raw`, then `V39TypedPacket.outputs_of_run` | The actual graph activity evaluator writes all `m^2` Boolean entries and the dimensions/threshold header; framing, parsing and final output extraction are physical operations. |

The new threshold is `B=ell+7+K*(L+36*(16+ell))`, not an old generated
threshold. `V42RawSamplerOutput.final_threshold` identifies the actual batch
result. `V42WRaw.threshold_field` feeds that exact word to the header writer.
`finished_threshold` and `finished_word` show that it is preserved and printed.
There is no discarded-threshold limitation in this randomized packet.

`wordFromLabels` defines the semantic word with the same dimensions, matrix,
threshold and indexing. `outputWord_eq_fromLabels` is definitional. The
`output_event_error_200` theorem holds for **every event on that exact printed
word**, comparing the fair-bit implementation with
`V39RecursiveGenerator.sampleLaw`. That ideal law is the product of `m`
independent samples from the actual row law and `m` independent samples from
the actual column law, with the two groups independent. Its error is at most
`1/200`, which is strictly below the manuscript's `1/100` allowance. This is
an unconditional finite-law comparison for every public graph satisfying the
stated numerical guards; it assumes no communication lower bound or favorable
sample event.

`RoundedDraw.BitBlocks b N` contains all choices of `N` blocks of `b` Boolean
bits, and `bitBlocksLaw` is the repeated product of the fair-bit block law.
`tapeWord_length` proves the literal tape length is `b*N`. All reserved tapes
are covered. `every_output_valid` proves that every actual output decodes to
the advertised square instance. Positivity of its power-of-two side and the
exact `m^2` row-major payload length are proved in that endpoint.

## Complete clock, random-bit budget, and cutoff guards

Let `T=(K+1)*L`, and write `N` for the reserved draw count, rather than the
number of vertices. The packet derives its reservation from the actual
recursive sample requests. It proves

```
actual draw count <= N <= 2^(112*T)
b <= 160*T
b*N <= 2^(272*T)
raw input size <= 2^(275*T)
packed input size <= 2^(278*T).
```

The block precision is exactly `clog 2 (200*A*N)`, where
`A=max {512,4*s*(n+s),q2,w,Q,p0}`. It is not an assumed precision or
resource certificate. `V42FullSchedulePeak.all_peaks` bounds all intermediate
scalar values, including logarithm operands, sample argument, alphabet
maximum, and the complete reserved bit count. Thus the arithmetic clock is
charged even for values larger than the printed matrix header.

`packed_outputs_exponential` bounds the actual finite machine by

```
2^(packetExponent*((K+1)*clog 2 n)).
```

`packetExponent` is one closed natural number fixed before all graphs,
round counts and source constants. Its proof includes graph parsing, scalar
compilation, constructor-bank copies, precision copying, generator program
construction, the actual rounded interpreter, recursive-label codecs,
graph-dependent entry evaluation, all table cells, threshold and dimension
headers, input framing/decoding, and output serialization. Local helper
inequalities with scalar or clock bounds are fully discharged in this closed
endpoint; there is no supplied run or table-size premise.

The final exponential theorem requires `K>=1`, as the manuscript does.
It uses exactly the reserved tape with no arbitrary extra suffix. The more
general `packet_outputs` accepts any extra suffix and charges the full packed
input length; an unbounded suffix is not silently claimed to satisfy the pure
`n,K` bound. Short or malformed packed inputs are outside this endpoint's
stated domain. They are not random tapes of the prescribed reservation.

`V42RuntimeSchedule.FullTests` consists of the old numerical source-width
guards plus `V42PublicCutoff.fullLengthCutoff 0 <= L`. The old guard is used
for the unchanged `s,q2` repetition arithmetic, not as a proof of correctness
for the new `w,Q` recipe. New width/clock bounds are proved with the explicit
new length cutoff. The public `sourceCutoff gamma Delta` is the maximum of
the prior effective source cutoff and `2^(fullLengthCutoff 0)`.

`tests_all_large` discharges every runtime numerical premise from only
`gamma>0`, `Delta>0`, `n>0`, `n<=2*edgeCount`, `2*edgeCount<=Delta*n`, and
that public cutoff. `promised_packed_outputs` consumes this theorem directly.
Validity of the encoded graph and a nonzero vertex carrier remain explicit.
Neither a YES/NO promise nor a coloring is needed to execute the machine.
The cutoff can be very large, but is an explicit fixed integer depending
only on the fixed source constants.

## Proof-value audit and downstream boundary

The new `V42FullTableWriter` has one private opaque datum,
`fixedArithmeticData`. Its type packages only two fixed natural numbers with
equalities identifying them as `V39WTablePrepare.N` and
`UnaryBinaryEncoding.coefficient`. Its body is the corresponding pair with
reflexive equality proofs. It contains no execution, clock, size, correctness,
or desired endpoint proposition. Its projections are reconciled with those
exact constants by `prepCount_eq` and `headerCoefficient_eq` in the ordinary
clock proof. The audit explicitly inspects the opaque body; it is not accepted
merely because its name resembles arithmetic data.

The independent all-declaration audit and statement checks are retained under
[Audit.lean](replay/Audit.lean) and [Statements.lean](replay/Statements.lean).
Both compiled with exit zero; their complete logs are
[Audit.compile.log](Audit.compile.log) and
[Statements.compile.log](Statements.compile.log). The checks include the exact new width
and threshold formulas, dyadic sample side, lack of source-constant output
advice, complete input shape, strict `1/100` output-event comparison, and the
elementary conversion of the certified exponential bound to
`n^(2*packetExponent*(K+1))` for `n>=2`.

Downstream consumers must use this exact `outputWord`, `wordFromLabels`,
sample law, activity order, `B`, and sample side. In particular, joining a
finite theorem on `V42FullConstruction.actualState` or
`V42FullActualLabels.iterate_eq_actualState` still requires instantiating the
same graph/item ordering and activity; an old full-schedule theorem or a
similarly named matrix cannot replace that identity. The difference is
concrete: `LiteralEdgeEncoder.activity_eq_owner` expresses literal activity
as the owner's activity **after a selector permutation**;
`LiteralEdgeEncoder.matrix_eq_owner` proves the corresponding entry
conjugacy. Choosing `itemOrder` alone does not make the owner's activity
definitionally identical to the runtime activity. See the existing
`EdgeMatrixProductionConjugacy.lean`, pinned in
[ACTIVITY_BRIDGE.json](ACTIVITY_BRIDGE.json). The recursive carrier/law
transport must be retained when applying the finite theorem to this exact
printed sample. The root identifies the separately accepted
[compression and source-bound review](../compression-review/REPORT.md) and its
[receipt](../compression-review/RECEIPT.json) as closing that integration:
`V42GraphLiteralBounds.source_upper`, `source_rank`, and `source_no_bounds`
instantiate the generic `V39SelectorTransport.graph_D`, `graph_rank`, and
`graph_profile_iff` at the new widths, and `V42PrintedGraphGap` consumes those
original-law transports. That is complementary evidence owned by the other
review, rather than a result proved by this runtime packet.
[COMPLEMENTARY_MATCH.json](COMPLEMENTARY_MATCH.json) checks that all common
runtime/numeric source modules in the two reviews have identical frozen source
hashes. This packet proves the
runtime and representation side of that join, not the finite NO profile,
compression success probability, estimator midpoint, all-input source-CNF
compiler, or randomized ETH consequence.

No new mathematical defect has been found in the bounded packet scope.
Fresh production compilation, transitive audits of the integrated source,
and the root's final manuscript-level joins remain separate obligations.
