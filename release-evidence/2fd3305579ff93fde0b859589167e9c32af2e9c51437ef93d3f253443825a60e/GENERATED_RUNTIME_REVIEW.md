# Independent review of the v42 generated runtime packet

26 October 2026. Reviewer: `v42_runtime_review`.

The packet computes and prints the square padding of the actual new generated
construction from graph bytes and a unary round count. The definitions and
closed resource statement are suitable for integration in that scope. They do
not supply a correct new threshold-and-matrix request to a decision procedure.
That separate endpoint remains necessary. No NP or ETH consequence is certified
by this runtime review.

Only `private-provenance-refs/8298f9497f4d60eef82dbab202993e2a0f36d3b477ab7c7b901d3c12c94e044f/runtime-review` was changed. No Git command,
shared build, production edit, manuscript edit, worker launch, or external model
call was performed. At most one reviewer-owned compiler ran at a time.

## Frozen inputs and private verification

The seven runtime source hashes match the producer's `runtime/MANIFEST.json`
(SHA256 `57b6456cae16d81ff1968d3853be2bfcb2db3306ef32e3dbcdc1c4d18cfdc532`).
The producer README hash was
`f6a656b12261318e8fc4f9dc4df28852825f0ee8808bc270eeaf62b413aff14f`.
[FREEZE.json](FREEZE.json) records the exact original and replay source paths,
hashes, and lengths for all seven runtime files and their six changed v42
numeric/constructor dependencies. All thirteen were copied to [replay/](replay/)
and compiled afresh, in dependency order, without the producer's private object
files.

[REPLAY.json](REPLAY.json) records thirteen exit-zero private compilations,
their times and output hashes. The compiler was Lean 4.30.0, commit
`d024af099ca4bf2c86f649261ebf59565dc8c622`; see
[LEAN_VERSION.txt](LEAN_VERSION.txt). [LEAN_PATH.json](LEAN_PATH.json) contains
only the replay directory and existing root/package library caches.

The independent all-declaration axiom audit and additional statement examples
are in [Audit.lean](replay/Audit.lean). The corrected audit compiled with exit
zero and checked **446 declarations**, including generated and private
declarations owned by all thirteen snapshots. Every transitive axiom cone is a
subset of `propext`, `Classical.choice`, and `Quot.sound`; there is no `sorryAx`
or additional axiom. The audit also checked the complete input shape, selector
leastness, exact new widths, legacy-threshold discrepancy, and threshold-free
square output. See [Audit.compile.log](Audit.compile.log) and
[RECEIPT.json](RECEIPT.json).

The first audit driver had an invalid documentation comment before `run_cmd`.
It still checked all 446 cones and examples, but exited one on that comment
syntax error. The failed driver and log are preserved as
`Audit.first-failed.lean` and `Audit.first-failed.log`. Changing the comment to
an ordinary block comment produced the clean rerun; no frozen proof source
changed.

Existing production dependencies were inspected through their actual
definitions and generic theorem statements. Their selected source hashes are
in [READBACK_SOURCE_HASHES.json](READBACK_SOURCE_HASHES.json). Their entire
production source closure was not rebuilt by this reviewer. Fresh production
dependency builds and the root's source-bound gates remain required.

The reviewed manuscript source SHA256 is
`1c7f0fedc92989087219c2773411a42f610503846c6cf1e2dea5ac18961684f7`;
see [MANUSCRIPT.json](MANUSCRIPT.json). The relevant anchors are
`def:amplification-parameters`, `det:construction`, `proof:det:amplifier`, and
`lem:generated-schedule`. This review does not retarget any source lock.

## What the machine actually does

| Step | Definitions and checked connection | Finding |
| --- | --- | --- |
| Read the graph and rounds | `V42RuntimePrefix.input` is exactly `encode [graph, [], replicate K true]`; `V40GraphConstructorFront.counts_result` recovers the actual vertex and edge counts from a valid encoded graph. | No supplied counts, parameter list, source table, matrix, or selected run enters the external input. |
| Choose the dyadic size | `V42RuntimeSelector.expression` physically computes `max k0 ((Nat.clog 2 n + 3)/4)`. `V42PublicCutoff.generatedExponent_minimal` proves this is the least exponent with `k >= k0` and `n <= 2^(4*k)`. | This is the new least-dyadic choice, with no root approximation or old search predicate. |
| Compute parameters | `V42RuntimePacket.terms_eval` checks the actual finite scalar programs against `q1=s-2`, `q2=2^(6*k)=s^6`, `s=2^k`, `w=2^(8*k)=s^8`, `Q=2^(24*k)=s^24`, `rep=q2/pow2Ceil(4*s*m)`, and `ni=4*s*(n+(s-3))`. The seed logarithm field is physically changed to `4*k`. | Exact new literal widths; no old generated width is silently reused. |
| Produce graph data | `V42RuntimeSource` prints the canonical indexed item-law bytes and the entire graph activity table using the physical law/activity loops. `V42RuntimeWords.source_outputs` identifies those bytes with the law and activity consumed by the new graph construction. | No supplied law, per-cell procedure, or prepared source context remains in the closed prefix. |
| Produce seed and fuel | `V42RuntimeSeed` routes the actual new context to the physical weighted lookup-seed constructor at `4*k`, then constructs the actual iteration driver's unary fuel. | The initial stored matrix is the new construction's lookup seed, and the round count is charged. |
| Run seven calls each round | `V42RuntimeWords.run` is definitionally `V42GeneratedConstruction.graphRun k (4*k) ... (4*k) j`. `round_outputs` instantiates `StoredMatrixEnvelopeStep.outputs` with the new parameters and that exact current stored matrix. | The functional and physical successor states agree on the same construction. |
| Print and bound | `V42GraphRuntime.public_source_bound` uses the actual iteration driver and physical square printer. It bounds the time and printed length of the same `publicRun ... K` square word in the original graph-byte length. | This is a closed execution/length theorem, not an assumed size certificate. |

The seven-call identity was checked below the wrapper level. `StoredRoundStages`
physically starts an eight-field bank, executes exactly seven successive stages,
and retains each earlier source for later requests. `StoredRoundData.call`
orders them as the column-label source, inner source, outer source, metadata
source, base source, selector source, and final interlace source. Each
`StoredSourcePhase` calls `CodeDWholeConstructor.machine`, then prints its
actual positional law and tuple list. Its source is definitionally
`IndexedLaw.construct 8192`, through `executableCodeD 8192`. `StoredMatrixPhysicalStep`
then prints all actual Boolean cells and both complete rational weight vectors.
No successful source call, desired profile, or source array is a premise of the
closed runtime theorem.

The tolerance recipe also has the new values `eta=s^-2`,
`theta=(512*Q)^-1`, and `deltaU=eta/(16*w)`, proved by
`V42Schedule.recipe_exact`. These are correctness/cutoff quantities; the
generated machine does not consult an old tolerance predicate or receive them
as advice. The finite profile, restoration, and source-promise proofs must use
these new quantities separately. This review does not certify those finite
proofs merely from their numerical definitions.

## Fixed constants, charged inputs, and remaining premises

For a fixed `k0`, define

```
M = V42GraphRuntime.machine k0
A = V42GraphRuntime.amplification k0
C = V42GraphRuntime.sourceExponent k0
```

All three definitions are fixed before the graph and `K`. `A` is a power of
two and at least `2^64`. The closed theorem bounds both the actual execution
time and square-word length by

```
((EncodedGraph.encode g).length + 1) ^ (C * A^K).
```

The final endpoint assumes exactly a valid encoded graph, `0 < g.vertices`,
`2 <= k0`, `2*g.edges.length <= Delta*g.vertices`, and `2*Delta <= k0`.
It derives the exact repetition/width equality internally using dyadic
divisibility. There is no YES/NO hypothesis, target matrix/run premise,
resource certificate, independently supplied source law, or precomputed bank.
Taking a sufficiently large fixed cutoff depending on the fixed source
constants is permitted; proving the chosen cutoff meets all correctness
requirements belongs to the numerical/endpoint owners.

The prefix includes graph parsing, least-size selection, all scalar arithmetic,
law/activity production, context routing, seed materialization, and fuel
writing. Per-round bounds include all seven actual Code D runs, rational
encodings, retained banks, complete lists, table cells, and both next-round
weight vectors. These are physical Boolean-stack programs; expression
evaluation is not a unit-cost machine instruction. The bound on the input
length includes unary `K`, before the generic iteration argument absorbs it
into the fixed `A^K` factor. The square formatter and its intermediate output
are also covered by composition clocks and actual output-length bounds.

`outputs_with_tail` is a generic helper with an explicit tail-execution
premise. `public_outputs` and `public_source_bound` discharge it with the
physical square formatter; the closed endpoint has no such premise.

## Threshold boundary found during review

The inherited square formatter internally computes

```
V40StoredThreshold.thresholdNumber (4*k) K
  = LookupSeed.exponent (4*k) + 1 + K*(50*k).
```

The new generated threshold has increment `40*k`. Therefore this formatter
must not be cited as producing the correct new threshold-and-matrix request.
The independent audit includes a kernel-checked example of the discrepancy.
The root has assigned the correct new threshold/midpoint request to a separate
endpoint worker; that follow-up needs its own review.

This discrepancy does not invalidate the accepted square-word endpoint:
`StoredMatrix.squareWord` contains only square dimensions and table cells.
`DeterministicETHPhysicalSquare.squareMatrixMachine_outputs` and
`V40StoredSquare.stage_outputs` prove the same square output for every
intermediate threshold `b`. The final matrix projection discards `b`.
The old threshold's physical computation and temporary serialization are
included in the proven formatter clock. There is no uncharged operation or
incorrect threshold in the promised final square word.

## Integration conclusion

**Accept for integration:** the literal statement review, thirteen fresh
source compilations, and 446-declaration transitive axiom audit all pass for
the seven frozen runtime files in the generated square-table execution and
resource scope above. Original and replay source hashes were rechecked at
completion. Keep the separate new-threshold,
finite YES/NO/profile, source-classification, NP, and ETH obligations visible.
Private replay, a fresh production build, and complete manuscript-level
correspondence remain distinct evidence levels.
