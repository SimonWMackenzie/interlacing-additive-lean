# Revised parametric caller review, 2 November 2026

The frozen revised Source/Carrier/Caller set passes bounded independent
semantic review and sequential private Lean 4.30.0 replay. It supplies one
fixed machine computing the actual source graph, arbitrary implemented gap,
actual sampled table midpoint request, and classifier output from two
physically separated random blocks. No desired SAT decision or probability
law is assumed. The execution results retain the explicit tape-fit and
numerical public-test hypotheses; final paid-runtime and probability
composition remain consumer work.

All earlier reports and private snapshots were retained unchanged. The
latest reviewed parametric set is in `parametric-revision2/`, to preserve
the preceding frozen Source snapshot as provenance.

## Exact frozen set and replay

The worker confirmed these three files frozen together after compilation.
Their hashes were recomputed before replay:

| File under `parametric-revision2/V43Parametric/` | SHA-256 |
| --- | --- |
| `Source.lean` | `cd402174082883d3f64b3f4a9e5067ceeacf4f6feefac46ed3ed297f1a0e65f5` |
| `Carrier.lean` | `615b0d01f3c03a204b7eb96e51a2c7b91da2253a68945373b2294afc16fce149` |
| `Caller.lean` | `d4d94541252eb47d0cc202210cb9957e2bb1fcb1ce73883a5014a06d18099f3e` |

All three were compiled serially, with this revision's private directory
first on `LEAN_PATH`, followed by existing production and package object
directories. All exited successfully. Logs are
`parametric-revision2/{Source,Carrier,Caller}.replay.log`. The nine printed
theorem axiom reports contain only `propext`, `Classical.choice`, and
`Quot.sound`. No shared build or clean dependency rebuild was run.

The revised `Source.lean` differs from the earlier reviewed source only by
adding the local `Classical.decEq` instance for `V42RawMidpointRequest.Raw`
and whitespace. It aligns the bank-index representation with the
production request packet, allowing literal identity across modules.
There is no mathematical statement change. The Carrier source hash is
unchanged; its earlier semantic assessment applies and it was recompiled
against this revised Source.

## Fixed source-to-classifier execution

`Caller.machine D B C S` depends on the fixed approved source reductions,
fixed classifier, and implemented schedule. It is defined before every
formula, numerical public-test witness, construction tape, and classifier
tape. The graph and unary gap are computed by the reviewed source front;
they are not preloaded trusted values supplied with an execution premise.

`sourceWord_eq` connects the **literal** bank word emitted by the front
to `V42RawRequestPacket.inputWord`. It uses the actual sampled bit-block
view of the first `precision*reservation` bits and preserves the remaining
construction tape as `residual`. The inherited `word_view` theorem proves
that the reconstructed sampler word concatenated with that residual is
exactly the original tape. The only condition is that the sampler prefix
fits; no random values are inspected to choose the representation.

The equality is proved via canonical bank widening, rather than a claim
that two separately encoded banks merely decode to compatible values.
The revised local equality instance ensures that the typed bank-numbering
terms are aligned with the exact production packet machine.

`runs` composes `front_outputs` with the existing physical
`classified_outputs`. Its literal result is `C.output` on
`V42RawRequestPacket.request`, using the actual selected prefix of the
separate classifier tape. That request is exactly
`natField (2*B L K+K) ++ matrixWord L K (actual matrix)`, with
`L=clog 2 graph.vertices` and `K=S.gap Phi.variables`. Its matrix is the
same actual sampled matrix used by the production sampler/table printer.
It therefore has the same word, cost object, and midpoint convention as
the reviewed `Accuracy` family. No alternative table or threshold is
substituted at the classifier endpoint.

The output theorem requires public numerical `FullTests`, the actual
sampler-prefix length bound, and the classifier-prefix length bound.
None of these is an assumed SAT answer, comparison correctness theorem,
execution theorem, or final decision probability. `FullTests` governs
public construction numerics, not whether the formula is satisfiable.

The clock is the actual source-front composition clock plus the existing
requester/classifier cap at a quantity containing the physical source word
length, raw printer clock, actual sample entry count, and classifier-block
length. Its coefficients are fixed with the programs. The proof does not
choose a favorable random execution or drop an uncharged transfer.

## Fair carrier execution

`randomMachine D B C S R` composes the reviewed physical splitter with the
same source-to-classifier machine. It is fixed by the source, classifier,
schedule, and actual resource producer before the formula or random tape.
`random_runs` proves execution on every tape in the finite fair carrier of
length `carrierLength R (encode Phi)`.

For those tapes, both actual split blocks have exactly `blockLength` bits.
The theorem discharges the lower-level length premises from its explicit
uniform sampler-fit and classifier-fit hypotheses. The input is the raw
encoded formula paired with the carrier tape. The output is exactly
`randomOutput` on the two blocks delivered by `splitMachine`, with its
complete explicit `randomClock`. There is no prepared graph or bank state
in the theorem's input.

Together with the reviewed `split_law`, this gives the correct physical
starting point for independent construction and classifier randomness.
The first sampler prefix and second classifier prefix are disjoint. A
final consumer still has to prove that the output event depends on those
prefixes exactly as in the existing finite-law accuracy theorems.

## Exact remaining consumer premises

1. Instantiate the paid resource producer `R` and prove its actual output
   length/clock bounds. Prove `precision*reservation <= blockLength` and
   the uniform `C.tapeLength request <= blockLength` premise for every
   relevant request.
2. Consume `Schedule.paid`, source/formula size bounds, actual constructor
   bounds, and the resource producer bounds to put the carrier length,
   carrier-generation clock, source/front clocks, split clock, and final
   `randomClock` below a fixed polynomial in the displayed `S(N,k)`.
   The finite carrier's length is physically computable, but this file
   does not yet prove it is paid within `S^{O(1)}`.
3. Establish the exact equality between `randomOutput`'s event under the
   carrier law and the construction-bit/classifier product law used in
   `Accuracy`. The reviewed `split_law` and existing bit-block word view
   are applicable ingredients; the output-law bridge is not asserted as
   already proved here.
4. Supply the actual YES/NO gap facts, estimator accuracy, monotone error
   transfer, and eventual cutoffs, then finish the bounded-error SAT
   consumer and finite-size exact patch. This caller directly handles the
   randomized-construction path with an arbitrary selected-tape
   classifier; it is not by itself all four final endpoint theorems.

No blocking semantic defect was found in this revised set at the stated
scope. Root production compilation, transitive axiom audit, exact
source-bound admission, and final consumers remain separate gates. Only
this private review directory was written; there were no production,
shared-build, Git, or manuscript changes.
