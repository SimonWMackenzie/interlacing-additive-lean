# Independent admission review: compression to the actual printed v42 matrix

Accept the eight frozen compression-join modules for production integration, subject to the root's fresh production builds, import renaming and release gates. I found no mathematical, quantifier, probability-law or same-object defect in this join.

The final YES theorem bounds the communication cost of **the actual raw requester's matrix** on every tape. The final NO theorem gives cost exactly `H=B+K` for that identical matrix with probability at least `49/50` under the actual fixed fair-bit-block law. The compatible catalogue, sampling event, source cost/profile, selector transport and implemented sampler error are proved along the chain; none is silently supplied as a desired-conclusion premise of the final theorem.

This review changed only `private-provenance-refs/b1bf47d9e3bf10b99ce133c84edba2c21ec417730647d6d3dd63b3d5f55640e1/compression-review`. It ran no Git command or shared build, launched no workers, and ran one compiler at a time.

## Frozen and replayed objects

[FREEZE.json](FREEZE.json) pins the eight reviewed source modules. [PROVIDERS.json](PROVIDERS.json) pins **all 53 new private dependency providers** in their import closure, with both source and object SHA-256 values and their actual provider paths. [SHARED_IMPORTS.json](SHARED_IMPORTS.json) pins the 51 immediate shared-library imports reached by that private closure. No private module had a shadowing provider.

Every packet source was copied to `replay/` and compiled afresh there. All 53 private providers were copied, source and `.olean`, to `providers/`; the independent replay never imported a new module from the implementation worker's original private directory. [LEAN_PATH.json](LEAN_PATH.json) records this resolution order: review packet, review provider snapshot, then the existing production and package libraries. [REPLAY.json](REPLAY.json) records eight exit-zero results and their private output hashes.

The provider objects were pinned and reused, not all freshly recompiled by this worker. Their mathematical/component reviews retain their separate owners. The fresh root production build remains necessary for complete dependency-source replay after admission.

## Literal final statements and remaining inputs

The complete final signatures are in [SeamAudit.compile.log](SeamAudit.compile.log).

`CurrentAdditive.V42PrintedGraphGap.every_tape_yes` concludes, for every actual bit-block tape,

```text
D (V42RawRequestPacket.matrix g hg K cc deltaV zeta tests bits)
  <= B (clog_2 g.vertices) K.
```

It requires a valid finite graph with positive vertex count, the numerical runtime tests, a proper three-coloring of its actual edge map, and the tape. No hardness profile, rank bound, sampling success, target cost or successful execution is an input.

`CurrentAdditive.V42PrintedGraphGap.no_probability` concludes

```text
49/50 <= (RoundedDraw.bitBlocksLaw
    (V42RawSamplerJoin.precision g.vertices K)
    (V42RawSamplerJoin.reservation g.vertices K)).prob
  (fun bits => D (V42RawRequestPacket.matrix ... bits)
    = H (clog_2 g.vertices) K).
```

Its remaining mathematical inputs are:

- valid graph data and positive vertex count;
- a positive degree bound `Delta`, the actual degree bound, a positive rational `gamma`, `n<=2*m`, and `2*m<=Delta*n`;
- the fixed effective semantic source cutoff `V42FullCutoff.sourceCutoff gamma Delta <= n`;
- the genuine external graph gap: every three-coloring leaves at least `gamma*m` monochromatic edges;
- `V42RuntimeSchedule.FullTests` at the actual public graph size and edge count.

`FullTests` is numerical. Its definition contains the inherited public edge-width tests and the new public length cutoff, with no matrix, sample outcome, probability conclusion or physical-run certificate. The packet's `public_runtime_tests` proves the canonical instance from the same graph-size and promise data. `runtimeCutoff_le_semanticCutoff` proves that this introduces no additional size cutoff. Thus the tests are an explicit, discharged numerical interface rather than a hidden semantic assumption. The theorem allows `K=0` as well; its restriction to the manuscript's `K>=1` is immediate.

## Checked chain and same-object seams

| Seam | Checked evidence and result |
| --- | --- |
| Current parameters and exact sample count | `V42PublicSchedule` defines the new full recipe, `B=seedCost+K*fullOverhead`, `H=B+K`, `rankBound=2^(B-1)`, and the literal power-of-two side `m=pow2Ceil(16*(r+1)*clog_2(r+2)*2^H)`. `V42Compression.sampleSide_eq` proves exact equality with `squareDrawsV38`; it does not merely prove a larger sample bound or assume a sampling certificate. |
| Rank gives a compatible-set catalogue | The imported `RankCountV38` proof builds its catalogue from the real rank. It stacks both output bits, bounds the stacked rank by `r+1`, constructs a finite common-zero catalogue and covers all compatible domains of depth `H-1`. Neither the catalogue nor its cardinality bound is a premise of `ideal_failure` or the final graph theorem. |
| Independent two-sided sampling | The compression theorem uses independent original row and column laws. `row_first_compression` explicitly swaps the product order to the inherited two-stage proof. The two failure contributions are combined by its proved finite-law two-stage bound. The rank bound also holds after the first sampled-column restriction. Separate positions remain present for repeated labels. |
| Universal and exact sampled cost | `sample_upper` is actual local precomposition, valid for every label tuple, including repeats. With the original cost upper bound `<=H`, the complement of sampled cost `<H` is exactly sampled cost `=H`. `ideal_exact` therefore proves probability `>99/100` of **equality**, rather than silently converting a lower bound into equality. |
| New iteration to complete labels and laws | `V42GraphOwnerBounds` invokes the new `V42FullIteration.upper_iteration`, `rank_iteration` and `no_iteration`. It then rewrites by `V42FullActualLabels.iterate_eq_actualState`. This is equality of the full state: finite row/column carriers, original rational laws, and entry function. `actualState` explicitly uses the new `q₁,q₂,w,Q` and the complete recursive `Row`, `Column`, `laws` and evaluator. No same-named old iteration is used in place of the new successor. |
| Owner activity to literal printed activity | `V42GraphLiteralBounds` explicitly instantiates `V39SelectorTransport.graph_D`, `graph_rank`, and `graph_profile_iff` with the new seed width, `q₁,w,Q`, while `s,q₂` are fixed by the actual graph width identity. This generic transport proves a recursive row/column bijection induced by the literal selector permutation and its `Fin.cast`. It does not assume the two activity maps are equal. |
| Original-law preservation across that permutation | `graph_matrix` gives exact entries at corresponding complete labels. `graph_laws_pushes` follows from the pointwise rational weight equalities in `laws_weight`, proved by induction through both successor laws. The original `255/256` and `1/256` two-family weights are retained. `graph_profile_iff` transports restrictions using these same laws and surjective bijections, in the correct direction from the owner result to the literal evaluator. |
| Actual public repetition | The literal source uses precisely `V42RawPublicRepeat.repetitions g` and its proved `width_eq g ... tests`. The owner theorem is instantiated with that same repetition and identity. The `cc,deltaV,zeta` arguments supply numerical proofs; they do not change the literal repetition, labels, source matrix or tape law. |
| NO robustness at both weights `3/5` | `source_no_bounds` yields the exact original-law two-threshold profile of the literal matrix at `rho=2^-L`. The source cutoff supplies `L>=1`; hence `rho<=1/2`. The `j=0` profile applies whenever row and column weights are at least `3/5`. The integer/natural casts preserve the lower-bound direction. This discharges the generic compression robustness premise. |
| Literal sampled matrix | `V42PrintedCompression.matrix_eq_sampled` is proved by `rfl`: the sampled function is definitionally `V42RawRequestPacket.matrix` at `V42WRaw.labels ... bits`. Its `Fin m` rows/columns retain every draw, including repeated labels. No successful subset, deduplication or alternate sampled table replaces it. |
| Encoded cost event | `V42EncodedCostEvent.HasCost C` is a predicate on a decoded emitted word. `hasCost_encode` uses exact `decode_encode` and `tableGame_rowMajor`, with `m>0` proved from the actual side bound. It establishes equivalence with the cost of the original indexed `m*m` matrix. The encoded threshold field does not masquerade as its cost. |
| Whole-output event error | `V42WRaw.output_event_error_200` is for every predicate on the exact emitted word and the actual `bitBlocksLaw(precision,reservation)`. It instantiates the checked rounded sampler at the new widths, public alphabet and proved draw reservation. The comparison law is exactly `sampleLaw`, namely the iid product of the same complete recursive laws used by the NO profile. This is a bound on the whole output event, not a one-coordinate error asserted for a correlated sample. |
| Correct probability arithmetic | `printed_exact` applies that error theorem to the encoded cost-equality event. The code uses the lower side of the absolute error bound. Ideal equality probability `>99/100` loses at most `1/200`, so implemented equality probability is `>197/200`, which implies the stated `>=49/50`. There is no reversed difference, unjustified independence step or missing second sampler-error charge. |
| Physical output and midpoint request | `V42RawRequestPacket.outputs` proves that one fixed machine outputs its actual request on the encoded graph, unary `K`, and the exact rounded tape prefix with any suffix. The review-only [SeamAudit.lean](replay/SeamAudit.lean) independently proves by definitional equality that `V42WRaw.outputWord` encodes the row-major payload of this exact `matrix`, and that the physical request is `natField(2*B+K) ++ matrixWord(matrix)`. It also proves the exact `H=B+K` identity. No physical execution is assumed as a premise of these reviewed conclusions. |

The physical graph parser, printer and sampler implementation providers were inspected at the output/request definitions and their actual joining theorems. Their complete runtime and low-level machine proof audits remain with the runtime reviewers; this admission review checks their exact use by the finite-gap chain. The CNF source reduction, estimator classification, joint classifier randomness and final physical CNF caller are outside this packet.

## Source correspondence

The author's attachment is pinned by SHA-256 `e9eb48925f087a64141c4b756ae3293856a87b353acae33f3fdc802b33f0f535`. The inspected current source has SHA-256 `1c7f0fedc92989087219c2773411a42f610503846c6cf1e2dea5ac18961684f7`. [SOURCE_COMPARE.json](SOURCE_COMPARE.json) records the following comparisons:

| Source block | Attachment lines | Inspected current source lines | Comparison |
| --- | --- | --- | --- |
| `thm:compression` statement | 2927–2944 | 2953–2970 | Exact text |
| Its proof | 2945–2974 | 2971–3000 | Exact text |
| `lem:sample-access` statement | 2998–3005 | 3024–3031 | Exact text |
| Its appendix proof | 4616–4712 | 4665–4762 | Only added hyperlink anchor/label |
| `thm:uniform-reduction` statement | 3013–3028 | 3040–3055 | Exact text |
| Its proof | 3030–3051 | 3057–3078 | Exact text |

The explicit ideal failure `<1/100`, implemented error `<=1/200`, exact `B+K` NO cost, per-tape YES guarantee, side length and preservation of repeated sample indices agree with those source blocks. The new wrapper uses positive rational laws because those are the actual source laws; the imported generic finite-law compression theorem also permits zero-weight outcomes as in the general source statement. The final source lock remains the root's responsibility during concurrent authorized manuscript finishing.

## Independent compiler and axiom evidence

All eight packet modules passed the independent private replay under Lean 4.30.0, commit `d024af099ca4bf2c86f649261ebf59565dc8c622`, with `relaxedAutoImplicit=false`. The independent [SeamAudit.lean](replay/SeamAudit.lean) also compiled successfully and has no warnings.

The packet's eighteen transitive axiom checks and the nine additional review identity/physical/conjugacy checks are all contained in `propext`, `Classical.choice`, and `Quot.sound`. The exact `H=B+K` identity uses no axioms. Source scanning of all eight packet sources and all 53 new provider snapshots found no `sorry`, `admit`, new `axiom` or opaque assumed conclusion.

There are three harmless packet lint warnings: an unused automatically included `NeZero g.vertices` instance in `wordFromLabels_hasCost`, and two unused simplification arguments in `no_probability`. No implementation source repair is requested. An initial replay invocation was rejected before elaboration because PowerShell did not preserve an unquoted `-D` argument; quoting the compiler flags fixed that review-command issue. Its log is retained separately from the eight successful final compilations.

## Admission boundary

The accepted objects are exactly the hashes in `FREEZE.json` together with the provider identities in `PROVIDERS.json`. The root should integrate these sources with the appropriate qualified imports, run fresh production dependency builds and axiom checks, and retain this report with the source-bound statement map. Existing component reviews are still needed for the pinned provider implementations; this join review does not replace all of them.

No open mathematical gap was found in the finite printed-matrix gap chain. It is not, by itself, a certificate of the downstream raw-CNF classifier, ETH contradiction, whole-paper completion, publication or a finished physical runtime audit.
