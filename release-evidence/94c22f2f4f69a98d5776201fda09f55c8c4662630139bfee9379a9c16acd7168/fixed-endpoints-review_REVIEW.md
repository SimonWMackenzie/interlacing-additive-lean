# Independent review of the V42 fixed-gap endpoint packet

## Decision and scope

Accepted for production integration, subject to the root's normal fresh
production build and source-lock gates. No mathematical, same-output, or
unresolved-premise defect was found in the six frozen modules.

The packet proves the literal all-input encoded-CNF fixed-gap reduction,
NP-hardness of the encoded communication decision language, and the
deterministic fixed-additive consequence `NP ⊆ P`. The last consequence uses
only a permitted estimator's accuracy on positive explicit tables; a stronger
intermediate theorem already needs accuracy only on positive square tables
whose side is a power of two. The existing `P ⊆ NP` adapter gives the usual
`P=NP` formulation if that final wording is needed.

## Frozen inputs and replay

The author confirmed the six-module freeze at manifest SHA256
`dbaa2a29dac900564d72bb59f02f5f191637ae20d30963a56360c0b8ad136330`.
Every source and log hash in that manifest matched before copying. Exact
source copies were replayed sequentially in this directory with Lean 4.30.0,
one private compiler, and private output objects. The original
`fixed-endpoints` directory was excluded from `LEAN_PATH`, so none of its
objects could satisfy a review import. Other separately owned private
provider objects and the shared dependency library were read-only.

All six modules compiled successfully in the declared order. The independent
`SameOutputReadback.lean` checks the new request/rectangular threshold,
literal source-to-estimator-family identity, exact comparison request, and
closed final endpoint types. `IndependentAudit.lean` checks all 84 named
packet declarations with transitive `collectAxioms`; only `propext`,
`Classical.choice`, and `Quot.sound` occur. Used private helper proofs are
included transitively. Logs and `RECEIPT.json` retain the results. Direct
private-provider source hashes are recorded separately in
`DIRECT_DEPENDENCY_HASHES.json`.

## Threshold and same-output checks

- The formatter physically computes
  `thresholdNumber L K=LookupSeed.exponent L+1+K*(10*L)`.
  With the actual source's `L=4*selected`, this is exactly the seed cost plus
  `K*(40*selected)`. Both the exported rectangular threshold and the midpoint
  numerator `2*threshold+K` use this new formula.
- The actual run is `V42GraphRuntime.publicRun` on the literal Dinur/BOT
  source graph. The selected exponent is computed from that graph's vertex
  count and the fixed promise cutoff. There is no coloring or desired-cost
  input to this constructor.
- `run_yes` uses the new constructor's YES bound. `run_no` derives the exact
  cost `threshold+K` from the new generated iteration and the same source
  graph's explicit NO promise. The base profile is the proved lookup-seed
  profile; no final profile or matrix-hardness record is supplied.
- `table_eq` identifies every entry of the serialized rectangular instance
  with the actual stored run. Its rows, columns and threshold are those of
  that same run. The source estimator word is its proved square padding,
  whose communication cost equals the original run's cost.
- `sourceInput` embeds precisely this run and round count into the new
  global permitted-estimator family. The extracted machine compares its
  actual output on this exact square word at the new numerator `2*B+K`.
  The global extraction proves a `48*(entries+1)^2` rational-code bound;
  no numerical comparison or header-length obligation remains in the final
  theorem's premises.

## Actual source and clock checks

`V42SourcePhysical` composes the all-input CNF graph producer, public selector,
seven-call weighted-state iterator and new output formatter. The explicit
tail bound is a power of the original encoded graph length with exponent
`exponent * amplification^K`. For each fixed `K`, ordinary producer-machine
composition gives a polynomial bound in the original raw CNF word length,
including the source producer, transfers and final output. `K` and the
external source records may determine the polynomial constants; neither the
input word nor its truth value chooses them.

The raw-word front uses the existing all-language CNF router, not the sparse
ETH router. Malformed, zero-variable and small inputs are handled by the
proved fixed router and preserve membership in the complete encoded-CNF
language. The producer's graph result is definitionally the T10 graph of
`fixedFormula w`; its truth-value equivalence is separately proved.

There are no target-word, execution, clock, prepared-state, source-profile,
graph-gap, or midpoint-comparison hypotheses in `fixed_gap_reduction`,
`fixed_gap_npHard`, `fixed_additive_square_inP`, or
`fixed_additive_np_subset_p`. A local generic composition helper accepts an
execution proof, but every use instantiates it with the actual pipeline's
proved run; it is not a final premise.

## Qualified old-threshold dependency

An initially overbroad audit rejected any occurrence of the old threshold
anywhere in a final proof's expression dependency graph. That occurrence is
real but harmless: the reused square formatter serializes an intermediate
old-format rectangle and then discards its threshold while printing the
square matrix word. `V40StoredSquare.stage_outputs` proves this output is
`R.squareWord` for **every** intermediate threshold, and all that internal
formatting work is charged by the existing clock.

`TraceOldThreshold.lean` records the exact path through
`requestExponent → request → V40DeterministicRequest.square →
V40StoredEnvelope.machine → V40StoredSquare.machine →
V40StoredRectangle.machine → fieldProducer → old threshold`.
This does not supply an old matrix gap or change the new exposed threshold.

The final audit therefore checks the appropriate distinction: four final
endpoint cones must contain the new actual source, new NO proof and relevant
new output printers and must exclude the old final hardness/gap endpoints.
Separately, six exposed semantic cones—new header, new rectangle, actual
threshold, source comparison, exported threshold equality, and source
classification—must contain no old threshold, threshold number or step cost.
All ten checks passed. The original overbroad failure log is preserved as
`logs/IndependentAudit.initial-overbroad.log`.

## Exact external boundary

The final source parameters remain the approved explicit `DinurReduction`
and `BOTReduction (booleanOccurrence D)` records. Their fields describe
external constraint/graph reductions, coloring completeness/soundness and
physical polynomial source compilers. They do not carry the desired
communication lower bound or a class-separation conclusion.

The NP consequences additionally expose `NPHard EncodedCNF.Language`.
The estimator consequences expose the permitted deterministic physical
estimator/comparator record and its stated all-table or dyadic-square
accuracy guarantee. These are the intended external premises. No existence
of the source records or Cook--Levin theorem is newly asserted here.

## Principal declaration map

| Source task | Reviewed providers |
| --- | --- |
| Actual deterministic source and new schedule | `V42ActualSource.run`, `threshold`, `run_yes`, `run_no` |
| New threshold and midpoint formatting | `V42DeterministicRequest.generated_threshold`, `rectangle_result`, `request_result`, `outputs` |
| Same literal instance and exact fixed gap | `V42FixedEndpoints.table_eq`, `threshold_eq`, `fixed_gap` |
| Complete physical source/output and fixed-round polynomiality | `V42SourcePhysical.request_outputs`, `rectangle_outputs`, `requestSource_polytime`, `rectangleSource_polytime` |
| Literal CNF reduction and NP-hardness | `V42FixedEndpoints.fixed_gap_reduction`, `fixed_gap_npHard` |
| Fixed additive-estimation consequence | `V42FixedEndpoints.fixed_source_classification`, `fixed_all_input_classification`, `fixed_additive_square_inP`, `fixed_additive_np_subset_p` |

All names in the table have prefix `CurrentAdditive`. This is an independent
private review and replay receipt, not a shared production build or release.
