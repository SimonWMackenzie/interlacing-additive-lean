# Independent review of complete resource and manuscript clocks

Accepted: both frozen modules passed independent private replay, exit zero,
with no diagnostics. The four printed main Clock theorems and six printed
main Total theorems each use exactly `propext`, `Classical.choice`, and
`Quot.sound`. This completes this reviewer's shared resource/clock assignment.

- `V43ResourceClock.lean`: SHA256
  `4E6EC1C150774E84C1C36A14BF56DE79BD89325750DE624D30C54375706D925B`.
- `V43ResourceTotal.lean`: SHA256
  `846DE204DA1838D38D3426C831033ADD65C6DAB5B02EF7B2E56D0379F1A3C9B3`.

The replay imports the reviewer's independently rebuilt shared Resource,
Algorithm, Timing and ResourceFit objects, the preserved private
Source/Carrier/Caller dependencies, frozen unary-power objects and existing
repository dependencies. It does not use the author's copied ResourceClock
object. The helper's adopted source was verified byte-for-byte before replay.
SourceBounds remains pinned at
`646AFB1B56B0D389C4F4AE9EA9EF1B87061F70F084DC1776D153488414894CEE`.
This is an incremental component replay, not a cold dependency build.

## What the clock theorems establish

Clock's eighteen helpers preserve literal physical costs. They bound output
length using actual machine runs and push bounds; pay same-input copying,
concatenation and all serial handoffs; and absorb the actual carrier,
cutting, retention, source generation and classifier clocks. The two generic
`cut_time_poly` and `retain_time_poly` helpers isolate machine-independent
arithmetic; they change no hypotheses or conclusion and do not replace a
physical run with an assumed bound. This isolation also avoids reducing very
large fixed machine constants during elaboration.

`random_clock_poly` bounds the very `randomClock` from the caller. It only
uses prefixes physically delivered by the split machine, so it does not
assume that an arbitrary longer raw tape is cheap to scan in full. Its
polynomial is in the resource size, not in a silently substituted successful
output. The source and classifier execution bounds were separately proved
for the same machine and requests.

Total's `resource_producer_clock_poly` pays both schedule computation and
the variable exponentiation that prints the resource. The proof uses the
actual `PowerMachine.resourceClock_le` cubic execution bound, not a unit-time
exponentiation operation. Carrier generation can run that printer repeatedly;
the literal concatenation clocks retain those repeated costs.

`concrete_tapes_fit` joins the already accepted tape budgets to the same
physical `resourceProducer` and its actual `blockLength`. The sampler fits
in the first block. Every estimator request, for every possible sampled bit
block, fits in the second block. No successful-sample condition is used.

`totalClock` is the exact sum of:

1. the physical unary carrier printer's clock;
2. the number of independent fair bits;
3. the explicit initial frame-writing allowance;
4. the tape-independent `uniformClock` for the actual deterministic caller.

This is the previously accepted fair-tape cost model, substantiated by the
independent `InitializationAudit`; it is not a claim that Lean constructs a
monolithic probabilistic transition system. Its terms match the shared
`FairBitAlgorithm.Algorithm.totalTime` when the endpoint uses this carrier and
uniform caller clock. Establishing that exact instantiation is the endpoint
consumer's join, not a premise of the resource theorem.

## Quantifiers and remaining hypotheses

`total_clock_resource_polynomial` proves one pair of polynomial constants
before quantifying the input formula and its mathematical source tests. Its
indexing structure contains only a valid formula, sparsity, and admissibility
tests. It contains no desired clock conclusion, successful run, SAT algorithm
or answer. The only supplied machine cost is `Schedule.paid`, the explicit
implementation requirement for computing the gap schedule. All construction,
resource and classifier costs are proved from physical implementations.

`total_clock_manuscript_polynomial` proves, above the explicit sparse encoding
cutoff, that this whole charge is at most a fixed polynomial in
`randomizedSize C0 N (gap N)`. It allows every `C0 >= 1`. The resource exponent
may depend on the fixed estimator; that dependence is absorbed into the final
polynomial degree and does not move the manuscript's construction constant
after the estimator. The `chosen_total_clock_*` wrappers discharge the exponent
side conditions for `resourceExponent D B C`.

The approved Dinur/BOT interfaces and source admissibility tests remain
explicit. This review does not supply the tests for a routed all-input
instance, prove its success probability, or establish its chosen analytic
gap schedule. The final endpoint must join the same machine, exact finite
tape law, correctness probability and this clock. No ETH premise, desired
algorithm, opaque certificate, new axiom or proof hole occurs here.

See `ResourceClock-replay.log`, `ResourceTotal-replay.log`, and
`CLOCK_TOTAL_RECEIPT.json`. The receipt admits exactly eighteen Clock and ten
Total declarations. Root integration and production checks remain separate;
this reviewer changed no production files and ran no shared build or Git
operation. Private compiler processes were serialized.
