# Randomized output law and concrete algorithm wrapper review

Reviewed on 2 November 2026. The frozen common Probability bridge and the
two randomized outer/concrete construction modules pass bounded independent
semantic review and private Lean 4.30.0 replay. The actual machine's output
event has the correct independent two-stream law, and the concrete
rational-gap wrapper discharges the physical tape-fit conditions. These
are component conclusions; the final Corollary 1.4 error/runtime endpoint
still has to be assembled and reviewed.

## Frozen files and replay

The root/worker confirmed the files frozen. Hashes were checked directly:

| File | SHA-256 |
| --- | --- |
| `parametric-revision2/V43Parametric/Probability.lean` | `25e664a5c9e9db0155b6bea41f183313be03784066aff4a8bc3839b3978a7e58` |
| `randomized-outer/V43RandomizedAlgorithm.lean` | `aa6d02ebbddc9dd278feaf1b84b6735faa188dc3063ff9f063f6c20c1a5de4b6` |
| `randomized-outer/V43RandomizedConcrete.lean` | `5930cb5e1513243a266b07e8a2b302dc5a3839dcc598ad269c87ac5013cb30fb` |

Probability was compiled against the previously replayed private revised
Source/Carrier/Caller set and existing production objects. The outer
Algorithm and Concrete modules were then compiled serially against their
worker's stable dependency objects in randomized, parametric,
power-schedule, resource-fit, unary-power, and general roots, followed by
production/package objects. All three exited successfully. Logs sit beside
the private copies. All seven printed theorem/definition axiom reports
contain only `propext`, `Classical.choice`, and `Quot.sound`.

This replay reuses dependency objects; it is not a clean dependency rebuild
or a production gate. The source-level inspection below includes the
actual request semantics, tape-fit formula, and uniform-clock interfaces,
but does not claim a new independent admission of every dependency.

## Common probability bridge

`output_probability` concerns every predicate of the actual
`randomOutput` value of the previously reviewed fixed source-to-classifier
machine. Its left side uses the fair law on exactly the physically printed
carrier length. Its right side is the product of the complete rounded
sampler bit-block law with the independent amplified classifier law.

The first physical block is truncated to the actual
`precision*reservation` sampler prefix. `bits_take` proves that the total
bit-block view ignores the unused remainder of the first block.
`bits_word` proves that decoding the literal serialized sampler bits
returns those exact bit blocks, so the law is not silently permuted or
changed by a host-language view. The second block is the exact classifier
prefix after the first block's fixed offset; `cut_classifier` proves that
the outer carrier cut changes none of those bits.

The classifier tape length is proved common to every sampled payload by
`V42RawRequestSemantics.classifier_length`, using the same literal request
with fixed square dimensions and fixed public midpoint. Thus the cut
length is independent of the random table contents. The actual
`uniform_twoCut` theorem then supplies the independent rounded-block and
classifier laws. There is no assumed desired output law or success
probability.

`acceptance_probability` specializes this identity to output `[true]` and
the exact `V42JointEstimatorLaw.accepts` event. The request uses the actual
`V42RawRequestPacket.matrix`, its actual row-major table word, and public
numerator `2*B+K`, precisely matching the Accuracy source family. It does
not substitute a table or independently choose a midpoint.

The retained sampler/classifier prefix-fit premises are legitimate machine
input-length facts. They are not correctness premises, and Concrete below
discharges them for the chosen resource producer.

## Actual all-input outer algorithm

`routedAlgorithm` packages an actual `FairBitAlgorithm.Algorithm` for every
raw word. Its carrier producer first runs the physical sparse router and
then the physical carrier printer on that routed formula. Its main machine
uses `routerTapeMachine` to route the input while preserving all random
bits, then runs the same reviewed `randomMachine` on those bits. Its
execution theorem is for every fair tape, with one uniform clock rather
than a favorable-tape or expected-time bound.

The public tests follow because every routed formula has at least the
chosen cutoff variables and density at most `cs+2`. The definition's
remaining `hfit` concerns only physical prefix lengths. No final error
bound or finished-runtime assertion is accepted as input.

`routedAlgorithm_totalTime_large` uses the actual router identity above
the cutoff. It exposes, exactly, the carrier printer, uniform caller,
two executions of the router, original input framing, random bit count,
and all transfer costs. The identity is

`carrierClock + uniformClock + 2*routeTime + 14*inputLength + 7*carrierLength + 16`.

The duplicated router cost is retained because the carrier and main
machine both route the input. The fair-bit model's totalTime includes
carrier generation and one charge per random bit. This identity does not
already prove the corollary's asymptotic bound; it correctly identifies the
actual quantity the subsequent runtime theorem must bound.

## Concrete rational schedule and tape fits

`rationalSchedule a b` has a physical finite producer computing the proved
`iterations a b` function and its paid schedule theorem. The fixed rational
parameters are part of the program, before the formula or tape. The
algorithm definition introduces no unimplemented rational-root oracle.

`resource` uses the actual variable-exponent unary resource printer. On a
canonical formula its word length is the proved power of input length and
the actual schedule gap. `concrete_resources` applies
`ResourceFit.actual_tapes_fit` for the actual sampler and every classifier
request, then uses the proved resource word length and
`resource_le_block`. It thereby discharges `hfit` for every routed raw
input. The resulting `algorithm` has no outstanding physical tape-fit
premise.

The resource exponent may depend on the fixed classifier's tape polynomial.
That affects the final runtime overhead, which is allowed to depend on
the estimator. It does not change the actual sampled table or the
source-only construction size used in an error-gap hypothesis. A generic
tradeoff endpoint must continue to keep these two constants distinct.

## Remaining final endpoint

The source and routing correctness architecture supplies the actual
construction gap and the SAT-preserving finite-prefix router. The final
endpoint must still attach that correctness to this concrete Algorithm,
discharge the full charged totalTime bound, choose a rational exponent
between `8c` and the arbitrary real target exponent, and quantify over all
`0<=c<1/8`, `8c<alpha<1`, and fixed sparse densities. It must have no final
probability or runtime conclusion as a hypothesis.

No blocking semantic defect was found in these three frozen components.
Root production compilation, transitive axiom audit, source correspondence,
and full endpoint admission remain separate gates. Earlier reviews were
retained unchanged; only the private review directory was written.
