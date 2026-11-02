# Shared fair-tape model and resource machinery: independent review

Accepted for the explicit fair-tape model below. Frozen private replays of
`V43Parametric.Resource`, `V43Parametric.Algorithm`, and
`V43Parametric.Timing` all passed with exit code zero and no diagnostics.
The independent `InitializationAudit` also passed. This review does not yet
admit the resource-fit/total-clock modules or either final randomized endpoint.

## Frozen files

- Resource: `6C97F483AA56384E86E95441B7C0250DDDEE1654116AA3005112686BE275AF91`.
- Algorithm: `32DA3962CF8B2F0E850B9E0616574C3CA4D512F7E16EEF0AFA85932933DAE214`.
- Timing: `0371765FF762140952D1722CB496A0B3C83F0F86AB4F48FA1025724BFC6D2417`.

Sources and fresh objects are under this directory's `V43Parametric/`.
Inherited Source/Carrier/Caller sources and existing private objects were
copied before replay; those components have the composition worker's separate
review. The Resource replay uses the frozen unary-power dependency already
reviewed independently: ResourcePower source hash
`D593936E25BBD194DEFA8A7303E4959143577E0CB56B82629DE0B77A033D1FB1`,
PowerMachine source hash
`E569493D11BCC29D402095831EC66E6A13B9918FE1B65AEBC25962CA68EE42A4`.
Existing repository imports were reused; this was not a cold dependency build.

## The exact randomized computation model

As in inherited `Paper2.SelectedTape.Algorithm`, randomness means a uniformly
distributed vector of a fixed finite length for each input, and execution is
an actual deterministic finite Boolean-stack machine on the literal encoded
pair of input and sampled bits. The new model permits more than polynomially
many random bits by requiring a fixed physical machine to print their length
in unary. That printer halts on every raw input word. Its result must equal
exactly `replicate (tapeLength w) true`; an abstract uncomputed tape-length
function alone cannot populate the structure.

`Algorithm.runs` requires the same deterministic machine to halt, within one
input-dependent tape-independent clock, on every prescribed bit vector for
every input word. `Algorithm.output` cannot secretly supply a different
unexecuted answer: that result is proved to be the machine's actual output
for each sampled vector. The probability is the uniform product law on
exactly that finite vector, not an input-dependent advice distribution.

The cost convention adds the physical length-printer clock, one operation
per independent fair bit, the cost of writing the literal initial framed word,
and the deterministic caller clock. The source defines a conservative frame
writing allowance `4*(|w|+tapeLength w+1)`. The independent checked
`InitializationAudit.framed_word_charge` proves that this dominates every
symbol of the actual pair encoding, whose length is `2*|w|+1+tapeLength w`.
`initialization_and_execution_charge` proves that all four costs are covered
by `Algorithm.totalTime` for every input and prescribed tape.

This is an explicitly charged fair-tape computation model, matching the
inherited finite-tape convention. `runs_total` enlarges the deterministic
caller's bound on the already framed input. It does not construct or claim a
single probabilistic transition kernel performing coin generation and initial
framing. The root explicitly accepted this model and requested the checked
initialization-cost evidence. No such stronger transition-system claim is
needed for this review or made here.

## Resource and execution identities

`resourceInput` physically normalizes both raw input and schedule result to
unary lengths and prints the exact canonical two-field input expected by the
unary power machine. Thus arbitrary raw schedule result bits do not break the
power machine's input format. On a canonical formula, the schedule's checked
identity gives the intended gap. `resourceProducer S E` really executes
`resourceMachine E` and prints unary `(|encode Phi|+2)^(E*(gap N+1))`.
Its clock includes the schedule, argument construction, full handoff, and
variable-exponent computation. It does not assume that exponentiation is a
unit-time operation or hide the superpolynomial output behind a polynomial
producer record.

`carrierProducer` physically runs the resource printer and prints the exact
two-block tape length. The inherited split machine operates on that very
length and preserves the original input. No differently sized carrier is
substituted into the probability law or caller.

`Timing.randomClock_eq` proves that the caller clock is unchanged when tape
bits change, using the literal lengths of both delivered blocks and the exact
source-word length. `random_runs_uniform` then proves every tape in the
actual finite carrier runs under the same `uniformClock`. Its remaining
premises are source admissibility and bounds fitting the sampler and every
classifier request into their respective blocks. Those are real obligations
for the endpoint consumer; this theorem does not silently discharge them.

## Axioms and admission boundary

All printed Resource and Timing declarations use only `propext`,
`Classical.choice`, and `Quot.sound`. `Algorithm.carrier_runs` is axiom-free;
`Algorithm.runs_total` and both independent initializer lemmas use only
`propext` and `Quot.sound`. No new axiom, proof hole or desired-output
certificate occurs in the reviewed sources.

This accepts the three shared components and substantiates the total-time
cost convention. It does not assert an instantiated all-input SAT algorithm,
its success probability, admissibility, resource-fit discharge or eventual
manuscript rate. Those need their own endpoint joins. No production files,
shared builds, Git operations or publication were changed. Private compiler
processes were serialized.
