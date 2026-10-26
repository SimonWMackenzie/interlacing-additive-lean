# Independent review of compact full-schedule computation

26 October 2026. Reviewer: `v42_runtime_review`.

The frozen packet computes the exact full-product recipe in polynomial time
in the binary input length of the positive source size. It supplies one
concrete finite Boolean-stack machine, with fixed clock constants before all
inputs, and prints all five widths plus all five rational parameters. The
implementation handles `q1=s-2` separately and does not materialize the large
widths in unary. The source read-back finds no blocking mathematical or
interface defect in this bounded computation claim.

**Accepted for this computation claim.** All eight frozen sources and the
independent statement checks passed. The final audit checked all 313 owned
declarations and found only `propext`, `Classical.choice`, and `Quot.sound`
in their transitive axiom dependencies; it found no new axiom, opaque,
unsafe, or partial declaration.

Only `private-provenance-refs/b4bf3fadc0afc215dcd810b1b480ffff5fd80bd3450959ad5263489340a0c9b6/full-schedule-interface-review` was changed.
No production edit, shared build, Git command, manuscript edit, worker launch,
or external model call was performed. One reviewer-owned compiler ran at a
time.

## Frozen inputs and private replay

The producer manifest SHA256 is
`4545d51619f3793cf7f26808aff26cbfa315896189fce06a3b58e4b872c510fa`,
and its README SHA256 is
`77d00b8e5b91d4e75e56f8f035562ef48a32be4639e93386b9654df1d8fed821`.
The three exact reviewed sources are:

| Module | SHA256 |
| --- | --- |
| `V42WidthPrimitives` | `4b8ca2074eb4fadea23f08ad426470206cb2a64de1514ccd4475ccdc8d0f06dc` |
| `V42FullWidthExpressions` | `57db86a3028639e2af972a12193d7de2b086de0da0d50cddf0eca25c31ad23a1` |
| `V42FullScheduleInterface` | `a39eb742f1341dd5cabfbf9b198407de25fbed26d0621e2cf33262f0615aa77d` |

[FREEZE.json](FREEZE.json) pins these files and their complete five-module
private source dependency closure: `V42Schedule`, `V42PublicSchedule`,
`V42PublicCutoff`, `V42PublicSize`, and `V42RuntimeSchedule`.
[DEPENDENCY_MATCH.json](DEPENDENCY_MATCH.json) confirms that all five
dependency source hashes match the producer's pins. All eight sources were
copied into [replay/](replay/) and independently compiled there with exit
zero, without reusing the producer's private object files.

[REPLAY.json](REPLAY.json) records exit codes, times, source hashes and fresh
object hashes. The compiler is Lean 4.30.0, commit
`d024af099ca4bf2c86f649261ebf59565dc8c622`; see
[LEAN_VERSION.txt](LEAN_VERSION.txt). [LEAN_PATH.json](LEAN_PATH.json)
contains the private replay directory and existing production/package caches.

[DEPENDENCIES.json](DEPENDENCIES.json) pins every transitively imported
project-owned source: eight fresh private modules and 1,330 cached production
dependencies, including the latter's existing object hashes. All project
sources and objects were found. There are 105 explicit external-library
import boundaries, qualified by the pinned package manifest, toolchain,
lakefile and compiler hash. This worker did not rebuild the entire existing
production or external-library closure. Fresh root-owned production gates
remain necessary after integration.

The manuscript source is `versions/v42/source/main.tex`, SHA256
`ec8af5767eccc1184e7a1b5f88979ab0a7ee9be60d91be4e61ec80aa66861f78`.
The producer's [SOURCE_ANCHOR.tex](PRODUCER_SOURCE_ANCHOR.tex) preserves
`lem:full-schedule` and its proof, SHA256
`a2eafd1aba4caf455160757a4fd53f07584cb0fac51d368139bdf66f80523f68`.
The recipe values are those of `def:amplification-parameters`. This review
did not change a manuscript source lock.

## Exact input, output, and quantifiers

A positive size `n` is represented by `positiveInput n = (n-1).bits`, in
canonical little-endian binary. `positiveInput_length` proves its length is
exactly `L=Nat.clog 2 n`. The case `n=1` is included and has the empty input
word. This convention is explicit; no unary encoding of the magnitude `n`
or hidden size advice is supplied.

For `ell=clog 2 (L+1)` and `a=16+ell`, the ten output fields are:

| Field | Exact value | Encoding |
| --- | --- | --- |
| 0 | `s=2^a=pow2Ceil(2^16*(L+1))` | canonical natural `Nat.bits` |
| 1 | `q1=s-2` | canonical natural `Nat.bits` |
| 2 | `q2=2^(L+2*a)=s^2/rho` | canonical natural `Nat.bits` |
| 3 | `w=2^(8*a)=s^8` | canonical natural `Nat.bits` |
| 4 | `Q=2^(24*a)=s^24` | canonical natural `Nat.bits` |
| 5 | `rho=1/2^L` | canonical `CodeDCodec` rational bytes |
| 6 | `x=1/2^(8*L)=rho^8` | canonical rational bytes |
| 7 | `eta=1/2^(2*a)=s^-2` | canonical rational bytes |
| 8 | `theta=1/2^(9+24*a)=1/(512*Q)` | canonical rational bytes |
| 9 | `deltaU=1/2^(4+10*a)=eta/(16*w)` | canonical rational bytes |

`recipeWord L` is exactly the ten-field `BitMachineBankCodec.encode` of these
words. Natural widths use little-endian `Nat.bits`; rational fields use the
existing canonical rational codec, whose numerator and denominator digits
are in its documented most-significant-first order. The physical reversal
for that codec is included in the program and clock.

`exact_full_recipe` proves all ten mathematical identities, including the
least-dyadic choice of `s`. `current_runtime_widths` is exact agreement with
the current randomized runtime's `fullS`, `fullQ1`, `fullQ2`, `fullW`, and
`fullQ`. It does not merely bound those values above.

`full_schedule_binary_widths_polytime` concludes

```
producer.machine.OutputsWithin (positiveInput n)
  (recipeWord (Nat.clog 2 n))
  (producer.coefficient*(Nat.clog 2 n+1)^producer.degree).
```

Its only mathematical input is `n>=1`. The stronger generic producer output
proof works on any input word, computing the recipe at its length.
`fixed_machine_before_all_inputs` quantifies

```
exists M, exists C d, forall n>=1,
  M.OutputsWithin (positiveInput n) (recipeWord (clog 2 n))
    (C*((positiveInput n).length+1)^d).
```

Thus the machine and both polynomial constants are fixed before `n`. There
is no base matrix, round number, source cutoff, successful run, supplied
width list, assumed producer, or desired resource certificate in the closed
endpoint. The internal arithmetic pair has its unused second coordinate
fixed to zero by the program; it is not a round-count input.

## Why the cost is polynomial in the binary size

The actual bit-length counter consumes one input bit per loop step and
produces unary `L`. The finite scalar programs compute only `s`, `q1`, and
the exponents needed for the remaining outputs. Their largest intermediate
value is proved at most `1048576*(L+1)`, uniformly for all `L`, including zero.
In particular, `s<131072*(L+1)`, so its unary conversion and that of `q1`
cost polynomial time in `L`.

The other integer fields are produced by a literal two-stack power writer.
It writes `e` zero digits and a one from a unary exponent of length `e`,
and its proved clock is at most `2*(e+1)`. It therefore produces
`(2^e).bits` without enumerating `2^e` unary cells. All exponents here are
linear in `L+1`. This is the necessary compact computation for `q2`.

Canonical reciprocal fields are written directly from those actual binary
denominators: fixed positive sign/numerator fields, followed by the
physically reversed and framed denominator. The existing `raw_inverse`
identity proves this is the canonical rational representation, including
denominator one at `L=0`. No arbitrary rational normalization or gcd
algorithm is assumed at unit cost.

The ten fields are combined through the physical bank serializer. All
input-length counting, arithmetic setup, finite scalar execution, unary to
binary conversion, binary power writing, reversal, field framing, copying,
and serialization are covered by the actual producer's composition bounds.
Each component is a fixed finite Boolean-stack program. Mathematical
expression evaluation and the desired output word are specifications, not
extra machine instructions.

## Concrete producer and proof review

The producer has an `irreducible` annotation to prevent eager elaborator
expansion of nested metadata. It remains a definition with the concrete
body `V40SourceLocal.physicalBank fields`; it is not an opaque declaration
or an assumed proof record. The review audit explicitly prints this checked
definition value.

The private generic helpers `realizes_at_length` and `fixed_before_inputs`
accept a producer with its existing execution proof. Their final public
consumers instantiate the concrete producer above and its proved
`producer_result`. Inspecting only those generic helpers would not establish
the construction; the review traced the actual field producers and scalar
programs down to their physical outputs.

Independent [Statements.lean](replay/Statements.lean) checks binary-length
boundaries at powers of two and their successors, the exact `q1` output
field, decoding of all five canonical rational fields, the closed clock
statement in the supplied producer-projection form, and the position of `q1` strictly
between consecutive powers of two. [Audit.lean](replay/Audit.lean) checks
the entire fresh declaration set, including generated and private
declarations, and the transitive axiom cones.

An initial reviewer-authored statement file failed because of a rational
decoder proof application and eager expansion of the exported concrete
metadata aliases. The supplied projection-form clock theorem compiled
throughout. Correcting the local proof application and using that provided
form made the independent check pass. The initial reviewer source and log
are preserved as `Statements.first-failed.lean` and
`Statements.first-failed.log`; no frozen producer source was changed.

## Source wording qualification and scope

The last sentence of the preserved full-schedule proof says that every
width is a power of two. The actual recipe intentionally has `q1=s-2`.
For `a=fullExponent L>=16`,

```
2^(a-1) < q1 < 2^a.
```

The independent statement check proves these inequalities for every `L`.
The literal power-of-two sentence therefore needs the `q1` qualification.
The requested polynomial bit-complexity conclusion is correct and is
proved directly by this packet without that false premise. This review
reports the wording issue and makes no manuscript edit.

The accepted computation claim is separate from choosing a cutoff that
makes the recipe admissible, the finite communication theorem, the raw
graph sampler/runtime, and the final source/NP/ETH consequences. The output
identities connect this compact producer to the same numerical recipe;
they do not silently change those separately owned implementations or
their status.
