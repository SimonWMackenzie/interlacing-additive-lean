# Source-size and eventual-domain review, 2 November 2026

The frozen `V43TimeTradeoff/SourceBounds.lean` passes bounded independent
semantic review and private Lean 4.30.0 replay. It proves actual table-size
lower and upper bounds for arbitrary round counts, with the stated
positive-round requirement only where needed. Its constants do not depend
on an estimator or a gap schedule. This is additional component coverage;
it does not establish the complete SAT runtime theorem.

The prior `REVIEW.md` is retained unchanged.

## Input and replay

The root supplied a frozen file with SHA-256
`646afb1b56b0d389c4f4ae9ea9ef1b87061f70f084dc1776d153488414894cee`.
Its hash was checked directly before copying it into this private directory.
It was compiled against the previously replayed private `Accuracy` and
`Numerics` modules and the existing production dependency objects. The
single private compiler exited successfully; the log is
`V43TimeTradeoff-SourceBounds.replay.log`. All five printed theorem axiom
reports contain only `propext`, `Classical.choice`, and `Quot.sound`.
This was not a shared build or a clean dependency rebuild.

The target remains the same selected v43 `thm:time-tradeoff`, source
SHA-256 `bfde23b90f50785939095a6d37b7b247965ee6c45beaca9011a8963dec3cc9d6`.

## Actual lower bounds and eventual accuracy

`sampled_entries_ge_vertices` proves
`n <= sampleEntries (clog 2 n) K` for every `K >= 1`. It bounds the actual
sample side below by `2^(clog 2 n)` and then bounds its square below by the
side. It does not replace entry count with an unrelated declared budget.
The positive-round condition is faithful to the target theorem's
`k(N) >= 1` and is not a polynomial bound on that schedule.

`randomized_source_entries_large` uses the actual source graph
`t10Graph Src Bsrc Phi`. Its hypothesis is exactly
`Bsrc.degreeBound*T0 <= Phi.val.variables`. The source geometry gives
`T0 <= graph.vertices`, and the preceding sample bound then gives
`T0 <= actual sampleEntries`. The source geometry's division step is
sound because `Bsrc.degreeBound_pos` is part of the approved source
interface; there is no reversal of the degree factor or missing rounding
condition.

`deterministic_source_entries_large` concerns the actual
`V42ActualSource.run Src Bsrc Phi K`. Its proof follows
`T0 <= graph.vertices <= 2^(4*selected) <= actual square side <= actual
square entry count`. The side bound is the proved lower bound for this
same constructor run. It applies even at `K=0`.

Thus, for every fixed estimator accuracy cutoff `T0`, the fixed original
variable cutoff `degreeBound*T0` suffices for both constructions, uniformly
over all schedules satisfying `K>=1` in the randomized case. A final
endpoint still has to combine this cutoff with its other eventual
hypotheses and handle the finitely many smaller inputs.

## Randomized upper bounds

`randomized_constructor_resources` bounds the actual sample entry count,
the output execution of the fixed raw printer `V42WRaw.finiteMachine`, and
the actual rounded sampler tape length by one displayed
`randomizedSize ((e+1)*randomizedGraphExponent) N K`.

Its assumptions are actual source geometry (`g.Valid`, nonzero vertices,
`g.vertices <= N^e`, `N>=1`) and the established public numerical tests.
The printer conclusion is an `OutputsWithin` theorem for the same packed
input and `outputWord`; its clock is enlarged from the all-round access
theorem. The tape conclusion concerns the literal
`RoundedCodeLoop.tapeWord`. The entry bound is the square sample size of
that same output recipe, whose payload identity is retained by the
underlying `sample_access_all` theorem.

The exponent
`randomizedGraphExponent = 2*packetExponentAll+544+80` is an absolute
construction constant and is positive. The graph-to-source lift uses
`C=(e+1)*randomizedGraphExponent`; it correctly raises both sides of
`g.vertices+2 <= (N+2)^(e+1)` to the same nonnegative exponent. It holds
for every natural `K`, including zero. There is no `K <= poly(N)` premise.

For the actual source, the inherited
`DeterministicETHSourceBridge.sparse_graph_vertices_polynomial` supplies
`e=Src.sizeExponent+3` above its fixed sparse-source cutoff. Therefore this
choice of `C` depends only on the fixed source and the absolute printer
constant. Density may affect the cutoff. No estimator, schedule, payload,
or tape is available when this constant is selected. The module does not
yet wrap that substitution and the public-test cutoff into one
source-specialized endpoint theorem, but the needed inherited bounds have
the required quantifier order.

## Deterministic upper bound and constants

`deterministic_source_size` bounds the actual square entry count of
`V42ActualSource.run Src Bsrc Phi K`. It first uses the existing actual
square-word length bound, then bounds the selected public dyadic size by
`N^(Src.sizeExponent+4)`. The equality of the resulting power with
`deterministicSourceConstant*amplification^K` is a direct multiplication of
exponents; the final base enlargement from `N` to `N+2` has the correct
direction.

Its `C` is explicitly
`(Src.sizeExponent+4)*sizeExponent Bsrc.degreeBound (k0 Src Bsrc)` and is
proved positive. Its `A` is
`V42ETHPhysical.amplification Src Bsrc`, the fixed source-selected
constructor amplification. That amplification depends on the prefix and
iteration machine, not on the estimator tail. The imported
`V42GraphRuntime.amplification_ge` gives `A >= 2^64`, hence `A >= 2`.

Both constants precede every formula, round count, estimator, and schedule.
They also precede the clause-density parameter in their definitions. Once
the approved source records are fixed, this supplies an effective absolute
`A` and a source-only `C`, as required for this component. This module does
not replace its selected-source constructor with the separate universal
caller-supplied-scale constructor, and its proof consistently uses the
actual selected-source tables throughout.

The retained hypotheses are sparsity, the inherited source graph polynomial
cutoff, `N>=16`, and `N>=2^(4*k0)`. They are all fixed eventual conditions,
independent of `K`, the estimator, or its tapes. There is no source promise
in an executable table constructor and no assumed SAT decision.

## Exact remaining boundary

This file discharges the earlier table-size and eventual-accuracy premises
at the component level. It also bounds the randomized raw printer and its
construction tape. It does **not** prove the deterministic whole printer
clock in the displayed `S`, the source/front/schedule clock absorption,
the final classifier tape bound, or the final all-four SAT machine
composition and finite-size patch. In particular,
`deterministic_source_size` is a table-size theorem, not a whole-algorithm
runtime theorem.

No blocking semantic defect was found at this scope. Root production
compilation, transitive axiom review, source-bound admission, and the final
consumer proofs remain separate gates. Only this private review directory
was written; there were no production, shared-build, Git, or manuscript
changes.
