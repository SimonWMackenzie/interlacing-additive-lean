# Independent review of every admissible deterministic public size

Accepted. The frozen packet proves the deterministic reduction for every
admissible requested public size, using one fixed physical program. It
constructs the seed and actual iterates at that size, prints the matching
public threshold, and bounds both full execution and complete encoded
output. The earlier least-size clock bound alone did not establish this
claim; this packet supplies the missing interface.

All four fresh private module replays, all 21 public theorem readbacks and
axiom queries, and the independent dependency audit passed. Only
`propext`, `Classical.choice`, and `Quot.sound` occur. There are zero
warnings, no forbidden declarations, no frozen-source changes, and no
dependency drift. No mathematical or statement blocker was found.

## Exact source boundary

The source is replacement v42
`papers/randomized-additive-hardness/versions/v42/source/main.tex`, SHA256
`EC8AF5767ECCC1184E7A1B5F88979AB0A7EE9BE60D91BE4E61EC80AA66861F78`.
The relevant anchors are `src:gap-colouring` (lines 1234--1249),
`det:reduction` (lines 2669--2726), and `lem:generated-schedule`
(lines 4940--4989). `SOURCE_COMPARE.json` also verifies that both latter
theorem/proof regions are byte-identical to the previously frozen
`1C7F0FED...` manuscript; their hashes are respectively
`6AD4B633B2948732C1A19546082E5D974ACCFAB8382C090019428C165E310838`
and `6A8E9E3756576EC2D43400A2BDBEB6F94AAB92BBE8D10B56141195CA85A58A2D`.

The theorem's opening mentions a graph and a round count; its later
quantifier over every admissible public N, its formula for the public
threshold, and its proof make N an implicit parameter of the actual
construction. The proof uses seed logarithm L=log N and iterates the
construction chosen at that N. This is the source-faithful interpretation
reviewed here.

Merely bounding the clock of the least-size output using a larger N is
insufficient. Padding that output preserves its communication cost and its
least-size threshold; it cannot produce the source's exact NO equality at
the generally different threshold B_N. A fixed finite output also cannot
have side at least every unbounded admissible N.

The original generic `V42GeneratedConstruction.graphRun` already accepts
any admitted dyadic exponent p. `V42ActualLower.public_side` proves that
its existing square duplication has side at least 2^(4p), even at zero
rounds. The missing interface was the uniform physical program carrying
the caller's p through parameter compilation, source construction, the
seed with logarithm 4p, the actual weighted iteration, and the final
threshold printer.

Every dyadic s in the source is s=2^p, so its N=s^4 is exactly 2^(4p).
The source graph theorem explicitly supplies nonempty loopless graphs
with no isolated vertices, maximum degree Delta, and
n/2 <= m <= Delta*n/2. These are the graph premises of the wrapper;
they do not supply a desired matrix cost, recurring profile, or execution.

## Checked statement boundaries

- The actual input carries p, rather than recomputing the least exponent.
- The seed, every generated width, and all actual rounds use that p.
- The emitted threshold is d0(4p)+K*(40p), retained in the full square
  instance encoding; square duplication preserves communication cost.
- The same fixed machine and amplification A precede p, K, and the graph.
  A clock coefficient may depend on fixed source degree Delta.
- The fixed graph-promise cutoff depends only on gamma and Delta. Both
  time and complete output length are bounded for every larger p with
  n <= 2^(4p).
- The NO result closes the seed and recurring-profile induction internally.
  Only the external source graph gap and degree promises remain premises.
- Fresh private compilation and all printed public theorem axioms pass.
  The executable dependency graph contains the new requested-size prefix
  and threshold formatter and excludes the least-size selection machine.

Production integration and repository-wide release gates belong to the
parent task and are outside this private review.

## Frozen interface readback

`V42UniversalPrefix` has no static p parameter in its program or program
metadata. Its input is the existing graph-front input containing the graph,
p and K. It composes graph counting, the generic recipe parameter printer,
the actual source generator, and the actual seed/round-envelope printer.
Its output is the physical iteration driver's input for the same
`V42RuntimeWords.word ... p ... 0` and round count K. The old least-size
selector is bypassed.

`V42UniversalFormatter` composes the new v42 rectangle printer with the
generic physical square printer. It outputs `encodeInstance`, retaining
the public threshold as part of the complete output. Its cost theorem
identifies the decoded square table's communication cost with the actual
stored matrix entry function, and its shape theorem retains
`thresholdNumber (4*p) K` while making both dimensions the same power of
two.

`V42UniversalRuntime` fixes the whole prefix/actual-round-driver/formatter
machine. Its amplification and exponent definitions have no p, K, graph,
or gap parameter. Its C depends only on the fixed source degree bound.
It bounds the graph encoding using n <= N and 2m <= Delta*n, and bounds
both execution and every output bit by N^(C*A^K). The lemma
`requested_selected` is only used to reuse the existing arithmetic width
proof at requested p; the executable program does not invoke the old
selector.

`V42UniversalReduction.actual_reduction` quantifies over every p above
`fixedPromiseCutoff gamma Delta` and every graph with n <= 2^(4p).
It returns the encoded valid square instance, the two physical bounds,
its exact threshold, its side lower bound, its YES upper bound and its
NO equality. `fixedPromiseCutoff_graph` turns the fixed promise cutoff
into the graph-specific common cutoff. The NO proof applies the already
reviewed `graphRun_no`, which closes both the initial seed profile and
the recurring-profile induction. The final equality is B_p+K by exact
natural-number arithmetic.

This is stronger than the source's K >= 1 range because it also admits
K=0. The graph promise remains external, as in the source theorem.

The prefix's two enormous scalar metadata constants use a private
`Classical.choose` of the trivial proposition that a natural equals
itself, avoiding kernel normalization of a concrete giant numeral.
`coefficient_value` and `degree_value` prove exact equality to the explicit
composition metadata expressions. These are number equalities, not
assumed resource estimates or executions. Effectiveness can use the
explicit expressions; it does not require evaluating the choice wrapper.
The executable machine itself is still the concrete composition.

## Hashes and independent replay

The exact frozen sources are:

| Module | SHA256 |
| --- | --- |
| `V42UniversalPrefix` | `EF0C63713DEF02CC83BA78779F982BC151DB41A8A9FC292ED4DC74995B553A30` |
| `V42UniversalFormatter` | `DCACA91138C50A539A4462D18F4B6BD2B79259F24992B812B8E5A4F0ABDA4816` |
| `V42UniversalRuntime` | `22482693692E052815DAE07AECB095D0627F1934F04905698F0723052F01EFFF` |
| `V42UniversalReduction` | `41FFCD33C05AE1C12D29B800629B07ACE22666D60B22AECD7AA6C23D38EE504E` |

`ORIGINAL_FREEZE.json` pins each original source and object against the
author's direct freeze messages and each independently replayed object.
All original source/object hashes match. The parent authorized completing
this independent receipt without waiting for additional author metadata
after the author hit capacity. The separate author aggregate audit is
not required for this result; our own readback covers all 21 public
theorems, including the scalar equalities and every final endpoint.

`replay.ps1` compiles the four snapshots sequentially, then the two
reviewer files `StatementReadback` and `DependencyAudit`. The Lean version
is 4.30.0. The command-line settings are
`relaxedAutoImplicit=false`, `maxHeartbeats=4000000`,
`maxRecDepth=65536`, and `synthInstance.maxSize=32768`; existing
source-local settings are preserved. This is a private replay under those
budgets, not a claim about the production default resource budget.

The dependency audit traverses 74,659 declarations. It requires the
requested-size prefix, actual parameter/source/seed outputs, actual
weighted round driver, new threshold printer, square cost preservation,
public side bound, seed-closed generated NO induction, fixed-promise
cutoff, new weighted incoming endpoint and same-source restoration.
It rejects the historical least-size selector machines and historical
incoming/alignment proof paths. The old `selected=p` arithmetic lemma is
permitted and does not put a selector in the executable program.

All 84 resolved imported module source/object pins remain unchanged
against the three staged baselines. `AXIOM_AUDIT.json` checks all 21 queries
against the three permitted axioms. `FORBIDDEN_SCAN.json` finds no
`sorry`, `admit`, or new `axiom` token in the four sources.

One initial reviewer invocation failed before reading any Lean source
because PowerShell split an unquoted dotted `-D` option. The script now
quotes each option, and all six actual compilations passed. The initial
failure log is preserved as `logs/INITIAL_INVOCATION_FAILURE.log`; no
author source was changed for this correction.

## Accepted scope and remaining boundaries

The exact every-admissible-N clause of `det:reduction`, interpreted with
its implicit public size parameter as its proof specifies, is accepted.
There is no remaining internal desired-output, execution, next-profile,
or input-dependent-cutoff premise in this interface. The graph-source
degree and gap promises remain external inputs, as specified by the
source theorem. Fixed source Delta makes C an absolute construction
constant, while the one power-of-two amplification A is already fixed
before Delta, p, the graph, and K.

This receipt does not change frozen source bytes, integrate production,
re-run repository-wide gates, or replace separate randomized/ETH endpoint
reviews. Those tasks are owned by the parent.
