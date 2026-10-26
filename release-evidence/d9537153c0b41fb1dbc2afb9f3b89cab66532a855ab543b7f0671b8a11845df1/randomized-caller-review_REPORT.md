# Independent review of the original-formula randomized caller

The frozen eleven-module caller packet is accepted at its stated scope.
It proves an actual fixed-machine execution from the original formula word
and one finite fair-bit tape to the new request/classifier output. Its
length-only tape carrier, unused-suffix execution, original-variable source
clock, and exact independent event law are checked. No desired source run,
printed table, estimator output, or acceptance probability is a premise.

All eleven modules replayed successfully from private source copies; all
44 public theorem axiom queries use only `propext`, `Classical.choice`, and
`Quot.sound`. There are no compiler errors or warnings. An independent
dependency audit traversed 47,730 declarations and confirmed the new actual
printer/request path, physical source cut and exact tape law.

The final bound on the **whole** caller time and the numerical ETH
contradiction remain separate endpoint obligations. `sourceClock_sparse`
only bounds the source/cut/frame component named in its statement.

## Source, freeze, replay and receipt

- Manuscript context: `papers/randomized-additive-hardness/versions/v42/source/main.tex`,
  SHA256 `1C7F0FEDC92989087219C2773411A42F610503846C6CF1E2DEA5AC18961684F7`.
- All 33 source/object/log artifacts in the author's `MANIFEST.json` matched
  their stated hashes before snapshotting. The unmodified manifest and README
  are retained as `MANIFEST_ORIGINAL.json` and `README_ORIGINAL.md`.
- Each of the eleven `.lean` files was copied into this review's `snapshot/`.
  No author packet, production source or prior review was edited.
- `replay.ps1` ran the manifest's dependency order, followed by the independent
  `StatementReadback` and `DependencyAudit` modules. All thirteen commands
  exited 0. One private compiler ran at a time and wrote only review-local
  `.olean` files and logs.
- Compiler: Lean 4.30.0, commit `d024af099ca4bf2c86f649261ebf59565dc8c622`;
  command overrides `relaxedAutoImplicit=false,maxHeartbeats=12000000`,
  together with the options explicitly present in the frozen source files.
- `DEPENDENCIES.json` records 70 resolved source/object modules, expanding
  the new v42 dependency chain and pinning its direct generic imports, plus
  the toolchain, Lake manifest and manuscript. Those existing dependency
  objects were used, not freshly rebuilt here.
- `REPLAY_V42MidpointRequestClock.json`, `REPLAY_StatementReadback.json`,
  `AXIOM_AUDIT.json`, the private logs and `RECEIPT.json` record the checks.
- No shared build, production change, Git operation or subdelegation was used.

## Fixed machine and original-word routing

The machine is fixed by the approved external `DinurReduction`,
`BOTReduction (booleanOccurrence D)`, the selected physical classifier, the
clause-density bound and a fixed cutoff. These parameters precede every
original formula word and every tape.

The source front routes every raw word to a valid formula with at least the
cutoff number of variables. It uses density `density+2`; this supplies the
two-clause fixed NO fallback even when the promised original density is zero.
The inherited routing theorem proves identity on sufficiently large valid
sparse encoded formulas, and satisfiability preservation on the valid sparse
domain. Malformed/small-input routing is part of the actual source machine.

`source_exists` uses the proved `V39SourceFront.all_input_cut_framed`
construction, whose quantifiers are `exists fixed M,a,e,p; forall w,tape`.
The selected `frontMachine/frontA/frontE/frontP` therefore share one global
witness, rather than selecting a machine for each input or desired output.
The front physically routes, cuts the bounded tape prefix, compiles the
source graph and round count, and frames blank work cells around the three
computed inputs. `frontWord_eq` proves its output is the exact new caller
bank and classifier block.

The original raw tape is not transferred wholesale to the source/printer.
The first cut and the later classifier block are bounded before the source
framing and all later transfers. This is why the proved time can be
independent of an arbitrarily long unused suffix.

## Exact new physical table and midpoint

`V42RawMidpointRequest` composes `V42WRaw.program` with the generic physical
midpoint program. The retained threshold, retained round count and printed
table ports are pairwise distinct by injective stack embeddings. The proof
obtains from the actual raw printer's final bank:

```
B port       = unary B(clog2(n),K),
K port       = unary K,
printed port = encodeInstance(m,m,B,rowMajor(actual sampled matrix)).
```

The midpoint program physically constructs the numerator `2B+K`, projects
the matrix part of that same printed word, and serializes

```
natField(2B+K) ++ matrixWord(actual sampled matrix).
```

This is the comparison midpoint `(B+K/2)`; it is not a reuse of an old
schedule threshold. The new sample side, `B`, all source widths and the
actual literal edge activity occur in the raw matrix definition.

`V42RawRequestPacket.outputs` compiles this concrete run into the fixed
finite framed machine. `initial_only_inputs` identifies the entire input
bank with only graph bytes, unary `K` and the bounded construction tape.
No precomputed table, source law, precision, constructor program or midpoint
is preloaded as an additional input.

`printed_word_eq`, `request_eq` and `request_physical_projection` identify
the physical output with the exact new semantic family, retaining dimensions
and every row-major payload bit. They hold on **every** construction tape,
including every rounded/default-label outcome, and assume no communication
gap or successful-sampling event.

The permitted classifier is then run through `V40ClassifierTail.after`,
which preserves its separate block while the request is computed and
physically cuts that block to the request's exact selected tape length.
The final machine is composition of this new requester/classifier and the
actual original-word source front.

## Closed execution and tape carrier

For clarity, let:

```
b = actual ticket precision,
N = actual reserved number of tickets,
L = blockLength(density,cutoff,w),
j = classifier.cR+1,
P = 2^j * L,
R = carrier(classifier,cutoff,|w|).
```

The fixed minimum is the maximum of the actual-source numerical cutoff and
the proved two-block resource cutoff. For every routed word it derives

```
b*N <= L,
L + classifier.tapeLength(actual request bits) <= P,
P <= R.
```

These are proved from the fixed cutoff, source geometry, new literal bit
reservation and the classifier's polynomial bounds. They are not input
certificates supplied with a particular tape. The graph is nonempty/valid
and its numerical `FullTests` are also derived for every routed word.

`bankWord_eq` reconstructs `tape.take L` as the exact consecutive ticket
words followed by its unused residual. It matches the raw printer's
`ticketWord(bits) ++ suffix` input format pointwise.

`runs` has one tape-length premise `P<=tape.length`, then derives both
source-bit and classifier-bit fit and composes the actual machines.
`carrier_fit` proves that premise for the length-only carrier

```
AEth4.tapeCA(AEth4.phiLen(cutoff), 7+j, |w|).
```

Consequently `runs_carrier` takes an arbitrary
`tape : Fin R -> Bool` and proves the actual execution. Its remaining
inputs are the fixed source/classifier parameters, fixed cutoff inequality,
raw word and finite tape; no tape-fit, graph, source-law, run, output or
correctness premise remains.

`output_append` shows that appending any suffix to a tape already containing
the first `P` bits leaves both observed prefixes unchanged.
`extend` specializes to an initial carrier-length tape and proves the
actual machine still outputs the original value within the **same**
`time(...,w)` after an arbitrary appended suffix. This is an execution
statement, not only a distributional or semantic suffix assertion.

## Charged time and original variables

The final `time` contains the original-word source/cut/frame clock,
composition overhead for the complete front word, and the new requester /
classifier cap. `bankInputCap`, `frontWordCap` and `sizeCap` bound every
transferred bank, retained classifier block, raw-printer clock and table
entry count. `classified_clock_le` uses the same matrix and request named
by the execution theorem. Its polynomial cap is fixed before all graphs,
rounds and tapes.

`sourceClock_sparse` proves that for each positive real `epsilon`, there are
fixed integers `A,d,N0` such that every promised sparse valid formula with
`N>=N0` has this exact **source/cut/frame** clock at most

```
A * ceil(2^(epsilon*N)) * (|encode(formula)|+1)^d.
```

Here `N` is the number of variables in the original formula, not the source
graph size or padded variable count. The density slack is handled explicitly.
The sparse encoding/routing theorem makes the route the identity above the
cutoff. The constants of the already selected source machine are passed to
the generic physical cut-clock theorem; no fast-run premise is assumed.

This theorem does not itself bound the complete `time` by the final ETH
budget. The new raw printer clock, fixed polynomial caller cap and final
numeric cutoff still need the endpoint owner's composition proof.

## Exact event law and independence

For an `ActualEstimator E`, all possible sampled matrices have the same
dimensions and payload length. `request_length` therefore proves that their
serialized requests have identical lengths. Since selected tape length is
a function of request length, `classifier_length` proves one common exact
length `s`, independent of the construction bits and payload contents.
It is not merely a common upper bound.

The caller's output observes only:

```
first b*N bits                      -> construction ticket blocks,
s bits beginning at position L     -> classifier,
```

where `b*N<=L` and `L+s<=P<=R`. The gap between `b*N` and `L` and all later
bits are unused by this output. `bits_take` removes the unused part of the
first cut; `bits_word` proves that parsing the literal ticket concatenation
recovers the original blocks. `cut_classifier` identifies the later prefix
with the segment beginning at `L`.

`V40BlockTapeLaw.uniform_twoCut` proves an exact identity for **every event**
of those two disjoint segments of a uniform length-`R` tape. The first factor
is exactly `RoundedDraw.bitBlocksLaw b N` in the physical ticket order, and
the second is uniform on `s` classifier bits. This is an exact bijection /
finite-product calculation, not a moment bound, total-variation estimate,
assumed sampler law, or independence assumption.

`machine_probability` rewrites the actual caller output through those
identities and obtains exactly `sourceLaw` and `sourceAccepts` for the same
routed formula, source graph, round count, request and classifier. It has
no accuracy, gap, satisfiability, desired decision probability, or successful
construction event as a hypothesis. The theorem is an acceptance-event
identity for the already proved executing machine; the separate semantic
YES/NO endpoint must supply the correctness probability.

## Dependency and axiom audit

The independent audit starts from `runs_carrier`, `extend`,
`sourceClock_sparse` and `machine_probability`. It traversed **47,730
declarations**, checked their permitted axioms, and required these exact
references in the proof graph:

- `V42RawMidpointRequest.physical_request_raw`;
- `V42WRaw.physical_encoded_raw`;
- `V42RawRequestPacket.classified_outputs`;
- `V39SourceFront.all_input_cut_framed`;
- `V40BlockTapeLaw.uniform_twoCut`.

It rejected the older concrete `V40RawRequestPacket`,
`V40RawMidpointRequest`, `V40SourceClassifier`, and
`V39ActualRandomizedReduction` paths. The audit passed. Generic physical
composition, source framing, midpoint, tape-cut and law lemmas retain their
earlier verified scope; their old version names do not substitute an old
concrete output or threshold here.

## Remaining boundary

Accepted: the frozen caller's actual execution, fixed effective finite tape
carrier, unused-suffix execution, source/cut/frame clock in original variables,
same new physical table and midpoint request, actual selected classifier,
and exact independent physical-to-semantic acceptance-event identity.

Separate: finite communication hardness / rank / sampling success, numerical
ETH rate and eventual cutoffs for correctness, full-time subexponential
composition, original-input semantic decision transfer, final contradiction,
and production integration/release gates. The approved Dinur/BOT implementation
records and their author-owned fidelity qualification remain explicit inputs.
This review adds no new external theorem record or axiom.

## Frozen source hashes

The following are the reviewed `.lean` sources under
`private-provenance-refs/44a27f2a226ef0e1d87d5c9fec5f7a7ec37094ef5b4f7bf2417192d18166a55c/randomized-caller`; the unmodified original
manifest additionally pins the supplied objects and logs.

| Module | SHA256 |
| --- | --- |
| `V42MidpointRequestClock` | `46B35861CB168B5E3C5DE3A4300BDF374D99E658FBDDEFE63FF80A715980A624` |
| `V42RawMidpointRequest` | `EA444B3E01AB451B6042DEAEB86D7AE57A705F1920ABC58E65921BB92F5D839C` |
| `V42RawRequestPacketTypes` | `1BC758A52C3610CF8783CF484A15416ADE2C72769756B5AEEE670EF683BC7366` |
| `V42RawRequestPacket` | `289670456A021D46477EE25481D49D823F86C30CFBAFEA24F4F7E5A03D638840` |
| `V42RawClassifierClock` | `54780DFAC0725CF2C11EEA377F42BDE0543872BF5CAAEED8F59C296BF39AED7D` |
| `V42RawRequestSemantics` | `F4DFF8D95E317E6A0BEFEB4185E75DF4FDF30EBA9FCC1C6559D6DD31688809E8` |
| `V42SourceClassifierResources` | `69C7B4E15D7DC9BFCF9232A00EBC25F5EC586BA04AEFB1AE21959B6356146B2D` |
| `V42SourceClassifierMachine` | `C533D6B2F9372FB8F091156176B0918621081556BB4FFEA3B898B6A40ED009B6` |
| `V42SourceClassifierRun` | `371CDD8ACA3EDA462742EC9FFAC6FE4B26A9D1F217196CAE126635D2723E585C` |
| `V42RandomizedMachineLaw` | `B29D6F61CD54CA4255D4711575A5A6F52238DBEC6090C6FC1A97F498F9AB1BE3` |
| `V42CallerAudit` | `84B25B1BB4D7B2D0553610214056C0BC64F93C837903A2BD155505B377D78CE7` |
