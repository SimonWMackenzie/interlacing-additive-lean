# Independent review: common alignment and same-construction restoration

2026-10-26. Reviewer `v42_proof_review`. **Accept the seven frozen proof/transport
modules for integration at their explicit conditional scopes.** No mathematical
repair was found. Four nonblocking tactic/simplifier linter warnings remain,
listed below. The dependency audit also independently passed.

## Scope and frozen inputs

This review covers v42 `res:alignment`, its new `res:incoming` use at each
physical stopping node, transport to the original full-product construction,
and transport/restoration on the actual finite-index `SourceData` construction.
The source clauses and the proof of `res:alignment` were reopened by label.

The frozen sources were copied unchanged into `alignment-snapshots/` beneath
this review directory. Its `FROZEN_HASHES.json` records the independent hashes;
they match the worker's `alignment/SOURCE_HASHES.json`:

| File | SHA256 |
| --- | --- |
| `V42IncomingGuard.lean` | `cd0a588443cc4bf663991590dbdd867e49d09835a152a1c4930ae8910d66ce27` |
| `V42IncomingBob.lean` | `da121bd6d362efd9717c861792c628a9132c7685587f1f0262c15010ca96b095` |
| `V42IndexedAlignmentProtocol.lean` | `349dac84e76ffa24a84148bb1b46bd0b887ebb744e43ced12ef433b79e41c693` |
| `V42IndexedAlignment.lean` | `08bbed5e04a69fbbdfe66c0fb662027d0074db2ebfbbb18f96159fd48aab0c85` |
| `V42FullProductAlignment.lean` | `4b71d047fb51e96603f4fbdd7986f940959ab32728f32435ead584f1fbd636b6` |
| `V42ActualItemStreams.lean` | `1da283c499009159d905700fd4e44e4b8b5e7c705b9cd5ca577f819b1f5a0df4` |
| `V42ActualInternal.lean` | `b0aa2c8ceff0b6ed26afd450c005361e4c09ed8b23d358f036bbf3f957a6ec7c` |
| `V42AlignmentDependencyAudit.lean` | `56d1ff2b055420010a2f55ea83ef30d5502ded369d653775b824c70eba339280` |

Each source independently compiled in dependency order using one private
compiler at a time, with exit code 0. Each printed endpoint has only
`propext`, `Classical.choice`, and `Quot.sound`. The snapshot directory owns
all eight replay logs and private objects. No `sorry`, `admit`, new axiom,
`unsafe` declaration, or opaque desired-result structure occurs in these files.

## Exact lower-bound conclusions

For the supplied source matrix `N`, set `C = H+ell+b+1`, `w=2^r`, `s=2^b`,
and `q2=2^ell`. The generic and actual-construction alignment endpoints prove
all three conclusions on one literal internal matrix `W`:

1. `D W = C+r`.
2. The current two-threshold restriction profile at row threshold `theta` and
   height `C+r-1` (exactly two column thresholds, not an extra third threshold).
3. Every actual restriction of `W` retaining row weight at least `theta` and
   column weight at least `1-eta/(16w)` has cost at least `C+r`.

All laws in the conclusions are the supplied original complete-stream label
laws and block/column mixture laws. No lower bound is proved for a surrogate
matrix and then silently presented as a claim about the original one.

## The current `2s` incoming bound is used everywhere

`V42IncomingGuard.weighted_ratio_eq` exactly simplifies the 256th-moment
Markov ratio to `C128/W^128`, where `C128` is the source's displayed constant.
`destination_guard` derives the guard for every real density
`W >= 512 s kappa` from the scalar premise `C128/s^128 <= theta/4`. Its only
size assumptions are `s>0` and `kappa>=1`; it introduces no integer/dyadic
density restriction.

`V42IncomingBob.first_bob_diagonal_mass_lt` follows the actual denser Bob child
under the original complete-stream law before selecting metadata or base
labels. That child has mass at least `theta/2`; Bob's one charged bit produces
the strict local cost premise for the new weighted incoming theorem. Its
conclusion is the actual total receipt from any fixed original copy set:
`sum receipt_i < 2 s kappa`.

In `V42IndexedAlignmentProtocol.protocol_impossible`, the same finite run of
the original protocol defines its stopping nodes, node row sets, owner copies,
and origin map. The proof sets **`K=2s`**. It proves the incoming estimate for
every stopping node in both branches:

* At depth `r`, `k=r-depth=0` and `kappa=2^k=1`. The terminal protocol's actual
  remaining cost yields the strict restriction bound needed by
  `V42IncomingSharpBound.incoming_diagonal_mass_lt`, so the receipt is `<2s`.
* Before depth `r`, the actual node is a genuine Bob query; the proof invokes
  the new `V42IncomingBob.first_bob_diagonal_mass_lt` with `kappa=2^k`.

The same new numerical ratio guard is supplied in each branch. No old
`8s` bound, logarithmic grouping factor, or old incoming endpoint supplies
either branch.

## Exceptional-capacity and loss accounting

The exceptional set `E` is chosen from the whole retained event **before**
the protocol frontier is constructed. The same set and original event are
used by conditioning, the reference-support obstructions, the near-full source
argument, and every owner-to-owner foreign receipt. The set is not reselected
at individual stopping nodes.

The actual owner-frontier theorem is opened and consumed with
`E.card <= exceptionCount theta (eta/2) <= e0`. It derives, rather than assumes,
at least `3w/4` assigned owner nodes, an injective owner-to-original-copy map,
exceptional capacity at most `2e0`, total reference loss at most
`eta/(8 lambda)`, and strict missing-source weight greater than `eta` at every
owner. The near-full source hypothesis concerns the original `N`, so this is
not a callback assuming the desired missing-weight conclusion.

The new proof explicitly charges all unassigned-node receipts by
`K * exceptionalCapacity <= (2s)*(2e0) <= eta*w/16`.
This is the changed source budget, with the factor `2s` and the whole
exceptional capacity both present. The owner count uses
`4*(2e0) <= w`; equality suffices for the weak `3w/4` owner count used in
the later strict contradiction.

Foreign receipts use the loss of the **receiving** assigned copy, as in the
source. The generic conservation theorem is applied to actual destination
events of the same run. Its proof identifies node rows with the original
retained rows whose actual destination equals that node, derives initial
deleted mass from the retained product-law weight, and only then sums the
receipts. It does not assume a free-standing partition or conservation
certificate. The source scalar `4 mu w q2 x <= eta/32` and the derived total
reference loss give the stated total owner-to-owner receiving bound.

## Module and declaration decisions

| Module / declarations | Decision |
| --- | --- |
| `V42IncomingGuard`: `weighted_ratio_eq`, `destination_guard` | Accept. Exact algebra and monotone positive-density comparison with the current source constant. |
| `V42IncomingBob`: `first_bob_diagonal_mass_lt` | Accept. Actual Bob child, original event mass, and actual bit charge feed the new weighted endpoint. |
| `V42IndexedAlignmentProtocol`: `protocol_impossible` | Accept. Derives all local bounds, frontier counts/losses and conservation on one actual run; both branches use the new `2s` bound. |
| `V42IndexedAlignment`: `nearfull` | Accept. Chooses an actual optimal restriction protocol, extends it to the nonempty full carriers, and applies the protocol contradiction. Nonempty retained events are proved from positive retained weights. |
| `V42IndexedAlignment`: `selector_upper` | Accept. Uses the full interlace selector upper bound, then composes with the given complete-stream decoder; it requires only the source upper bound and is independent of the NO-side lower-bound hypotheses. |
| `V42IndexedAlignment`: `alignment` | Accept. Tests the near-full theorem on the full rectangle, combines its lower bound with the independent upper bound, and derives the one-bit-lower two-threshold profile from the actual source reference profile and independence. |
| `V42FullProductAlignment`: `alignment` | Accept. Applies the common theorem to literal full sources and transports costs, both profiles and near-full restrictions using proved decoder equalities, law pushforwards and surjections. Its conclusion contains the original `fullW` and original full tuple laws. |
| `V42ActualItemStreams`: `pi_symm_pushes`, `alphabetEquiv`, `metadataEquiv`, `metadata_weight`, `toItemStreams`, `law_eq`, `decode_rowNumber`, `internal_entry_eq` | Accept. Reindexes a finite alphabet by a weight-preserving equivalence. Complete labels, index laws and repetitions remain unchanged; product laws and each decoder/matrix entry are proved equal. |
| `V42ActualInternal`: `W`, `alignment` | Accept. The output `W` is defined directly using `src.B`, `SourceData.Streams.decode`, and the original supplied labels. The item adapter identifies that very function with the generic internal matrix. The physical source near-full and upper hypotheses are transported in the correct directions. |
| `V42ActualInternal`: `indexed_restoration` | Accept. The base exact cost and both needed lower-bound inputs are derived from the preceding alignment theorem, then applied to the actual supplied seventh `ExactList` at the actual supplied width `Q=2^rQ`. The result is literally `src.successor st out R activity`, with the same `out.law` and complete-stream law. No replacement source is chosen. |
| `V42ActualInternal`: `full_restoration` | Accept. Applies the previously reviewed closed-boundary full-product restoration theorem to the same `W`; it derives the needed exact-cost/base-profile/near-full inputs from alignment and preserves the full original tuple carriers and laws. |
| `V42AlignmentDependencyAudit` | Accept as an audit utility. It traverses actual theorem types and proof values from the six listed roots, rejects the historical incoming/alignment namespace prefixes, requires the new weighted incoming endpoint, and checks the axiom allowlist. Independent replay visited 51,508 declarations and passed. |

The actual dependency statements inspected include
`V39SharedReceiptJoin.choose_exception_before_nodes`,
`V39IndexedOwnerObstructions.local_obstructions`,
`V39IndexedTwoFamilyOwnerFrontier.owner_frontier`,
`V39IndexedTwoFamilyRunConservation.contradiction`,
`V39IndexedInternalProfile.profile`, the relevant full-product cost/law
transport interfaces, `V39TwoThresholdRestoration.restored_width`, and the
already-reviewed `V42FullIidRestoration.rational_restoration`.
The new incoming theorem's exact statement was also opened; its independent
internal mathematical review belongs to the separate incoming reviewer.

## Genuine inputs and remaining completion boundary

These are conditional finite theorems with meaningful inputs, not unconditional
closure of the full v42 construction. In particular, the following remain
explicit mathematical premises:

* Actual source `A`, template `T`, and reference `Nref` two-threshold profiles.
* Actual source `N` near-full retained-rectangle lower bound and source upper
  bound at `C=H+ell+b+1`.
* The listed positive scales, powers of two, numerical width/loss/exception
  margins, and current incoming moment guard.
* For indexed outer restoration, a supplied `ExactList` with genuine bounded
  coordinate-law independence and the explicit outer width/scale inequalities.
  For full outer restoration, the source's full-product width and scale
  conditions, including the closed `Q theta <= 1/20` boundary.

None of those premises is the desired internal `W` cost, its profile, its
near-full restriction conclusion, a local incoming or foreign receipt, a
frontier owner count, a destination partition, or a successor lower bound.
`SourceData` and `ExactList` contain finite lists, laws, decoders and exact
bounded-coordinate event laws; they contain no communication-complexity
conclusion. Proving these genuine inputs for the selected source, public
schedule and physical constructor remains separately owned work. This review
does not upgrade the conditional packet to end-to-end paper completion.

## Nonblocking cleanup and replay limits

Independent replay reported these linter-only issues:

* `V42ActualItemStreams.lean:69`: unused `Equiv.refl_apply` simp argument.
* `V42ActualItemStreams.lean:96`: unnecessary sequential-focus `<;>` syntax.
* `V42ActualInternal.lean:213`: two occurrences of unnecessary sequential-focus
  `<;>` syntax.

These do not affect theorem statements or accepted proof scopes. Any cleanup
changes the frozen hash and should be recorded/replayed by the integrator.

The private replay used new snapshot objects for the seven modules and audit,
with frozen reviewed/assigned incoming, weighted-moment and restoration private
dependency objects plus the production library. It did not freshly rebuild
every inherited production dependency. Root integration must rename the bare
new import paths as needed and run fresh production dependency/axiom/source
gates. No shared build, Git operation, production/manuscript edit, or
subdelegation was performed by this reviewer.
