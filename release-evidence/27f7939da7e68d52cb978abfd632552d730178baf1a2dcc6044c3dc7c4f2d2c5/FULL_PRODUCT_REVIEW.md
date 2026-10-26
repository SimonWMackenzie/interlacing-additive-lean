# Independent review: replacement-v42 full-product amplification and NO iteration

2026-10-26. Reviewer `v42_proof_review`. **Accept for integration at the finite
full-product amplification/iteration scope.**

The nine frozen modules independently compiled in their stated order, exit 0,
with only the standard three axioms for the printed principal endpoints.
Mathematical statement review found no repair needed. The independently authored
proof-value audit also passed, as recorded below.

## Frozen source and implementation identity

The nine reviewed module copies, private objects, compiler logs and worker
manifest are in `randomized-snapshots/` under this review directory.
`FROZEN_HASHES.json` was generated independently; each source hash matches its
entry in `WORKER_MANIFEST.json`:

| Module | SHA256 |
| --- | --- |
| `V42FullSuccessor` | `25797ff383ea474ba0fdd0af9dd6ecb28067fb91f15c0743237f25f88082f823` |
| `V42FullIteration` | `4e70f876afbad96d9da5405ec067d4f4afabcfc41634996b5bdb5b1feb97105e` |
| `V42FullProfiles` | `f7b6cc4aaff66cfc06e2a71a32575a01b4539d96c2901209e9f3fecf03cf05b4` |
| `V42FullNearFull` | `f3f742b978523b244a05053921928d6bcb5c1d1fb1a9ca6a22d2819806727844` |
| `V42FullAlignment` | `67481118f0382a107a0a959585f788919634d4e2d0db695cf94080e2f76bab0d` |
| `V42FullAmplifier` | `7d29c0f4b3c105f597ef14087c2ee7efb700a494dd37972f47c9413f8b0076ca` |
| `V42FullCutoff` | `ad96d092e201c9c8b8fc06fb7cf4cddfd082e29fe11ae44e2856e14520a6dd14` |
| `V42FullNoIteration` | `cb7a85cdca73eb0ce4dc9627c6927d5c92271d814e0407c4d9aa02145e356232` |
| `V42FullPublicAmplifier` | `9fccdad13de1595e5692fe8896dc47f0a2b004e514dbed0e1280568be794a49e` |

The source contracts were reopened at `thm:amplifier`, `prop:iteration`, and
`lem:full-schedule` in the current v42 manuscript, SHA256
`1c7f0fedc92989087219c2773411a42f610503846c6cf1e2dea5ac18961684f7`.
The worker manifest records the earlier author-replacement SHA256
`e9eb48925f087a64141c4b756ae3293856a87b353acae33f3fdc802b33f0f535`;
these are distinct observations, not a single frozen release receipt.

## The current construction and numerical recipe

Write `L=clog 2 |V|`, `k=16+clog 2 (L+1)`, and `s=2^k`.
The reviewed construction uses exactly

```text
rho = 2^(-L), x = rho^8,
q1 = s-2, q2 = 2^L s^2,
w = s^8, Q = s^24,
h = L+36k = L+36 log2(s).
```

`V42FullSuccessor.internal` is the transpose of the width-`w` full interlace
of the literal current graph-source matrix `V38Matrix.matrix order edge ...`.
`V42FullSuccessor.successor` is the transpose of the width-`Q` full interlace
of that same internal function. Both definitions retain the original full
tuple carriers. The law definitions are the actual complete tuple laws and
uniform-index product laws for these carriers. No YES/NO property occurs in
the constructors or law definitions.

The source cost is `d+L+4k+1`; the two interlaces add `8k+24k`, yielding the
exact NO cost `d+L+36k+1 = d+h+1`. The YES source protocol saves its one source
bit, yielding the upper bound `d+h`. The rank multiplier is bounded by
`Q*w*s^2*q2 = 2^L s^36 = 2^h`, using the actual source matrix's rank estimate.
Thus the cost and rank accounting use the new widths throughout.

## Reuse of inherited source results is valid and limited

The base threshold `rho`, the source widths `s,q1,q2`, and the source matrices
`A,T,Nref` are unchanged. The inherited source-profile theorem proves their
profiles at `x_old=2^(-10L)`. The new source threshold is
`x_new=2^(-8L)`, and `x_old <= x_new`.

`V42FullProfiles.profile_row_mono` uses this comparison in the correct
direction: a set retaining mass at least `x_new` also retains mass at least
`x_old`. It neither reverses the mass inequality nor upgrades a profile to
smaller retained sets. `q₂_old` identifies the unchanged width, while the
other width/base-law identifications are definitional. The inherited source
theorem's actual statement and proof interface were opened; its inputs are
the base exact cost/profile, actual source widths/laws, graph counts, and its
proved fixed cutoff. It is not a final full-product amplifier or iteration
endpoint.

`V42FullNearFull.nearfull` does **not** reuse an old near-full conclusion at an
incompatible tolerance. It derives the new collision/deletion margins from
`V42SourceNearFullGuards.source_guards_common`, proves the needed three-tail
input from the actual base profile, and applies the generic
`V38FullNearFull.restriction_lower` to the actual retained source rectangle.
That generic theorem takes the graph coloring gap, actual A/T profiles,
explicit scalar margins and the three-tail bound; its proof constructs the
actual protocol prefix and surviving collision. It has no desired near-full
hardness, collision-count certificate, or final amplifier hypothesis.

## Declaration decisions

| Module / declarations | Decision and scope |
| --- | --- |
| `V42FullSuccessor`: width definitions, `fullS_ge_256`, `fullQ₂_mul`, `fullQ_pow`, nonzero instances | Accept. Literal new widths and exact power identities. |
| `V42FullSuccessor`: `internal`, `successor`, `rowLaw`, `columnLaw` | Accept as the promise-independent original full-product objects. |
| `V42FullSuccessor.upper` | Accept. Actual two interlaces plus current source protocol give the universal `D R+h+1` upper bound and the proper-three-coloring `D R+h` upper bound, with no NO premise. |
| `V42FullSuccessor.rank_le` | Accept. For `|V|<=2^L`, bounds the real 0/1 matrix rank of that same successor by `2^h rank R`; it uses the actual current source rank estimate and two explicit interlace rank bounds. |
| `V42FullIteration`: `State`, `seed`, `seed_cost_profile` | Accept. `State` reuses only finite carriers, rational laws and entries; it contains no cost/profile/runtime certificates. The unchanged lookup seed and its actual cost/profile are the permitted inherited base case. |
| `V42FullIteration.next`, `iterate` | Accept. Every step calls the new literal `V42FullSuccessor.successor`, uses its new complete laws, and fixes all public parameters independently of the number of rounds and graph promise. |
| `V42FullIteration.upper_iteration`, `rankBound_zero`, `rank_iteration` | Accept. Induction gives the general `H_i` upper bound, proper-coloring `B_i` upper bound, and rank `<=2^(B_i-1)` for the same `iterate` state. The base rank is the lookup matrix's actual rank. |
| `V42FullProfiles`: `q₂_old`, `x_old_le`, `profile_row_mono`, `profiles` | Accept. Exact unchanged source interfaces plus justified weakening to the larger current row threshold. |
| `V42FullNearFull`: `sourceCost`, `nearfull` | Accept. Proves source near-full cost under the current eta/x recipe from the graph gap, current scalar guards and actual inherited source profiles. |
| `V42FullAlignment`: `internalHeight`, `tupleLaw`, `copyLaw`, `alignment` | Accept. Instantiates the reviewed new common alignment theorem with the newly proved source profiles/near-full bound, the independent actual source upper bound, and proved current schedule guards. It returns exact internal cost, one-bit-lower profile and exact-cost near-full lower bound on the same `internal`. |
| `V42FullAmplifier`: private `restore_width`, `amplifier` | Accept. Applies the reviewed closed-boundary full-product restoration theorem to that same internal function, using `delta=eta/(16w)`, `Q theta=1/512`, `Q delta>=80L`, and outer threshold `2^(-L)=rho`. The resulting exact cost and renewed profile are on the new literal successor and its original full-product laws. |
| `V42FullCutoff`: `sourceCutoff`, `bounds` | Accept. A computable natural cutoff depends only on fixed rational gamma and natural Delta. For every graph size at least that cutoff, it proves the inherited source cutoff, current common-cutoff inequality, `4k<=L`, `L>=16`, `d0<=L`, and `h<=7L`. No stage-dependent eventual-test premise remains. |
| `V42FullAmplifier.amplifier_public` | Accept. Uses `bounds` to eliminate both extra `hk` and `hb` assumptions from the amplifier theorem. |
| `V42FullIteration.no_iteration_at_margins`, `no_iteration` | Accept. The new amplifier proves exact cost `H_i=B_i+i` and its renewed two-threshold profile by induction, starting from the actual lookup seed. The public version discharges `hk/hb` through the fixed source cutoff and has no assumed one-step or final NO conclusion. |

## Quantifiers, cutoff, and non-vacuity

The public one-step NO theorem quantifies every base Boolean matrix with
positive normalized rational input laws, actual exact cost `d>=3`, and its
two-threshold profile at `rho`. Its remaining graph inputs are ordinary
source data and promises: the vertex/edge finite carriers, looplessness,
bounded degree, positive fixed gap, the monochromatic-edge gap for every
three-coloring, standard count bounds, and the public source-size cutoff.
The numbering equivalence, edge-replication count and exact public width
identity describe the supplied graph-source constructor. They are not a
hardness or communication-cost certificate.

The fixed cutoff is

```text
max(old_source_cutoff(gamma,Delta),
    2^(fullLengthCutoff(fixedPromiseCutoff(gamma,Delta)))).
```

It is intentionally a sufficient, possibly very large, explicit natural
bound. It depends on neither the base matrix, actual round count, nor an
uncomputed edge/vertex ratio. The proof uses `n<=2m` to bound the source
vertex-deletion tolerance below by `gamma/(4Delta)`, then the proved cutoff
monotonicity and integer `clog` bounds to obtain `hk/hb` for every larger
`n`. The actual theorem and proof of that fixed-promise comparison were read.

The round count and width exponent are separate natural parameters. Every
stage's input laws guarantee nonempty finite carriers; `State` does not
silently carry an empty matrix with a desired default complexity. The public
cutoff in particular forces `L>=16`. The NO recurrence is valid for all
natural round counts including zero, and the actual seed has cost at least
7, so its `d>=3` premise is genuinely discharged in every iteration.

## Same actual matrix link

The separately owned and separately reviewed
`constructor/V42FullActualLabels.lean` was opened only for the object-identity
check requested here. Its `next_eq_generic`, `iterate_eq_generic`, and
`iterate_eq_actualState` identify this very new graph-ordered `State` with
the complete recursive-label construction, including carriers, laws and
entries. The displayed `next_eq_generic` expands `V42FullSuccessor.successor`
and `internal`; it does not refer to an old full successor. At this read its
SHA256 was `a6bac0a63e0059f34ba9a050fc80e55e3a6ae87e042d20c5a6c006c30663ffdb`.
Its independent replay and the physical constructor/evaluator audit remain
with the constructor reviewer; this report does not duplicate that claim.

## Independent proof-dependency audit

`randomized-snapshots/FullProductReviewAudit.lean` was authored independently
for this review, SHA256
`3f1128cd4accc014c478f69d8f8782f98fa582cbfbc2701edc23dfcaeaff44f9`.
It traverses actual declaration types and available proof values, rather than
rejecting an unused import. The imported historical libraries can remain
available for unchanged source or seed components without validating a new
endpoint by name alone.

The audit checks the axiom allowlist for thirteen new roots; rejects
historical full successor/amplifier and old full iteration `next/iterate` or
NO/upper/rank endpoints, as well as old incoming/alignment proof namespaces;
and separately requires the final `no_iteration` proof cone to contain every
new source-profile, near-full, alignment, amplifier, weighted incoming,
256th-moment and closed-boundary restoration endpoint.

Audit result: exit 0. The thirteen-root audit traversed 59,091 declarations;
the separate final `no_iteration` audit traversed 53,058 declarations and
found all required new dependencies. See
`randomized-snapshots/FullProductReviewAudit.log`. The only transitive axioms
at the checked roots are `propext`, `Classical.choice`, and `Quot.sound`.

## Replay and completion limits

The nine private replays use frozen snapshot objects and the previously
reviewed new alignment snapshot chain, together with the frozen private
parameter/source-guard/weighted-incoming/restoration dependency objects and
production library. The worker manifest records the complete proposed new
private dependency cone. This review did not rebuild every inherited
production dependency.

Compiler warnings were only unused automatically included section variables
in the two successor bounds and the alignment theorem. They are not changed
theorem scopes or proof failures; optional cleanup should be recorded and
replayed if it changes the frozen hashes.

This packet proves the finite full-product amplification/iteration
mathematics. It does not by itself prove bit-operation runtime, printing,
sampling, approximation-algorithm composition, SAT-to-graph construction, or
the randomized ETH consequence. Fresh production compilation, source locking,
constructor/machine linkage, axiom audit and final paper-level gates remain
root-owned. No production/manuscript edit, shared build, Git operation or
subdelegation was performed by this reviewer.
