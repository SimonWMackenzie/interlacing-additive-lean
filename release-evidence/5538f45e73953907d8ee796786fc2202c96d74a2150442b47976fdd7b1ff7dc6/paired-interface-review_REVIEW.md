# Independent review: generic two-template-input lower bound

**Verdict: pass for the full standalone v42 `res:paired` statement.** Both
frozen proof modules and the author's audit independently compiled from exact
copied sources. The author's object directory was excluded from the import
path. The independent full-statement, tag, width-one, axiom, and dependency
checks also passed. No actionable scope, law, counting, matrix, or cost defect
was found.

The target is the selected v42 `res:paired` statement and proof, at source
lines 4087--4125 at freeze time, together with the domain convention in
`def:profile` and the generic `det:exact` block bound. Exact source blocks
and selected reused foundation hashes are preserved under `pins/`.

## Full statement and source match

The exported result is
`CurrentAdditive.V42PairedInterface.paired_restriction_lower`.
Its four finite types `Gamma`, `J`, `So`, and `Sf` are independent universe
parameters. The theorem assumes:

* arbitrary `A : Gamma -> J -> Bool`, positive normalized rational base laws,
  and exactly the two-threshold deletion profile of `A`;
* natural `H >= 2`, dyadic `q = 2^ell`, positive `x`, and `2*q*x <= 1/8`;
* separate finite real laws `sigma_o` on `So` and `sigma_f` on `Sf`, and
  separate decoders into `J^q`, each exactly eight-wise with the common base
  column marginal;
* an arbitrary pair set `K` of original product mass at least `49/64`;
* ordinary and foreign column sets of normalized weights at least
  `1-epsilon` and `delta`, measured separately under uniform index times
  the base row law;
* `epsilon >= 0`, `0 < delta <= 1`, and the literal strict source inequality
  `2*q*x + epsilon < delta`.

The conclusion is `H+ell+1` bits for the actual matrix restriction to
`K` and the tagged retained columns. Since `log_2 q = ell`, this is exactly
`H_2+1`. There is no base-gadget shape, same-carrier, same-law, injective
decoder, desired lower-bound callback, matching upper bound, or third
profile rung among the premises.

The `[NeZero q]` instance is well-formedness for the uniform coordinate law;
it follows from `q=2^ell` and does not impose `q >= 2`. The independent
`width_one` theorem explicitly instantiates `ell=0`, `q=1`, with arbitrary
heterogeneous sources and arbitrary `K`, and obtains `H+1`. Zero ordinary
deletion is permitted: no `epsilon>0` or `2/q` slack appears.

## Laws, labels, and correlated retention

`V42HeterogeneousPairLaw.concat_dwise` splits each selected set of at most
eight tagged coordinates into its false-tag and true-tag slices. Each slice
has at most eight coordinates, so the corresponding source's exact joint
law applies. The two resulting singleton-event probabilities factor under
the original complete product law. Equality for arbitrary events is then
transported from those exact fibres. The proof does not assume that either
complete word is fully iid.

This concatenation statement uses distinct `So` and `Sf` types and laws.
It also covers the same inner coordinate selected on opposite tags. All
independence assertions concern the original product law. The later retained
set `K` is an arbitrary subset of `So x Sf`; it is not replaced by a product
of its marginal projections, and no conditional independence is asserted.
The generic exact-block theorem receives that same original pair source and
the actual retained pair set as separate arguments.

The column carrier is `(Bool x Fin q) x Gamma`. The false entry reads
`A gamma (decode_o z_o alpha)` and the true entry reads
`A gamma (decode_f z_f alpha)`. These are separate tagged columns even when
their inner `alpha,gamma` values agree. The independent audit proves that
the two tagged coordinates cannot be equal. Repeated decoded words are
allowed because original source labels remain the matrix rows.

Each column-copy law is normalized separately to one. The standalone theorem
does not import the application's unequal mixture weights for template and
item rows.

## Counting and protocol-cost direction

The proof counts heavy ordinary and foreign fibres as disjoint tagged
groups. The strict source slack implies strictly more than `q` heavy groups,
hence at least `q+1`, each with retained base-row weight at least `2*q*x`.
It uses the current generic tagged count, not the older three-pairs or
additional-`2/q` estimate.

After an injective tag reindexing, the generic exact-block theorem applies
with exponent `a=ell+1`, retained pair mass at least `49/64 > 9/25`, and
the current two-threshold profile. The selected row blocks map into the
actual retained tagged columns. `restrictionD_map_le` gives the required
direction from that selected interlace to the transposed retained matrix.
`restrictionD_transpose` then gives exact equality with the original
orientation. The final lower bound therefore preserves the exact protocol
cost, with no speaking-order assumption or extra transposition bit.

The source's stronger `2*q*x<=1/8` and `delta>0` premises are retained in
the exported statement. Their unused-variable warnings are harmless:
strict slack, `epsilon>=0`, and `delta<=1` already provide the scale needed
by this particular proof.

## Independent verification and boundary

The review replayed `V42HeterogeneousPairLaw`, `V42PairedInterface`, and
`V42PairedInterfaceAudit`, then compiled a separately written
`IndependentPairedAudit`. The latter checks the complete theorem type,
tag noncollapse, and `q=1`; audits all 12 exported packet/review declarations;
and traces the final proof's 19,821-declaration dependency cone. It requires
the heterogeneous concatenation, generic exact boost, current tagged count
and floor, restriction map, and exact transpose. It rejects the older
source-specialized `V39PairedObstruction` and `V39PairedConversation` proofs.
All audited axioms are contained in `propext`, `Classical.choice`, and
`Quot.sound`.

`RECEIPT.json` binds exact sources, objects, logs, source blocks, and the
review. Selected older generic foundations were inspected and pinned; this
is not a rebuild of their whole dependency cone. Production admission and
full repository gates remain root-owned. No author source, production source,
Git state, or shared build was changed by this reviewer.
