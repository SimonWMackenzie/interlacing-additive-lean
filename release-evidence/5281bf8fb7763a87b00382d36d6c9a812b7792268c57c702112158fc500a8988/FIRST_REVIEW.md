# Independent first review of the v42 proof refresh

Date: 2026-10-26. Reviewer: `v42_proof_review`. Production was read-only.

## Decision

Accept both reviewed packets at the scopes stated below. No mathematical or
Lean-statement repair is required for these scopes. The weighted packet is a
finite-distribution dependency for orders at least six, including the required
256th moment. It is **not** completion of the manuscript's full arbitrary-space,
all-positive-order moment lemma. The alternating packet proves the new
`m >= 2t >= 2` lookup statement and the NO-case lower bound on the actual
constructed matrix. Its lower-bound endpoints do not by themselves certify the
upper-bound protocol, explicit array generation, printer, or complete paper.

## Fixed objects reviewed

The author-replacement source read was
`papers/randomized-additive-hardness/versions/v42/source/main.tex`, SHA256
`e9eb48925f087a64141c4b756ae3293856a87b353acae33f3fdc802b33f0f535`.
The exact source anchors are `lem:conditioning-moment` (lines 4327--4354),
`yao:small-bias-escape` (3345--3385), and the lower-bound portion of `yao:lift`
(3409--3467).

The frozen review inputs and their SHA256 hashes are:

| Packet | Snapshot in this directory | SHA256 |
| --- | --- | --- |
| `weighted-moment/V42WeightedMoment.lean` | `WeightedMomentSnapshot.lean` | `ebb907f1ea28971b1738ccff098207506f69729cf1f0b140a8eb90702dca5521` |
| `deterministic/AlternatingV42.lean` | `AlternatingSnapshot.lean` | `0a5654f81be3450df5056c94448558333954c8ae3e2265649ce09c81a4f4fbe6` |

Both snapshots independently compiled from the repository root with one private
compiler at a time and exit code 0. Outputs and logs are in this directory.
The printed public endpoints have exactly `propext`, `Classical.choice`, and
`Quot.sound`. The snapshots contain no `sorry`, `admit`, or new `axiom`.

## Weighted packet: declaration decisions

All declarations in this table are in namespace `V42WeightedMoment`.

| Declaration | Decision and exact scope |
| --- | --- |
| `jointLawAgreement_mul` | Accept. Joint event laws on every index set of size at most `R` are preserved by multiplying coordinate `i` by the fixed real number `a i`. The event is pulled back along this coordinate map; no moment bound is assumed. |
| `iid_weighted_centered_mgf` | Accept. Under a normalized finite law, arbitrary centered real coordinate functions bounded in absolute value by 1, and fixed coefficients in `[0,1]`, the genuine independent-carrier product law obeys `E exp(t sum_i a_i X_i) <= exp((sum_i a_i)t^2/2)` for every real `t`. No positivity of total coefficient weight is needed for this declaration. |
| private `factorial_even_le_pair_pow` | Accept as arithmetic: `(2r)! <= (r(r+1))^r` for positive natural `r`, pairing opposite factors. |
| `iid_weighted_even_moment_ge_three` | Accept. For natural `r >= 3` and positive total weight `W`, its conclusion is exactly `E |sum_i a_i X_i|^(2r) <= (r^2 W)^r` under the actual independent comparison law. Its allowance `0 < W < 1` is stronger than the source's `W >= 1`, not an unproved source restriction. |
| `bounded_wise_even_moment_ge_three` | Accept. Same exact moment inequality on the original finite law, with `2r`-wise joint event-law agreement as its only independence premise. |
| `bounded_wise_moment_256` | Accept. Exact specialization `E |sum_i a_i X_i|^256 <= (2^14 W)^128`, using 256-wise joint event-law agreement. |

Dependency read-back:

* `Paper2.FiniteLaw` stores nonnegative real weights summing to 1. The sample
  space cannot be empty, as also proved by `FiniteLaw.nonempty`.
* `FiniteLaw.iid m` has weight `prod_i nu.weight(ws i)` and its normalization is
  proved by finite product/sum interchange; it is not a certificate structure
  carrying moments or independence consequences.
* `V38GeneralMoment.JointLawAgreement nu X R` quantifies every finite subset
  `s` of the variable indices with `s.card <= R` and every joint event on those
  coordinates. It compares the original law with the actual independent
  product-carrier law. This is a genuine finite-law independence property.
* `bounded_wise_raw_moment_eq_iid` expands the power, observes that each product
  of `2r` factors uses at most `2r` distinct indices, and transfers its
  expectation from equality of event laws. It does not assume the moment
  equality as a field of an opaque structure.
* `bounded_centered_mgf` proves the one-coordinate exponential bound from
  boundedness, centering, a pointwise chord inequality, and finite summation.
  `iid_exp_sum_indexed` factors the true product expectation.
  `moment_le_of_two_sided_mgf` is an independently proved exponential-series
  inequality with explicit two-sided exponential premises.

The final moment proof derives those exponential premises, chooses positive
`t = sqrt(2r/W)`, and checks the factorial/exponential arithmetic. It has no
moment, tail, or desired-bound premise. Quantifiers fix the coefficients before
sampling. The strict total-weight premise intentionally excludes the empty sum;
the manuscript's separate empty-sum and `r=1,2` clauses are outside this packet.
Arbitrary measurable probability spaces are also outside this packet.

## Alternating packet: declaration decisions

All declarations in this table are in namespace
`CurrentAdditive.SmallBias.V42`.

| Declaration | Decision and exact scope |
| --- | --- |
| `patterns_prob_le_direct` | Accept. A finite union of prescribed patterns has original-law mass at most the number of patterns times the one-pattern upper bound. |
| `no_short_lookup_actual_cut_pattern` | Accept. For the stated complete Alice-first tree and common first-`t` full response strategy, the actual cut retains at least `k` distinct requested rows and enough original column mass to contradict the explicit numerical pattern bound. |
| `numeric_pattern_gap` | Accept. The exponents and strict inequality are sufficient, including `h=1`: with `m=t+i+h` and `m <= 2^h <= 2m`, the product of retained-mass inverse and the pattern catalogue upper bound is at most `1/2 < 1`. |
| `no_short_lookup_complete` | Accept. The cut uses `h=clog 2 m`, `i=m-t-h`, and `k=2*2^h`; the row threshold gives the required strict inequality before integer rounding. It assumes the explicit log guard. |
| `no_short_lookup_at_bound` | Accept. It removes completeness by constructing an odd-depth normalized tree that preserves evaluations and every first-`t` full response table. The depth guard follows from `t < m`. |
| `no_short_lookup` | Accept. It weakens any original-law error `epsilon <= 2^(-4m)` to the target error and applies the preceding exact statement. Negative `epsilon` is not a vacuity loophole: the empty-pattern instance of `HasPatternBound` itself forces `epsilon >= 0`. |
| `twice_le_pow` | Accept, including `n=1`: `2n <= 2^n`. |
| `log_guard` | Accept. For the new literal premise `2t <= m` and `2 <= 2t`, it proves `clog 2 m <= m-t` without an extra asymptotic assumption. The boundary `m=2,t=1` is included. |
| `no_short_lookup_v42` | Accept as the new source lookup obstruction for every natural `m,t` satisfying `m >= 2t >= 2`, every fixed finite requested position set with size at least `2^(m-t+1)`, and every original labeled finite array law satisfying the stated pattern inequality. It excludes all Alice-first alternating protocols of cost at most `2m-1` with the common full early response strategy and correct entries on those rows. |
| `no_implies_strategy_colouring` | Accept. Restricts the NO promise from `2^(2^t)` colors to the smaller exact response-strategy color set by an injective color map; a genuine edge position is used to recover a smaller color. |
| `lower_bound_matrix` | Accept as a conditional NO-case theorem for the actual `matrixV38 (placeEdges edges index) C W`, for `t >= 4`, positive selector-label count, an arbitrary selector list satisfying `selectorGood`, a genuine finite array law, and the exact source NO-coloring promise. It concludes `2b+4t+2+2t-8 <= Dalt alice M` (natural subtraction is harmless under `t >= 4`). |
| `lower_bound_complete_addresses` | Accept as the source's complete address-list specialization of the preceding theorem. Its array pattern premise remains explicit. No selector event remains as a hypothesis, because the full address enumeration is proved to satisfy it. |

Dependency read-back and same-matrix checks:

* `Dalt` is the minimum achievable depth of actual strictly alternating binary
  protocol trees computing the given function. `exists_optimal` supplies an
  actual tree, cost equality, and entrywise correctness; it does not supply the
  desired lower bound.
* `HasPatternBound` is a one-sided event-weight bound for every finite requested
  position set and every bit pattern. All events use the same original `mu`;
  retained column sets are never renormalized.
* `actual_cut_rectangle` returns subsets of the original rows and columns, an
  actual Bob-first suffix, multiplicative row/mass retention inequalities, and
  entrywise equality on the retained rectangle. The new proof uses this result
  directly, not a prior lookup or matrix lower-bound endpoint.
* `exists_normalized_preserving_strategy` constructs padding and last-output
  normalization and proves its strict depth guard. `suffix_catalogue_bounds`
  bounds the actual catalogue of columns for a complete canonical suffix.
* `exists_monochromatic_dominantClasses` selects the largest classes of actual
  early response tables and returns both their cardinality inequality and
  equality of their full response tables on the real edge.
* `retained_projection_product` and `exists_large_projection` derive a concrete
  large coordinate projection. Their hypotheses are selector-product counting
  bounds, not lookup failure or a matrix lower-bound certificate.
* `Restriction.Rows` consists of actual pairs of an edge position and a
  represented address. `Restriction.protocol` is the original tree with local
  row/column input maps composed; its cost, response tables, and evaluations
  are preserved. The map from these rows to genuine `Fin H x Fin K` positions
  is proved injective in the new packet, so distinct retained requests are not
  accidentally identified.
* `placeEdges` uses only the public edges and their injective public indices.
  `matrixV38` is the piecewise table of the source: on an actual selected edge
  it reads `W ell (C z g,i)`, while nonincidences and unused edges read zero.
  The zero sentinel is not sampled and is not included in the pattern premise.
* The final contradiction instantiates the new lookup theorem with
  `m=b+3t-3`; it proves `m >= 2t` from `t >= 4`, transfers the exact source bias
  in the correct direction, and derives the integer lower bound. No premise
  asks for a short-protocol contradiction or the target lower bound.

Non-vacuity checks: `FiniteLaw (Fin samples)` excludes `samples=0`;
`hlabels` excludes an empty selector list; positive row thresholds and edge
embeddings preserve genuine distinct rows; the explicit NO promise must produce
an actual edge. The matrix constructor itself has no YES/NO promise argument.

## Reproduction and limits

Private sequential replay commands (run from the repository root):

```powershell
lake env lean -o private-provenance-refs/ffef5aeb3f89d9793af79f859f1a288275b94e7634c994a6dd175d77f7403630/WeightedMomentSnapshot.olean private-provenance-refs/a06bf95a4fabfb5ee8d85f27d4e4d0bcf1a6804905063689fbc33b69a2cbab07/WeightedMomentSnapshot.lean
lake env lean -o private-provenance-refs/e7c6352f27e252c5d044faec8e47209607b72df082fb0e54a38019226d29d74c/AlternatingSnapshot.olean private-provenance-refs/3a926d82d2ee76e6edc417233a9dde2ddb9d3ab01165e6f5ed97e1f657ea5b99/AlternatingSnapshot.lean
```

The corresponding logs are `weighted-replay.log` and `alternating-replay.log`.
This review inspected actual source dependency statements and proof bodies at
the interfaces listed above and replayed the new modules against available
dependency objects. It did not rebuild every imported production dependency;
fresh production dependency builds, integration, broader source correspondence,
and paper-level gates remain root-owned. No shared build, Git operation,
manuscript edit, or production edit was performed.

Optional prose cleanup: a few copied comments still call the generic argument
the v37 lemma. Updating them to say that the proof is reused for v42 would
improve traceability; this is not a correctness blocker.
