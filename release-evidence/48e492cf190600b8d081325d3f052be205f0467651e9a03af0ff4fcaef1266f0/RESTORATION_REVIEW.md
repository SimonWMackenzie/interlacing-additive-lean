# Independent review: full-product restoration at the closed scale boundary

2026-10-26. Reviewer `v42_proof_review`. **Accept for integration.**

Reviewed source: v42 `source/main.tex`, SHA256
`e9eb48925f087a64141c4b756ae3293856a87b353acae33f3fdc802b33f0f535`,
`cl:bridge` at lines 2289--2305 and the finite positive-rational input-weight
convention at lines 1015--1028.

Frozen module: `RestorationSnapshot.lean`, copied from
`restoration/V42FullIidRestoration.lean`, SHA256
`db49b654c2b1ed3b3a9a60f20f88090bcff75d310022b9d574046eaa60e527a2`.
Independent sequential private replay exited 0; see `restoration-replay.log`.
All six printed declarations use exactly `propext`, `Classical.choice`, and
`Quot.sound`, without `sorryAx` or project axioms.

## Literal statement and boundary review

`CurrentAdditive.V42FullIidRestoration.rational_restoration` assumes the exact
source hypotheses: finite nonempty row and column carriers with positive
normalized rational laws, base exact cost at least 3, `b >= 1`, positive
`theta,delta`, `delta <= 1/64`, `80b <= 2^r delta`, **`2^r theta <= 1/20`**,
the near-full-column bound at the actual base cost, and precisely the two
threshold bounds at that cost minus one. It concludes exact cost `D F+r` and
the regenerated two-threshold profile at that exact cost, with threshold
`2^(-b)`.

The matrix is literally
`V39FullIidRestoration.restored F r`, namely the transpose of the full interlace
on original column tuples `Fin (2^r) -> Y` and original row/block pairs
`Fin (2^r) x X`. Its row law is the actual iid tuple law for the original
column weights; its column law is the uniform block index times the original
row weights. There is no replacement matrix, generated tuple support, third
profile threshold, promise-dependent constructor, or desired-cost certificate.

The new boundary argument is valid at equality. Because `X` is finite, the
set of masses of all subsets of `X` is finite. The proof selects a strictly
smaller positive threshold `t < theta` such that
`t <= mu(U) iff theta <= mu(U)` for every subset `U`. Thus the near-full-column
bound and both input profile bounds transfer to `t` with no added assumption.
Since `2^r > 0`, `2^r t < 2^r theta <= 1/20`; the inherited strict theorem
applies. Its output depends on `F,r,b,delta` and the original laws, not on the
analysis threshold, so the output is unchanged. This is not continuity of
communication complexity or an approximation of rational weights.

## Declaration decisions

All declarations in namespace `CurrentAdditive.V42FullIidRestoration`:

| Declaration | Decision |
| --- | --- |
| `finite_threshold_lowering` | Accept. Finite induction constructs a positive threshold below `theta`, above every finite value strictly below `theta`, preserving every comparison. The empty finite family is handled explicitly. |
| `finiteLaw_threshold_lowering` | Accept. Applies the preceding theorem to `Set X`, which is finite when `X` is finite. It permits arbitrary real finite-law weights; rationality is only needed by the inherited restoration result. |
| `rational_profile` | Accept. Proves the source's non-strict scale boundary from the strict inherited theorem using unchanged eligible row sets. The abstract cost parameter `C` is a lower-bound interface, not silently identified with `D F`. |
| `rational_restoration` | Accept. Sets `C = D F`, derives the lower bound from the top profile evaluated on the full rectangle, and combines it with the independent selector-protocol upper bound. |
| `upper` | Accept. Inherits the actual full-interlace/transposition upper bound, independent of all lower-bound premises. |
| `restored_cardinalities` | Accept. Exact full tuple and block-carrier cardinalities; no support reduction is being hidden. |

Dependency read-back included `V39FullIidRestoration.rational_profile`, its
strict scale premise and literal output, `profile_full_lower`, `upper`, and
the actual definition of `restored`. The inherited rational profile transfers
the uniform-copy theorem using law pushforwards and surjective forgetting maps;
the production theorem does not stipulate its conclusion as an input.

This is acceptance of the reviewed new boundary extension against the available
production dependency objects. Root-owned fresh production dependency builds,
integration, broader correspondence and paper gates remain necessary. No
production edit, shared build, Git operation or subdelegation was performed.
