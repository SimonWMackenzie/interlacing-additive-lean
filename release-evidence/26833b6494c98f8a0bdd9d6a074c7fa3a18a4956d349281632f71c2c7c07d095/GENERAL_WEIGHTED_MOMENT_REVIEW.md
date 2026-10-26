# Independent review: general weighted moment lemma

2026-10-26. Reviewer `v42_proof_review`. **Accept for integration.**

Frozen implementation reviewed and independently replayed:
`general-weighted-moment/V42GeneralWeightedMoment.lean`, copied here as
`GeneralWeightedMomentSnapshot.lean`, SHA256
`b3d1d9cc88a69597316a78ebdc1a26bd06d9fd61f604a7416f85c32e74ea0686`.
The replay exited 0 without warnings; `general-weighted-replay.log` records
the printed axiom sets of the weighted count and all three moment endpoints.
Each uses exactly `propext`, `Classical.choice`, and `Quot.sound`.

## Exact scope

`V42GeneralWeightedMoment.bounded_wise_even_moment` proves the literal weighted
inequality of v42 `lem:conditioning-moment`:

`integral |sum_i a_i X_i|^(2r) <= (r^2 sum_i a_i)^r`.

The theorem quantifies an arbitrary type with a measurable-space structure and
an actual probability measure; it does **not** require a finite sample space.
It holds for every natural `r >= 1`, including `r=1` and `r=2`. Coefficients
are fixed real values in `[0,1]`, with total weight `W >= 1`. Every coordinate
is almost-everywhere measurable, has integral zero, and is bounded in absolute
value by 1 almost everywhere. Independence is ordinary Mathlib `iIndepFun`
for every subfamily of at most `2r` distinct coordinates, not an opaque moment
or cancellation certificate. There is no moment, tail bound, independent proxy,
finite-law transfer, or desired-conclusion premise.

The exact weighted 256th and 1024th moments are separately proved with constants
`(2^14 W)^128` and `(2^18 W)^512`. Their independence hypotheses require only
256 and 1024 coordinates respectively, as they should. The imported
`V39GeneralProbabilityMoment.bounded_wise_even_moment` already gives the unit
coefficient theorem including `m=0`; its zero-family branch has no positive
size assumption. Thus the manuscript's separate empty-sum clause is retained.

## Declaration read-back

All new declarations are in namespace `V42GeneralWeightedMoment`.

| Declaration | Review |
| --- | --- |
| `tupleWeight`, `PatternCode`, `codeWeight` | Accept. A tuple weight is the product of the fixed coefficients at its factor positions. A code stores a map of the `2r` factor positions into `r` names, and assigns original coordinates only to names actually used. These are explicit finite combinatorial objects. |
| `tupleWeight_nonneg`, `codeWeight_nonneg` | Accept. Direct products of the nonnegative fixed coefficients. |
| `tupleWeight_comp_le` | Accept. Fiberwise multiplication gives one coefficient raised to a positive occurrence count per used name; `0 <= a_i <= 1` bounds it by one coefficient per name. It does not impose artificial factors for unused names. |
| `sum_codeWeight` | Accept. For each name map with `k` used names, summing all coordinate assignments is exactly `W^k`; `k <= r` and `W >= 1` give `W^k <= W^r`. Exactly `r^(2r)` name maps occur. |
| `goodTuples_weight_le` | Accept. Tuples without a singleton coordinate have at most `r` distinct coordinates. The proof chooses an explicit factorization through `Fin r`, defines an encoding with an explicit decoding left inverse, and hence proves the chosen encoding injective. Nonnegative weights permit enlargement from its image to all codes. The final bound is exactly `(r^2 W)^r`. |
| `weighted_monomial` | Accept. Pointwise factorization of the coefficient product out of the variable monomial. |
| `weighted_coordinate_bound` | Accept. Derives the almost-everywhere unit bound on the scaled variables from the original bound and the coefficient interval. |
| `bounded_wise_even_moment` | Accept at arbitrary-probability-space and all-natural-`r>=1` scope. Expands the even power, integrates a finite sum of integrable monomials, cancels singleton terms by genuine independence and centering, bounds each remaining weighted contribution, and applies the newly proved weighted count. |
| `bounded_wise_moment_256`, `bounded_wise_moment_1024` | Accept. Literal arithmetic specializations with the correct constants and independence orders. |

The combinatorial `_hr` argument in `goodTuples_weight_le` is unused because
that helper is actually valid more generally; it does not weaken the public
moment theorem's `r >= 1` conclusion or hide a missing case.

## Dependency and vacuity audit

The relevant imported statements and proof bodies were opened, including
`SingletonCount.support_card_le_half`, `small_range_factor`, and the
general-probability module's monomial integrability, singleton cancellation,
moment expansion, and unit-coefficient theorem.

* `support_card_le_half` counts the factor positions by nonempty index fibers;
  absence of singleton fibers gives at least two factors per used coordinate.
* `small_range_factor` uses an embedding of the actual finite support into
  `Fin r` and extends the assignment only at unused names. The new `PatternCode`
  removes the unused-name coefficients from the weight count.
* `monomial_integrable` derives integrability from almost-everywhere
  measurability and the proved absolute bound under the probability measure.
  The new proof applies it to every scaled monomial before interchanging the
  integral with the finite expansion. No nonintegrable-default-zero behavior
  is used to derive the result.
* `monomial_integral_zero_of_singleton` restricts the actual independent
  subfamily to the monomial's support, whose size is at most `2r`; independence
  factors its powered-coordinate integral, and the singleton factor is exactly
  a coordinate's zero mean. The actual Mathlib
  `iIndepFun.integral_fun_prod_comp` declaration was also checked in
  `Mathlib/Probability/Independence/Integration.lean`: it is the standard
  product-integral theorem for measurable functions of independent coordinates.
* `monomial_integral_le_one` derives a pointwise/AE bound and uses the proved
  integrability, rather than assuming a moment bound.

An actual probability measure rules out an empty underlying probability
space. `W >= 1` forces a nonempty coefficient family for the weighted theorem.
Zero coefficients and zero-probability sample points are allowed. All random
variables and fixed coefficients have the correct quantifier order; the proof
does not choose coefficients after seeing a sample.

## Source provenance and replay limit

The source lemma was first reviewed under manuscript SHA256
`e9eb48925f087a64141c4b756ae3293856a87b353acae33f3fdc802b33f0f535`.
The worker receipt later recorded manuscript SHA256 `df1863e29aa83919557e71ac61d28d7fd291fc39ef1e4dbad3005569b6112ab1`.
During this independent review the shared manuscript had advanced to SHA256
`1c7f0fedc92989087219c2773411a42f610503846c6cf1e2dea5ac18961684f7`.
I therefore reopened `lem:conditioning-moment` by its actual label (then at line
4372); its mathematical statement and pattern-count proof still matched the
contract above. These source hashes are distinct observations, not one frozen
release receipt. Root-owned final source locking must use its final manuscript.

Independent private command from the repository root:

```powershell
lake env lean -o private-provenance-refs/8eb94655dbe2c338b99ddccdd0a1ebcae4feddf4c9d4667d59614e225225dc96/GeneralWeightedMomentSnapshot.olean private-provenance-refs/b0ff1c37baf42953c4d9502644ad56ffbe2272147377d7bdd62bcc672568624f/GeneralWeightedMomentSnapshot.lean
```

The replay used available production dependency objects; rebuilding imported
production dependencies, integration and source-bound paper gates remain with
the root. No production or manuscript edit, shared build, Git operation, or
subdelegation was performed.
