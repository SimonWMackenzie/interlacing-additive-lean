# Interlacing and additive inapproximability: Lean companion

This repository contains the Lean sources for an earlier **v40 snapshot** of
*Interlacing and Additive Inapproximability of Deterministic Communication
Complexity*, by Serge Gaspers, Tao Zixu He, and Simon Mackenzie. The development
studies how hard it is to estimate the communication needed to compute a Boolean
table exactly. Its randomized results concern the construction and estimator;
the communication cost being estimated is still deterministic.

The [frozen manuscript](manuscript-v40/output/INTERLACING_AND_ADDITIVE_INAPPROXIMABILITY_v40.pdf)
and [TeX source](manuscript-v40/source/main.tex) identify the snapshot covered by
the local completion record of 22 October 2026. Its main-source SHA-256 is
`8cfdd735e5703682f98c840df96397dea74ef2795716f7bdddb3b7e562e64cb0`.
**Correspondence with manuscript v42 has not been checked.** For the separate
public-package build and audit status, consult
[PUBLISHED_REPLAY.json](PUBLISHED_REPLAY.json) and
[release-status.json](release-status.json).

Here, `T` is the number of entries in an explicit total Boolean table, and
logarithms are to base two. These four modules provide useful starting points:

| Result | Starting module and declarations |
|---|---|
| **Deterministic fixed gaps.** For each fixed integer `k ≥ 1`, a polynomial-time reduction separates satisfiable from unsatisfiable encoded CNF inputs by a communication-cost gap of `k`. A permitted deterministic estimator with any fixed nonnegative additive error puts every NP language in P, assuming the stated CNF hardness. | [V40DeterministicFixedPhysical.lean](papers/randomized-additive-hardness/formalization/current-v27/lean/CurrentAdditive/V40DeterministicFixedPhysical.lean): `fixed_gap_reduction`, `fixed_gap_exact_no`, `fixed_additive_np_subset_p`. |
| **Deterministic growing error.** Under deterministic sparse ETH, there is a positive construction-dependent constant `c` for which no permitted deterministic estimator achieves error `c log log T` on all sufficiently large tables. | [V40DeterministicClassEndpoint.lean](papers/randomized-additive-hardness/formalization/current-v27/lean/CurrentAdditive/V40DeterministicClassEndpoint.lean): `deterministic_growing_hardness`, `deterministic_growing_square_class`. |
| **Randomized growing error.** Under randomized sparse ETH, for every `0 ≤ c < 1/8`, no permitted randomized estimator achieves error `c log T / log log T` with success probability at least `2/3` on every sufficiently large table. This already holds for square tables with power-of-two side length. | [V40RandomizedClassEndpoint.lean](papers/randomized-additive-hardness/formalization/current-v27/lean/CurrentAdditive/V40RandomizedClassEndpoint.lean): `quantitative_class`, `quantitative_square_class`. |
| **Strict alternation.** When Alice speaks first and the players alternate, the construction gives a deterministic polynomial-time reduction from encoded CNF with every fixed gap `k ≥ 1`. | [V39LiteralYaoNPJoin.lean](papers/randomized-additive-hardness/formalization/current-v27/lean/CurrentAdditive/V39LiteralYaoNPJoin.lean): `approved_cnf_fixed_gap_reduction`, `approved_cnf_strict_alice_nphard`. |

“Permitted estimator” includes an explicit polynomial-time machine and efficient
comparison of its encoded numerical output with thresholds of the form `m/2`.
The exact estimator and communication conventions are part of the Lean
statements. The alternating development also includes the stated fixed-error
estimator consequences for its four starter/output conventions; the coverage
map identifies their declarations.

The unrestricted results take the [Dinur](src/EthInapproximability/CurrentPaper/EncodedETHSource.lean#L149)
and [Bogdanov–Obata–Trevisan](src/EthInapproximability/CurrentPaper/EncodedETHSource.lean#L341)
reduction records as inputs. Their fields specify the gap, size, degree and
runtime guarantees required by the later proofs. The alternating results take the Guruswami–Lee source record
and its identification with the encoded CNF language. CNF hardness and the
appropriate deterministic or randomized ETH hypothesis remain explicit where
used. These external records are not constructed here, and their fidelity to
the cited source theorems remains a separate qualification.

To reproduce the package checks, install Lean through elan and Python 3.11 or
later, then follow [BUILD.md](BUILD.md) from a fresh checkout:

```sh
python verify_release.py
lake exe cache get
python replay.py
```

The [replay runner](replay.py) builds the project sources, runs the axiom and
raw-proof audits, checks dependency locations and revisions, and records the
outcome in `REPLAY.json`. It requires an empty project build directory, disables Lake's artifact cache,
and reuses external dependency objects. Only `propext`, `Classical.choice`,
and `Quot.sound` may occur in dependencies of the checked results. Some inherited
files contain unused citation axioms. A successful audit does not establish
manuscript correspondence or the fidelity of external source records.

`PUBLISHED_REPLAY.json` preserves the release's accepted build receipt;
`REPLAY.json` is created by your own run. Keeping these separate lets a fresh
checkout run the checks without overwriting the published evidence.

The [coverage map](manuscript-v40/COVERAGE.json) connects all 73 formal and
auxiliary manuscript blocks to the earlier declaration references. Every block
has references within the imported proof sources. One older helper,
`Paper2.AveragedProjection.rational_monotonicity_member`, is preserved under
[historical-coverage-supplements](historical-coverage-supplements/papers/randomized-additive-hardness/formalization/lean/Paper2/AAvgRationalMembers.lean)
and explicitly marked as outside the build. Its source is historical reference
material; the package replay does not compile it. The map preserves earlier
coverage evidence and is not a new review of each statement's correspondence.

The independent Beyond the Library formalization of the corrected
Mackenzie–Saffidine direct-sum result is a separate development, with its own
[public proof inspector](https://beyondthelibrary.github.io/formal_archive/p/Refuting/).
Original source notices are retained; dependency licenses and further
attribution are described in [BUILD.md](BUILD.md).
