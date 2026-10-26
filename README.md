# Interlacing and additive inapproximability: Lean companion

This source snapshot accompanies the exact v42 manuscript of *Interlacing and
Additive Inapproximability of Deterministic Communication Complexity*, by Serge
Gaspers, Tao Zixu He, and Simon Mackenzie. The paper studies the difficulty of
estimating the deterministic communication cost of an explicit Boolean table.
Randomized constructions and estimators do not change that communication model.

Explore the paper alongside its Lean proofs in the
[interactive proof inspector](https://simonwmackenzie.github.io/interlacing-additive-lean/inspector/),
with statement highlights, source search, and explanations of definitions and
Lean commands.

Read the [manuscript](manuscript-v42/output/INTERLACING_AND_ADDITIVE_INAPPROXIMABILITY_v42.pdf),
[single TeX source](manuscript-v42/source/main.tex),
[bibliography](manuscript-v42/source/references.bib), and
[source-to-Lean map](manuscript-v42/V42_STATEMENT_MAP.json).
The aggregate is [CurrentV42.lean](papers/randomized-additive-hardness/formalization/current-v42/lean/CurrentV42.lean).

The independent source-correspondence evidence is bound by
[FULL_COVERAGE_RECEIPT.json](FULL_COVERAGE_RECEIPT.json). This is distinct from
the package build: [release-status.json](release-status.json) identifies the
accepted verification mode. [PUBLISHED_CHECKED_BUILD.json](PUBLISHED_CHECKED_BUILD.json),
when present, records a canonical `CurrentV42` build with unchanged inherited
project objects reused, complete effective/raw audits, and exact source,
object, provider and dependency checks. It is not a cold source rebuild.
When present,
[PUBLISHED_REPLAY.json](PUBLISHED_REPLAY.json) and `published-build-logs/` preserve
the separate fresh project-source replay. A staging package without an accepted
build-and-audit receipt is not a completed release.

To perform the optional cold project-source reproduction in a fresh checkout:

```sh
python verify_release.py
lake exe cache get
python replay.py
```

See [BUILD.md](BUILD.md) for the exact scope and cache boundary. The manifest
records the exact imported local source closure, including inherited libraries
and meta-imports. Only `CurrentAdditive` and `CurrentV42` own the audited rows;
their actual transitive proof dependencies may use only `propext`,
`Classical.choice`, and `Quot.sound`. The audit also inspects generated raw
rows whose expressions differ from their effective declarations.

External source-reduction records, literal-CNF hardness and deterministic or
randomized ETH hypotheses remain explicit in the theorem interfaces. The
release does not construct those external source theorems or certify that
their records faithfully represent the cited papers. Some inherited sources
contain unused citation axioms. Those assertions are not part of the release's
checked theorem dependency claims.

Lean source paths match the development repository. [RELEASE_BINDING.json](RELEASE_BINDING.json)
translates the manuscript namespace and binds the public provenance copies.
Those copies replace private path locations by relative evidence IDs while
preserving source hashes and review conclusions. Original private hashes and
projected public hashes are distinct. Original private receipts are archived
locally. Canonical incremental verification and optional fresh reproduction
retain distinct public receipts and cache boundaries.
Earlier [v40 manuscript files](manuscript-v40/source/main.tex) remain frozen.
The old README, source manifest and replay receipts under `archive/v40/` refer
only to that earlier release, and their original relative paths are historical.
The unimported helper under `historical-coverage-supplements/` remains reference
material outside the current build.

The separate Beyond the Library formalization of the corrected
Mackenzie–Saffidine direct-sum result has its own
[public inspector](https://beyondthelibrary.github.io/formal_archive/p/Refuting/).
Original notices and dependency licenses are retained; no blanket license is
added by packaging this development.
