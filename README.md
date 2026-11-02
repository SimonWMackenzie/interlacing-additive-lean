# v43 Lean companion: communication complexity and 3-SAT running time

This source snapshot accompanies v43 of *NP-Hardness and Additive
Inapproximability of Deterministic Communication Complexity*, by Serge Gaspers,
Tao Zixu He and Simon Mackenzie.

Start with the [interactive paper and Lean inspector](https://simonwmackenzie.github.io/interlacing-additive-lean/inspector/).
It connects highlighted manuscript statements to their checked Lean sources and
explains the recorded verification and assumptions. It displays a verification
snapshot; it does not execute Lean in the browser.

The v43 additions prove the general implication from a communication-cost
estimator to an algorithm for sparse 3-SAT, and its two explicit running-time
corollaries. The general result covers deterministic and randomized estimators
with either construction. All 54 added proof modules were independently
reviewed, integrated, production-compiled and included in the effective and
raw-proof audits. The three runtime results have independently reviewed
correspondence with the current manuscript. Earlier checked components are
retained with their original evidence.

- [Manuscript PDF](manuscript-v43/output/INTERLACING_AND_ADDITIVE_INAPPROXIMABILITY_v43.pdf),
  [LaTeX source](manuscript-v43/source/main.tex) and
  [bibliography](manuscript-v43/source/references.bib).
- [Statement-to-Lean map](manuscript-v43/V43_STATEMENT_MAP.json) and
  [exact source lock](manuscript-v43/SOURCE_LOCK.json).
- [CurrentV43 aggregate](papers/randomized-additive-hardness/formalization/current-v43/lean/CurrentV43.lean)
  and [new-module admissions](papers/randomized-additive-hardness/formalization/current-v43/ADMITTED_MODULES.json).
- [Source-correspondence receipt](FULL_COVERAGE_RECEIPT.json),
  [source manifest](SOURCE_MANIFEST.json) and [package verification status](release-status.json).

From this repository root, check the supplied identities and evidence with:

```sh
python verify_release.py
```

[BUILD.md](BUILD.md) gives the canonical checked-build and optional cold-replay
commands. `PUBLISHED_CHECKED_BUILD.json`, when recorded, binds the canonical
incremental build, both audits and complete source/provider/object checks to
this exact package. Unchanged inherited project objects are reused. A separate
`PUBLISHED_REPLAY.json`, when recorded, certifies a fresh compilation of every
imported local project module. The package status states which checks passed;
an incremental build is not a cold replay. Pinned external toolchain and
dependency objects may be reused in either mode.

The cited Dinur and BOT reductions remain explicit source interfaces. Their
published-source fidelity retains the inherited author-owned qualification;
the formalization does not construct those external records. The three direct
runtime implications use no ETH assumption. Historical hardness and
strict-alternation results retain their own explicit hypotheses, including
selected-language identities where required.

The effective and raw audits cover the imported CurrentAdditive, CurrentV42
and CurrentV43 rows and their transitive proof dependencies, permitting only
`propext`, `Classical.choice` and `Quot.sound`. Raw rows whose expressions differ
from their effective declarations are checked separately. Unused inherited
citation assertions are outside the checked theorem dependency claims.

The source manifest records the complete imported local proof closure,
including meta imports. RELEASE_BINDING.json distinguishes original evidence
hashes from hashes of public path projections. Lean proof bytes and their
root-relative paths are preserved. The v40 and v42 manuscript snapshots and
historical metadata retain their original scope; their receipts do not certify
new source states.

The separate Beyond the Library formalization of the corrected
Mackenzie–Saffidine direct-sum result has its own
[public inspector](https://beyondthelibrary.github.io/formal_archive/p/Refuting/).
Original project notices and dependency licenses are retained.
