# Reproducing this proof snapshot

This package targets the exact v40 manuscript in `manuscript-v40/`, with
main-source SHA-256
`8cfdd735e5703682f98c840df96397dea74ef2795716f7bdddb3b7e562e64cb0`.
The manuscript files are frozen provenance, not the current editable paper.
Correspondence with v42 has not been checked.

Install Lean through elan and Python 3.11 or later. The included toolchain
file selects Lean 4.30.0; `lake-manifest.json` pins Mathlib and its dependencies.
From this repository's root:

```sh
python verify_release.py
lake exe cache get
python replay.py
```

The runner refuses an existing project build directory, disables Lake's artifact
cache with `LAKE_ARTIFACT_CACHE=false`, stops on any failed command, and records
source identity, command exit codes and log hashes in
`REPLAY.json`. It builds `CurrentAdditive`, runs both Lean audits, checks the
resolved object paths and dependency revisions, and rechecks source identity.
Use a fresh checkout for another clean replay; the script never deletes files.

The cache command downloads compiled external dependencies. All 5,032 local
proof modules are supplied as source; do not substitute project objects from
another checkout. The source check verifies their exact identities. The build
checks their Lean proofs. The owning audit checks the transitive axioms of
CurrentAdditive declarations; the supplemental audit also checks raw generated
proof rows, including the historical duplicate-name case. These checks do not
establish that external source-theorem interfaces faithfully represent the
cited papers, or that a later manuscript matches this snapshot.

The earlier local completion record used a fresh build of 2,678 CurrentAdditive
modules and reused inherited objects. Its provider inventory initially missed
80 meta-import dependencies; subsequent recovery preserved that failure,
checked all 15,633 providers and audited the actual raw proof expressions.
The public-package replay is a separate check and must report whether its
inherited project sources and external dependency objects were rebuilt or reused.

## Assumptions and attribution

The source reduction interfaces for Dinur, Bogdanov--Obata--Trevisan and the
Guruswami--Lee alternating source remain explicit, as do literal-CNF hardness
and the distinct deterministic and randomized ETH assumptions. A theorem about
one of these interfaces does not construct or prove the external result.

The `CurrentAdditive`, `Paper2` and `EthInapproximability` trees contain the
authors' successive developments. The `Workspace`, `NPCC`, `EthBridge` and
`LegacyNPCC` trees preserve the inherited NP-hardness development used by the
checked dependency closure. `manuscript-v40/COVERAGE.json` preserves the historical
group-based map for 73 formal and auxiliary manuscript blocks. Every block has
anchors in the imported proof closure. The map also cites one older helper,
`Paper2.AveragedProjection.rational_monotonicity_member`, which the final proof
does not import. Its exact source is preserved in `historical-coverage-supplements/`
and marked as outside the release build. The map is navigation through the
earlier evidence, not a new statement-fidelity review.

Original source notices are retained. No blanket license is added by this
packaging step. The separately fetched dependencies
retain their own licenses (Apache-2.0, and MIT for Cli).
