# Reproducing the source snapshot

Install Lean through elan and Python 3.11 or later. `lean-toolchain` selects the
toolchain and `lake-manifest.json` pins Mathlib and every fetched dependency.
The canonical checked-build receipt and a cold project-source replay are
different forms of evidence. The release status identifies which passed.

The canonical route uses existing unchanged inherited project objects. It first
checks every supplied proof source, the exact production configuration, admission
registry, and prior v40 fresh-release source/receipt identities. It runs
`lake build CurrentV42`, both complete audits and every provider/object/pin
check, then checks the source package again. Every imported object is hashed.
`PUBLISHED_CHECKED_BUILD.json` explicitly records
`project_build_initially_empty: false` and `fresh_project_replay: false`.
It does not claim all unchanged inherited project modules were cold rebuilt.

For the optional cold project-source replay, run from a fresh checkout:

```sh
python verify_release.py
lake exe cache get
python replay.py
```

That runner refuses existing project objects in `.lake/build`, existing local
replay logs, and externally set Lean search paths. It disables Lake's artifact
cache for every subprocess with `LAKE_ARTIFACT_CACHE=false`, builds `CurrentV42`,
runs the effective-declaration and raw-proof audits, checks all active object
providers and dependency source revisions, then rechecks the source package.
It stops on a failed command and writes `REPLAY.json` and `build-logs/`.
Nothing is deleted. Use another fresh checkout to repeat the replay.

The package preserves the production-validated Lake options and exact
source-local resource settings; only its default target changes to `CurrentV42`.
`RESOURCE_LIMITS.json` records these settings. Private compiler flags are not
silently added to the fresh replay: that replay must succeed using the supplied
sources and configuration.

Pinned toolchain objects and fetched external package objects can be reused.
All imported local project modules must be compiled in a fresh replay checkout.
The receipt states this distinction and records the observed module count;
there is no fixed historical count. `PROVIDER_INVENTORY.json` records hashes of
the actual object files, the toolchain identity and dependency manifest.
These hashes identify the objects used; they do not prove cached external
objects were compiled locally from source.

`AxiomAudit.lean` checks every effective declaration owned by imported
`CurrentAdditive` and `CurrentV42` modules and its transitive proof axioms.
`RawProofAudit.lean` additionally checks all actual generated rows owned by
those modules. If a raw row differs from the effective declaration, it checks
the actual type/proof expressions and their dependencies. Counts are observed
and cross-checked against the release's imported owner set. The audit permits
only `propext`, `Classical.choice`, and `Quot.sound` as proof dependencies and
rejects unsafe owned declarations or missing checked dependencies.

The complete provider inventory includes inherited `Paper2`,
`EthInapproximability`, `LegacyNPCC`, `Workspace`, `NPCC`, and `EthBridge` modules.
Reachable dependencies of the audited proof rows are checked transitively.
An unused inherited citation assertion is not promoted into the release's
checked theorem scope merely because its file is supplied for reproducibility.

`verify_release.py` checks file identities, exact local Lean source paths,
the admitted v42 module registry and review hashes, every accepted declaration
anchor, all formal and unnumbered coverage rows, and the independent coverage
gate bindings. Those identity checks do not replace the independent statement
reviews or establish fidelity of external source-theorem records.

Canonical checked-build evidence is kept in `PUBLISHED_CHECKED_BUILD.json` and
`published-checked-build-logs/`, with explicit path-projection bindings in
`PUBLISHED_CHECKED_EVIDENCE_BINDING.json`. Original private receipt/log hashes
and distinct public hashes are retained. These files do not assert a fresh replay.

Optional published fresh-replay evidence is kept in `PUBLISHED_REPLAY.json` and
`published-build-logs/`. Machine paths are projected to relative provenance IDs;
original/private and public/projected hashes are separately recorded in
`PUBLISHED_EVIDENCE_BINDING.json`. Executables, flags, exit codes and audit
conclusions are retained. Original private logs remain archived locally.
Your replay creates separate local files and does not
overwrite that evidence. Historical v40 receipts under `archive/v40/` are
preserved verbatim and do not certify the current source.

Historical private build-authority receipts bind their original manifest hash,
which is not the hash of a projected manifest. They preserve the attestation
trace and do not replace the current canonical checks or optional fresh public replay. Five already-public legacy
path comments in inherited source files have exact hash/line exceptions under
`PUBLIC_PATH_EXCEPTIONS.json`; those nonpersonal comments are preserved with
the proof bytes. New personal paths, attachment locations and credential data
are rejected during preparation.

Mathlib and the other fetched dependencies retain their own licenses, including
Apache-2.0 and the Cli package's MIT license. Original project notices remain.
