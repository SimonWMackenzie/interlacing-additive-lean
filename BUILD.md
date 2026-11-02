# Checking and reproducing this v43 source snapshot

Use Python 3.11 or later and the Lean toolchain selected by lean-toolchain.
lake-manifest.json pins Mathlib and every fetched dependency. Run all commands
below from the supplied package root unless another root is specified.

First verify the source identities, full manuscript correspondence, declaration
anchors, review bindings and any accepted build/replay evidence:

```sh
python verify_release.py
```

This source/evidence verifier does not compile Lean. Complete manuscript
correspondence is separately recorded in FULL_COVERAGE_RECEIPT.json. The 54 v43
proof additions and all three direct algorithmic results passed independent
review and integrated production build/audit checks before packaging.

## Canonical checked incremental build

PUBLISHED_CHECKED_BUILD.json records this mode when accepted; release-status.json
binds its exact identity. It reuses existing inherited project objects and does
not claim a cold source rebuild.

To repeat it against a matching development checkout that already has project
objects, use the actual CLI below. Replace the two placeholder paths; OUTPUT
must be a new directory outside the source package.

```sh
python checked_build.py --root MATCHING_DEVELOPMENT_CHECKOUT --source-package . --output NEW_CHECKED_BUILD_DIRECTORY
```

The runner checks exact sources, configuration, admissions and prior-release
provenance; runs `lake build CurrentV43`, AxiomAudit.lean and RawProofAudit.lean;
checks every resolved provider, object hash and dependency pin; then checks the
sources again. Lake's artifact cache is disabled for its subprocesses. Production
resource settings are preserved; only the public package's default target is
changed to CurrentV43. Private compiler overrides are not supplied silently.

The runner writes CHECKED_BUILD.json and logs to the selected output directory.
It does not commit, publish or replace this package's accepted public receipt.
PUBLISHED_CHECKED_EVIDENCE_BINDING.json distinguishes original receipt/log hashes
from hashes of path-projected public evidence.

## Optional cold project-source replay

Use a separate fresh source checkout/copy with no local project objects in
.lake/build, no local REPLAY.json and no local build-logs directory. Existing
external toolchain and pinned dependency caches may be reused.

```sh
python verify_release.py
lake exe cache get
python replay.py
```

replay.py accepts no root argument: run it from the fresh package root. It
refuses existing project objects or externally set LEAN_PATH, LEAN_SRC_PATH or
LEAN_SYSROOT. It disables Lake's artifact cache, builds every imported local
project module, runs both audits and the provider/pin checks, and verifies the
source package before and after. It writes a new local REPLAY.json and
build-logs; it never deletes existing evidence. Repeating this mode requires
another fresh checkout.

PUBLISHED_REPLAY.json and published-build-logs, when present, are separately
accepted public cold-replay evidence. A successful local replay does not replace
them automatically. Cached external objects are explicitly distinguished from
the freshly compiled local project modules.

## Audit and assumption scope

AxiomAudit.lean checks effective declarations owned by imported CurrentAdditive,
CurrentV42 and CurrentV43 modules and their transitive proof axioms.
RawProofAudit.lean also examines their actual generated/private rows. Where raw
and effective expressions differ, it checks the raw type and proof dependencies.
Only propext, Classical.choice and Quot.sound are permitted in audited proof
dependencies; unsafe owned declarations and missing checked dependencies fail.

All inherited local providers are included in SOURCE_MANIFEST.json. Reachable
proof dependencies are audited transitively; unused inherited citation assertions
are not promoted into the checked theorem scope. Exact source-reduction,
language and complexity premises remain visible in theorem interfaces. The
three direct runtime implications do not assume ETH. External Dinur/BOT record
fidelity remains qualified separately from compilation and manuscript matching.

The source verifier, independent correspondence reviews, canonical incremental
check, optional cold replay and website deployment are distinct evidence. A
website view or successful artifact download does not replace a Lean build.
