"""Verify the public snapshot's file identities; this does not check proofs.

After this check, run `lake build CurrentAdditive`, `lake env lean AxiomAudit.lean`
and `lake env lean RawProofAudit.lean`. See BUILD.md for the exact scope.
"""
from collections import Counter
from pathlib import Path
import hashlib
import json

root = Path(__file__).resolve().parent
manifest = json.loads((root / "SOURCE_MANIFEST.json").read_text(encoding="utf-8"))
seen = set()
counts = Counter()
for entry in manifest["files"]:
    relative = entry["path"]
    if relative in seen:
        raise SystemExit(f"Duplicate manifest path: {relative}")
    seen.add(relative)
    path = (root / relative).resolve()
    if not path.is_relative_to(root) or not path.is_file():
        raise SystemExit(f"Missing or invalid path: {relative}")
    data = path.read_bytes()
    if len(data) != entry["bytes"] or hashlib.sha256(data).hexdigest() != entry["sha256"]:
        raise SystemExit(f"Source hash mismatch: {relative}")
    if entry.get("role") == "checked_proof_source":
        counts[entry["module"].split(".")[0]] += 1
assert dict(counts) == manifest["project_module_counts"] and sum(counts.values()) == 5032
source_dirs = ("src", "vendor/npc-cc", "papers/randomized-additive-hardness/formalization/lean",
               "papers/randomized-additive-hardness/formalization/current-v27/lean")
actual_sources = {p.relative_to(root).as_posix() for d in source_dirs for p in (root / d).rglob("*.lean")}
expected_sources = {e["path"] for e in manifest["files"] if e.get("role") == "checked_proof_source"}
if actual_sources != expected_sources:
    raise SystemExit("Unexpected or missing local Lean sources in the release")
print(f"Verified {len(seen)} files, including all 5032 recorded project modules.")
print("File identity is not a proof build, a source-correspondence check, or verification of v42.")
