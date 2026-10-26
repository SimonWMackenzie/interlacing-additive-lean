"""Build and audit a new source checkout, recording successful command exits.

Run once in a fresh checkout after `lake exe cache get`. External package and
toolchain objects may be reused; this runner refuses existing project objects.
It does not delete objects or change any proof source.
"""
from datetime import datetime, timezone
from pathlib import Path
import hashlib
import json
import os
import subprocess
import sys

root = Path(__file__).resolve().parent
if hasattr(sys.stdout, "reconfigure"):
    sys.stdout.reconfigure(encoding="utf-8", errors="replace")
logs = root / "build-logs"
project_build = root / ".lake/build"
if project_build.exists() and any(p.is_file() for p in project_build.rglob("*")):
    raise SystemExit("Fresh replay requires an empty project .lake/build directory; use a new checkout.")
if logs.exists() or (root / "REPLAY.json").exists():
    raise SystemExit("Replay logs or receipt already exist; use a new checkout.")
if os.environ.get("LEAN_PATH") or os.environ.get("LEAN_SRC_PATH"):
    raise SystemExit("Unset LEAN_PATH and LEAN_SRC_PATH before a clean replay.")
logs.mkdir()

def now():
    return datetime.now(timezone.utc).isoformat()

def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

receipt = {
    "schema_version": 1,
    "status": "running",
    "started_utc": now(),
    "source_manifest_sha256": digest(root / "SOURCE_MANIFEST.json"),
    "project_build_initially_empty": True,
    "lake_artifact_cache": "disabled with LAKE_ARTIFACT_CACHE=false for every subprocess",
    "project_source_module_count": 5032,
    "external_objects": "Pinned toolchain and external package caches reused; external objects were not freshly rebuilt.",
    "v42_correspondence_checked": False,
    "commands": [],
}

def save():
    (root / "REPLAY.json").write_text(json.dumps(receipt, indent=2) + "\n", encoding="utf-8")

save()
replay_environment = os.environ.copy()
replay_environment["LAKE_ARTIFACT_CACHE"] = "false"
commands = [
    ("source-before", ["python", "verify_release.py"]),
    ("build", ["lake", "build", "CurrentAdditive"]),
    ("axiom-audit", ["lake", "env", "lean", "AxiomAudit.lean"]),
    ("raw-audit", ["lake", "env", "lean", "RawProofAudit.lean"]),
    ("providers", ["python", "check_replay.py", "build-logs/raw-audit.log"]),
    ("source-after", ["python", "verify_release.py"]),
]
for name, command in commands:
    log = logs / (name + ".log")
    record = {"command": command, "started_utc": now(), "log": log.relative_to(root).as_posix()}
    receipt["commands"].append(record)
    save()
    print("Running " + " ".join(command), flush=True)
    actual = [sys.executable, *command[1:]] if command[0] == "python" else command
    with log.open("wb") as output:
        process = subprocess.Popen(actual, cwd=root, env=replay_environment,
                                   stdout=output, stderr=subprocess.STDOUT)
        record["pid"] = process.pid
        save()
        code = process.wait()
    record.pop("pid", None)
    record.update({"exit_code": code, "finished_utc": now(), "log_sha256": digest(log)})
    save()
    print(f"Finished {name}: exit {code}", flush=True)
    if code:
        receipt.update({"status": "failed", "finished_utc": now()})
        save()
        print(log.read_text(encoding="utf-8", errors="replace")[-6000:], flush=True)
        raise SystemExit(code)

if digest(root / "SOURCE_MANIFEST.json") != receipt["source_manifest_sha256"]:
    receipt.update({"status": "failed", "reason": "Source manifest changed during replay", "finished_utc": now()})
    save()
    raise SystemExit(receipt["reason"])
receipt.update({"status": "passed", "finished_utc": now()})
save()
print("Fresh project-source build and both audits passed; provider and source checks passed.")
