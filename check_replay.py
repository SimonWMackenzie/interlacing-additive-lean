"""Check the active providers reported by RawProofAudit against the source manifest.

Usage: python check_replay.py build-logs/raw-audit.log
The Lean audit must finish successfully; its expected final counts are also
required here. External packages are checked against their Git revision pins.
"""
from pathlib import Path
import argparse
import json
import re
import subprocess

root = Path(__file__).resolve().parent
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("raw_audit_log", type=Path)
args = parser.parse_args()
text = args.raw_audit_log.read_text(encoding="utf-8-sig", errors="replace")
if "RAW_ROW_COUNTS rows=56544 theorems=37175 identical=56543 different=1 actualDependencies=59; standard3; no unsafe; kernelMissing=0" not in text:
    raise SystemExit("Expected raw-proof audit conclusion not found")
manifest = json.loads((root / "SOURCE_MANIFEST.json").read_text(encoding="utf-8"))
project = {e["module"] for e in manifest["files"] if e.get("role") == "checked_proof_source"}
expected = project | set(manifest["external_modules"])
providers = {}
for name, path in re.findall(r"RAW_ROW_RESOLVED\|([^|\r\n]+)\|([^\r\n]+)", text):
    if name in providers:
        raise SystemExit(f"Duplicate provider log entry: {name}")
    providers[name] = Path(path.strip()).resolve()
if set(providers) != expected:
    raise SystemExit(f"Provider mismatch: missing={sorted(expected-set(providers))}, extra={sorted(set(providers)-expected)}")
lean_prefix = Path(subprocess.check_output(
    ["lake", "env", "lean", "--print-prefix"], cwd=root, text=True).strip()).resolve()
lean_version = subprocess.check_output(["lake", "env", "lean", "--version"], cwd=root, text=True).strip()
if not re.search(r"Lean \(version 4\.30\.0,", lean_version):
    raise SystemExit(f"Unexpected active Lean toolchain: {lean_version}")
project_objects = (root / ".lake/build/lib/lean").resolve()
packages_dir = (root / ".lake/packages").resolve()
for name, path in providers.items():
    if not path.is_file():
        raise SystemExit(f"Missing proof object: {name}")
    if name in project:
        target = project_objects / (name.replace(".", "/") + ".olean")
        if path != target:
            raise SystemExit(f"Project module resolved outside fresh checkout: {name}")
    else:
        provider = manifest["external_providers"][name]
        if provider["kind"] == "toolchain":
            target = lean_prefix / "lib/lean" / (name.replace(".", "/") + ".olean")
        else:
            target = packages_dir / provider["package"] / ".lake/build/lib/lean" / (name.replace(".", "/") + ".olean")
        if path != target.resolve():
            raise SystemExit(f"External module has unexpected provider: {name}")
pins = json.loads((root / "lake-manifest.json").read_text(encoding="utf-8"))
for package in pins["packages"]:
    directory = packages_dir / package["name"]
    revision = subprocess.check_output(["git", "-C", str(directory), "rev-parse", "HEAD"], text=True).strip()
    if revision != package["rev"]:
        raise SystemExit(f"External dependency revision mismatch: {package['name']}")
    if subprocess.check_output(["git", "-C", str(directory), "status", "--porcelain", "--untracked-files=no"], text=True).strip():
        raise SystemExit(f"Modified external dependency: {package['name']}")
print(f"Verified {len(providers)} active providers, including {len(project)} local project objects, and all dependency revision pins.")
print(lean_version)
