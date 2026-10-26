"""Check dynamically observed audit counts, all providers, and dependency pins.

Usage: python check_replay.py build-logs/raw-audit.log
Run only after both Lean audits exit successfully. Provider identity does not
establish that external cached objects were rebuilt from source.
"""
from pathlib import Path
import argparse
import re
import subprocess
from release_common import ROOT, check_pin, need, read, sha, write

COMMANDS = [
    ("source-before", ["python", "verify_release.py"]),
    ("build", ["lake", "build", "CurrentV42"]),
    ("axiom-audit", ["lake", "env", "lean", "AxiomAudit.lean"]),
    ("raw-audit", ["lake", "env", "lean", "RawProofAudit.lean"]),
    ("providers", ["python", "check_replay.py", "build-logs/raw-audit.log"]),
    ("source-after", ["python", "verify_release.py"]),
]

def check_receipt(root, receipt, published=False):
    need(receipt.get("status") == "passed" and receipt.get("project_build_initially_empty") is True,
         "Replay receipt is not a successful fresh project replay")
    need(receipt.get("source_manifest_sha256") == sha(root/"SOURCE_MANIFEST.json"), "Replay manifest identity mismatch")
    need(receipt.get("full_coverage_receipt_sha256") == sha(root/"FULL_COVERAGE_RECEIPT.json"), "Replay coverage identity mismatch")
    records = receipt["commands"]
    need([r["command"] for r in records] == [c for _,c in COMMANDS] and
         all(r.get("exit_code") == 0 for r in records), "Missing/failed/changed replay command")
    for record in records:
        base = "published-build-logs" if published else "build-logs"
        path = root/base/Path(record["log"]).name
        expected_hash = record.get("public_log_sha256", record["log_sha256"]) if published else record["log_sha256"]
        need(path.is_file() and sha(path) == expected_hash, "Missing/changed replay log")
    inventory = root/("published-build-logs" if published else "build-logs")/"PROVIDER_INVENTORY.json"
    inventory_hash = receipt.get("published_provider_inventory_sha256", receipt.get("provider_inventory_sha256")) if published else receipt.get("provider_inventory_sha256")
    need(inventory.is_file() and sha(inventory) == inventory_hash,
         "Missing/changed provider inventory")
    manifest = read(root/"SOURCE_MANIFEST.json")
    need(receipt.get("project_modules_compiled_from_source") == manifest["project_module_count"],
         "Replay module census differs from release")
    if published:
        binding=read(root/"PUBLISHED_EVIDENCE_BINDING.json")
        for entry in binding["identity_bindings"]:
            check_pin(root,{"path":entry["release_path"],"sha256":entry["public_sha256"]})

def check(root, raw_audit_log, manifest_path=None, output_path=None):
    text = raw_audit_log.read_text(encoding="utf-8-sig", errors="replace")
    pattern = (r"RAW_ROW_COUNTS owners=(\d+) v42Owners=(\d+) rows=(\d+) theorems=(\d+) "
               r"identical=(\d+) different=(\d+) actualDependencies=(\d+); standard3; no unsafe; kernelMissing=0")
    conclusions = re.findall(pattern, text)
    need(len(conclusions) == 1 and text.count("RAW_PROOF_AUDIT_COMPLETE") == 1,
         "Missing/duplicate raw proof audit conclusion")
    owners, v42owners, rows, theorems, identical, different, dependencies = map(int, conclusions[0])
    need(owners > 0 and v42owners > 0 and rows > 0 and 0 < theorems <= rows and identical+different == rows,
         "Inconsistent raw proof row counts")
    manifest = read(manifest_path or root/"SOURCE_MANIFEST.json")
    project = {e["module"] for e in manifest["files"] if e.get("role") == "checked_proof_source"}
    owned = {m for m in project if m == "CurrentV42" or m.startswith("CurrentV42.") or
             m == "CurrentAdditive" or m.startswith("CurrentAdditive.")}
    need(owners == len(owned) and v42owners == len([m for m in project if m.startswith("CurrentAdditive.V42")]),
         "Raw audit did not cover the exact target-owned module set")
    pairs = re.findall(r"RAW_ROW_RESOLVED\|([^|\r\n]+)\|([^\r\n]+)", text)
    need(len(pairs) == len({m for m,_ in pairs}), "Duplicate resolved module")
    providers = {m:Path(p.strip()).resolve() for m,p in pairs}
    need(set(providers) == project|set(manifest["external_modules"]), "Provider inventory differs from exact release closure")
    prefix = Path(subprocess.check_output(["lake", "env", "lean", "--print-prefix"], cwd=root, text=True).strip()).resolve()
    version = subprocess.check_output(["lake", "env", "lean", "--version"], cwd=root, text=True).strip()
    toolchain = (root/"lean-toolchain").read_text(encoding="utf-8-sig").strip()
    requested = toolchain.rsplit(":v", 1)[-1]
    need(re.search(r"Lean \(version "+re.escape(requested)+r",", version), "Unexpected active toolchain: "+version)
    objects = (root/".lake/build/lib/lean").resolve()
    packages = (root/".lake/packages").resolve()
    inventory = []
    for module, path in sorted(providers.items()):
        suffix = Path(*module.split(".")).with_suffix(".olean")
        if module in project:
            target = objects/suffix
        else:
            provider = manifest["external_providers"][module]
            target = prefix/"lib/lean"/suffix if provider["kind"] == "toolchain" else packages/provider["package"]/".lake/build/lib/lean"/suffix
        need(path == target.resolve() and path.is_file(), "Unexpected or missing provider: "+module)
        inventory.append({"module": module, "provider_kind": "project" if module in project else manifest["external_providers"][module]["kind"],
                          "olean_sha256": sha(path), "bytes": path.stat().st_size})
    pins = read(root/"lake-manifest.json")
    for package in pins["packages"]:
        directory = packages/package["name"]
        revision = subprocess.check_output(["git", "-C", str(directory), "rev-parse", "HEAD"], text=True).strip()
        need(revision == package["rev"], "External dependency revision mismatch: "+package["name"])
        modified = subprocess.check_output(["git", "-C", str(directory), "status", "--porcelain", "--untracked-files=no"], text=True).strip()
        need(not modified, "Tracked external source modifications: "+package["name"])
    write(output_path or root/"build-logs/PROVIDER_INVENTORY.json", {"lean_version": version,
          "toolchain_sha256": sha(root/"lean-toolchain"), "dependency_manifest_sha256": sha(root/"lake-manifest.json"),
          "project_modules": len(project), "raw_rows": rows, "raw_theorems": theorems,
          "raw_different_rows": different, "raw_actual_dependencies": dependencies, "providers": inventory})
    print(f"Verified {len(providers)} providers including {len(project)} local project modules; {rows} owned raw proof rows.")
    print(version)

if __name__ == "__main__":
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("raw_audit_log", type=Path)
    args = p.parse_args()
    try:
        check(ROOT, args.raw_audit_log)
    except (ValueError, OSError, KeyError, subprocess.CalledProcessError) as error:
        raise SystemExit("FAIL: "+str(error))
