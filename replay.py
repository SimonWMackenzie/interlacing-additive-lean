"""Fresh CurrentV42 source build, both audits, provider pins and source checks.

External pinned toolchain/package caches can be reused. This runner refuses
all existing project objects, creates logs/receipt, and never deletes files.
"""
from datetime import datetime, timezone
import os
import subprocess
import sys
from release_common import ROOT, need, read, sha, write
from check_replay import COMMANDS, check_receipt

def now():
    return datetime.now(timezone.utc).isoformat()

def run(root=ROOT):
    project_build = root/".lake/build"
    need(not project_build.exists() or not any(p.is_file() for p in project_build.rglob("*")),
         "Fresh replay requires empty project .lake/build; use a new checkout")
    need(not (root/"build-logs").exists() and not (root/"REPLAY.json").exists(), "Replay output exists; use a new checkout")
    for name in ("LEAN_PATH", "LEAN_SRC_PATH", "LEAN_SYSROOT"):
        need(not os.environ.get(name), "Unset "+name+" before replay")
    manifest = read(root/"SOURCE_MANIFEST.json")
    logs = root/"build-logs"
    logs.mkdir()
    receipt = {"schema_version": 2, "status": "running", "started_utc": now(),
               "target": "CurrentV42", "source_manifest_sha256": sha(root/"SOURCE_MANIFEST.json"),
               "full_coverage_receipt_sha256": sha(root/"FULL_COVERAGE_RECEIPT.json"),
               "project_build_initially_empty": True,
               "lake_artifact_cache": "disabled with LAKE_ARTIFACT_CACHE=false for every subprocess",
               "project_modules_compiled_from_source": manifest["project_module_count"],
               "external_objects": "Pinned toolchain and package cached objects reused; external objects not freshly rebuilt.",
               "v42_correspondence": "Independent source-bound root gate, distinct from this proof replay.",
               "commands": []}
    def save():
        write(root/"REPLAY.json", receipt)
    save()
    environment = os.environ.copy()
    environment["LAKE_ARTIFACT_CACHE"] = "false"
    for name, command in COMMANDS:
        log = logs/(name+".log")
        record = {"command": command, "started_utc": now(), "log": log.relative_to(root).as_posix()}
        receipt["commands"].append(record)
        save()
        print("Running "+" ".join(command), flush=True)
        actual = [sys.executable, *command[1:]] if command[0] == "python" else command
        with log.open("wb") as output:
            process = subprocess.Popen(actual, cwd=root, env=environment, stdout=output, stderr=subprocess.STDOUT)
            code = process.wait()
        record.update({"exit_code": code, "finished_utc": now(), "log_sha256": sha(log)})
        save()
        if code:
            receipt.update({"status": "failed", "finished_utc": now()})
            save()
            print(log.read_text(encoding="utf-8", errors="replace")[-6000:], flush=True)
            raise SystemExit(code)
    need(receipt["source_manifest_sha256"] == sha(root/"SOURCE_MANIFEST.json"), "Source manifest changed during replay")
    receipt.update({"status": "passed", "finished_utc": now(),
                    "provider_inventory_sha256": sha(logs/"PROVIDER_INVENTORY.json")})
    check_receipt(root, receipt)
    save()
    print("Fresh CurrentV42 project build, effective/raw proof audits, complete providers and source identities passed.")

if __name__ == "__main__":
    try:
        run()
    except (ValueError, OSError, KeyError) as error:
        raise SystemExit("FAIL: "+str(error))
