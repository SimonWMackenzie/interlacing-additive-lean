"""Canonical checked incremental build; unchanged inherited objects may be reused.

This is NOT a fresh project-source replay. Existing project objects are required.
All supplied sources, providers, object hashes, dependency pins, audits and prior
v40 fresh-release provenance are checked. Use replay.py for a cold project build.
"""
from datetime import datetime, timezone
from collections import Counter
from pathlib import Path
import argparse
import contextlib
import hashlib
import json
import os
import re
import subprocess
import sys
from release_common import ROOT, OWNER, check_pin, find_project_root, need, original_digest, read, sha, write
from verify_release import verify
from check_replay import check

def now():
    return datetime.now(timezone.utc).isoformat()

def unchanged_prior(package,manifest):
    old_manifest=package/"archive/v40/SOURCE_MANIFEST.json"
    old_receipt=package/"archive/v40/PUBLISHED_REPLAY.json"
    previous,receipt=read(old_manifest),read(old_receipt)
    prior=[e for e in previous["files"] if e.get("role")=="checked_proof_source"]
    counts=dict(Counter(e["module"].split(".")[0] for e in prior))
    need(prior and len({e["module"] for e in prior})==len(prior) and
         counts==previous["project_module_counts"] and
         receipt.get("project_source_module_count")==len(prior),
         "Prior v40 source census disagrees with its accepted fresh receipt")
    need(receipt.get("status")=="passed" and receipt.get("project_build_initially_empty") is True and
         receipt.get("source_manifest_sha256")==sha(old_manifest) and receipt.get("commands") and
         all(r.get("exit_code")==0 for r in receipt["commands"]), "Missing accepted prior v40 fresh-project provenance")
    current={e["module"]:e for e in manifest["files"] if e.get("role")=="checked_proof_source"}
    need(all(e["module"] in current and current[e["module"]]["path"]==e["path"] and
             current[e["module"]]["sha256"]==e["sha256"] and current[e["module"]]["bytes"]==e["bytes"]
             for e in prior), "Inherited v40 source changed or left closure; this bounded reuse path requires separate review")
    return {"unchanged_prior_source_modules":len(prior),"prior_public_source_manifest_sha256":sha(old_manifest),
            "prior_public_fresh_replay_sha256":sha(old_receipt)}

def source_match(root, package):
    manifest=verify(package)
    tools={}
    for filename in ("checked_build.py","check_replay.py","release_common.py","verify_release.py"):
        need(sha(ROOT/filename)==sha(package/filename), "Executing verification helper differs from package: "+filename)
        tools[filename]=sha(package/filename)
    modules=[e for e in manifest["files"] if e.get("role")=="checked_proof_source"]
    for entry in modules:
        source=root/entry["path"]
        need(source.is_file() and sha(source)==entry["sha256"] and source.stat().st_size==entry["bytes"],
             "Checked source differs from supplied package: "+entry["module"])
    for relative in ("lean-toolchain","lake-manifest.json"):
        need(sha(root/relative)==sha(package/relative), "Checked dependency/toolchain identity differs")
    config=(root/"lakefile.toml").read_text(encoding="utf-8-sig")
    config,count=re.subn(r"^defaultTargets\s*=.*$",'defaultTargets = ["CurrentV42"]',config,flags=re.M)
    need(count==1 and config==(package/"lakefile.toml").read_text(encoding="utf-8-sig"),
         "Checked Lake configuration differs beyond default target; resource settings are not interchangeable")
    admission=OWNER+"ADMITTED_MODULES.json"
    need(sha(root/admission) in {original_digest(package,admission),sha(package/admission)},
         "Checked admission registry differs from source-bound package")
    inherited=unchanged_prior(package,manifest)
    snapshot=hashlib.sha256(json.dumps([(e["module"],e["sha256"],e["bytes"]) for e in sorted(modules,key=lambda e:e["module"])],
                                     separators=(",",":")).encode("utf-8")).hexdigest()
    result={"source_snapshot_sha256":snapshot,"source_module_count":len(modules),
        **inherited,"new_source_modules":len(modules)-inherited["unchanged_prior_source_modules"],
        "selected_source_lock_public_sha256":sha(package/"manuscript-v42/SOURCE_LOCK.json"),
        "verification_tool_sha256":tools,
        "prior_source_lock_identity_pins":[e for e in read(package/"manuscript-v42/SOURCE_LOCK.json").get("input_pins",[])
                                         if e["path"].split("/")[-1] in {"SOURCE_LOCK.json","SELECTED_SOURCE_LOCK.json"}]}
    print(json.dumps(result,indent=2))
    return result

def check_checked_receipt(package, receipt, evidence, published=False):
    need(receipt.get("status")=="passed" and receipt.get("verification_mode")=="canonical_checked_incremental" and
         receipt.get("project_build_initially_empty") is False and receipt.get("fresh_project_replay") is False,
         "Receipt does not truthfully identify an incremental checked build")
    need(receipt.get("source_manifest_sha256")==sha(package/"SOURCE_MANIFEST.json") and
         receipt.get("full_coverage_receipt_sha256")==sha(package/"FULL_COVERAGE_RECEIPT.json"), "Checked build binds another source/coverage package")
    commands=receipt.get("commands",[])
    need(len(commands)==3 and commands[0]["command"]==["lake","build","CurrentV42"] and
         all(r.get("exit_code")==0 for r in commands), "Missing/failed canonical CurrentV42 commands")
    for record,filename in zip(commands[1:],("AxiomAudit.lean","RawProofAudit.lean")):
        command=record["command"]
        need(len(command)==4 and command[:3]==["lake","env","lean"] and
             command[3].replace("\\","/").split("/")[-1]==filename and
             record.get("audit_source_sha256")==sha(package/filename), "Checked audit command/source differs")
    checks=receipt.get("checks",[])
    need([r["name"] for r in checks]==["source-before","providers","source-after"] and
         all(r.get("exit_code")==0 for r in checks), "Missing/failed complete identity/provider checks")
    need(receipt["source_before"]==receipt["source_after"], "Checked sources/provenance changed during build")
    need(receipt["source_before"].get("verification_tool_sha256")=={filename:sha(package/filename) for filename in
         ("checked_build.py","check_replay.py","release_common.py","verify_release.py")},
         "Checked receipt identifies different verification helper code")
    manifest=read(package/"SOURCE_MANIFEST.json")
    inherited=unchanged_prior(package,manifest)
    need(all(receipt["source_before"].get(k)==v for k,v in inherited.items()),
         "Checked receipt does not cover every unchanged prior module and exact prior identities")
    project={e["module"] for e in manifest["files"] if e.get("role")=="checked_proof_source"}
    need(receipt["source_before"]["source_module_count"]==len(project) and
         receipt.get("project_sources_cold_rebuilt") is False, "Invalid incremental source census")
    for record in commands+checks:
        log=evidence/Path(record["log"].replace("\\","/")).name
        expected=record.get("public_log_sha256",record["log_sha256"]) if published else record["log_sha256"]
        need(log.is_file() and sha(log)==expected, "Checked-build log identity mismatch")
    inventory=evidence/"PROVIDER_INVENTORY.json"
    expected=receipt.get("published_provider_inventory_sha256",receipt["provider_inventory_sha256"]) if published else receipt["provider_inventory_sha256"]
    need(inventory.is_file() and sha(inventory)==expected, "Checked provider/object inventory changed")
    objects=read(inventory)
    need(objects["project_modules"]==len(project) and
         {e["module"] for e in objects["providers"]}==project|set(manifest["external_modules"]) and
         all(re.fullmatch(r"[0-9a-f]{64}",e["olean_sha256"]) for e in objects["providers"]),
         "Incomplete checked object/provider inventory")
    prior=package/"archive/v40/SOURCE_MANIFEST.json"
    prior_receipt=package/"archive/v40/PUBLISHED_REPLAY.json"
    need(receipt["source_before"]["prior_public_source_manifest_sha256"]==sha(prior) and
         receipt["source_before"]["prior_public_fresh_replay_sha256"]==sha(prior_receipt), "Prior fresh-release provenance drift")
    if published:
        binding=read(package/"PUBLISHED_CHECKED_EVIDENCE_BINDING.json")
        for entry in binding["identity_bindings"]:
            check_pin(package,{"path":entry["release_path"],"sha256":entry["public_sha256"]})

def run(root, package, output):
    root,package,output=root.resolve(),package.resolve(),output.resolve()
    existing=root/".lake/build"
    need(existing.is_dir() and any(existing.rglob("*.olean")), "Checked incremental mode requires existing project objects; use replay.py for a fresh build")
    need(not output.exists(), "Checked-build output exists; use a new directory")
    for variable in ("LEAN_PATH","LEAN_SRC_PATH","LEAN_SYSROOT"):
        need(not os.environ.get(variable),"Unset "+variable+" for checked provider lookup")
    output.mkdir(parents=True)
    receipt={"schema_version":1,"status":"running","verification_mode":"canonical_checked_incremental",
        "fresh_project_replay":False,"project_build_initially_empty":False,"project_sources_cold_rebuilt":False,
        "scope":"Existing project objects reused; CurrentV42 build plus complete current effective/raw audits and exact source/provider/object/pin checks. Independently admitted new components retain their production-build evidence. No cold rebuild claim.",
        "source_manifest_sha256":sha(package/"SOURCE_MANIFEST.json"),
        "full_coverage_receipt_sha256":sha(package/"FULL_COVERAGE_RECEIPT.json"),
        "lake_artifact_cache":"disabled with LAKE_ARTIFACT_CACHE=false for build/audit subprocesses",
        "external_objects":"Pinned toolchain and package objects reused; not freshly rebuilt.",
        "started_utc":now(),"commands":[],"checks":[]}
    def save():write(output/"CHECKED_BUILD.json",receipt)
    def operation(name,function):
        log=output/(name+".log")
        record={"name":name,"operation":"source_match" if name.startswith("source-") else "complete_provider_object_pin_check",
                "log":log.name,"started_utc":now()}
        receipt["checks"].append(record);save()
        try:
            with log.open("w",encoding="utf-8") as target,contextlib.redirect_stdout(target):
                result=function()
            record["exit_code"]=0
            return result
        except BaseException:
            record["exit_code"]=1
            raise
        finally:
            record.update({"finished_utc":now(),"log_sha256":sha(log)});save()
    environment=os.environ.copy();environment["LAKE_ARTIFACT_CACHE"]="false"
    save()
    try:
        receipt["source_before"]=operation("source-before",lambda:source_match(root,package));save()
        commands=[("build",["lake","build","CurrentV42"]),
                  ("axiom-audit",["lake","env","lean",str(package/"AxiomAudit.lean")]),
                  ("raw-audit",["lake","env","lean",str(package/"RawProofAudit.lean")])]
        for name,command in commands:
            log=output/(name+".log")
            record={"command":command,"log":log.name,"started_utc":now()}
            if name!="build":record["audit_source_sha256"]=sha(Path(command[-1]))
            receipt["commands"].append(record);save()
            print("Running "+name,flush=True)
            with log.open("wb") as target:
                code=subprocess.call(command,cwd=root,env=environment,stdout=target,stderr=subprocess.STDOUT)
            record.update({"exit_code":code,"finished_utc":now(),"log_sha256":sha(log)});save()
            need(code==0,"Canonical command failed: "+name)
        operation("providers",lambda:check(root,output/"raw-audit.log",package/"SOURCE_MANIFEST.json",output/"PROVIDER_INVENTORY.json"))
        receipt["source_after"]=operation("source-after",lambda:source_match(root,package))
        receipt.update({"status":"passed","finished_utc":now(),"provider_inventory_sha256":sha(output/"PROVIDER_INVENTORY.json")})
        check_checked_receipt(package,receipt,output);save()
    except BaseException:
        receipt.update({"status":"failed","finished_utc":now()});save()
        raise
    print("Canonical incremental CurrentV42 build, complete audits and source/object/provider checks passed; no cold rebuild performed.")

if __name__=="__main__":
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("--root",type=Path,default=find_project_root())
    p.add_argument("--source-package",type=Path,default=ROOT)
    p.add_argument("--output",type=Path,required=True)
    args=p.parse_args()
    try:run(args.root,args.source_package,args.output)
    except (OSError,ValueError,KeyError) as error:raise SystemExit("FAIL: "+str(error))
