"""Verify exact package/source identities and closed source-correspondence links.

This is not a Lean build. Current compilation/audits and provider checks are
separate gates, recorded by checked_build.py or the optional cold replay.py.
"""
from collections import Counter
import argparse
from release_common import (ROOT, LIBRARIES, check_coverage, check_pin, module_path,
                            need, original_digest, read, sha)

def verify(root=ROOT):
    manifest = read(root/"SOURCE_MANIFEST.json")
    need(manifest.get("schema_version") == 2 and manifest.get("target") == "CurrentV42", "Wrong release manifest")
    entries = manifest["files"]
    need(len({e["path"] for e in entries}) == len(entries), "Duplicate manifest path")
    need(len({e["path"].casefold() for e in entries}) == len(entries), "Case-colliding manifest paths")
    for entry in entries:
        check_pin(root, entry)
    project = [e for e in entries if e.get("role") == "checked_proof_source"]
    need(len({e["module"] for e in project}) == len(project), "Duplicate project module")
    need(all(module_path(e["module"]) == e["path"] for e in project), "Unexpected local source path")
    counts = dict(Counter(e["module"].split(".")[0] for e in project))
    need(counts == manifest["project_module_counts"] and len(project) == manifest["project_module_count"],
         "Project module count mismatch")
    actual = {p.relative_to(root).as_posix() for base in set(LIBRARIES.values())
              for p in (root/base).rglob("*.lean")}
    need(actual == {e["path"] for e in project}, "Unexpected/missing local Lean source")
    need(len(set(manifest["external_modules"])) == manifest["external_module_count"] and
         set(manifest["external_providers"]) == set(manifest["external_modules"]), "External provider census mismatch")
    admitted = read(root/"papers/randomized-additive-hardness/formalization/current-v42/ADMITTED_MODULES.json")["modules"]
    new = {e["module"]: e for e in project if e["module"].startswith("CurrentAdditive.V42")}
    need(set(new) == {e["module"] for e in admitted}, "Unadmitted/missing current-source proof module")
    bindings = {b["original_path"]: b for b in read(root/"RELEASE_BINDING.json")["identity_bindings"]}
    for item in admitted:
        need(new[item["module"]]["sha256"] == item["sha256"], "Admission source identity mismatch")
        b = bindings.get(item["review"])
        need(b and b["sha256"] == item["review_sha256"], "Missing admission review binding")
        check_pin(root, {"path": b["release_path"], "sha256": b.get("public_sha256", b["sha256"])})
    gate = read(root/"FULL_COVERAGE_RECEIPT.json")
    need(gate.get("status") == "passed" and gate.get("correspondence_complete") is True and
         gate.get("unresolved_obligations") == [], "Full-coverage gate has not passed")
    expected = {"source_sha256": sha(root/"manuscript-v42/source/main.tex"),
                "coverage_sha256": original_digest(root, "manuscript-v42/V42_STATEMENT_MAP.json"),
                "admitted_manifest_sha256": original_digest(root, "papers/randomized-additive-hardness/formalization/current-v42/ADMITTED_MODULES.json"),
                "aggregate_sha256": sha(root/"papers/randomized-additive-hardness/formalization/current-v42/lean/CurrentV42.lean")}
    need(all(gate.get(k) == v for k,v in expected.items()), "Stale full-coverage gate")
    required = {"inventory_complete", "source_correspondence", "declaration_anchors", "independent_review"}
    need(required <= {c["name"] for c in gate["checks"]}, "Missing full-coverage checks")
    for c in gate["checks"]:
        need(c.get("exit_code") == 0 and c.get("evidence"), "Failed/missing coverage gate evidence")
        for evidence in c["evidence"]:
            b = bindings.get(evidence["path"])
            need(b and b["sha256"] == evidence["sha256"], "Unbound coverage-gate evidence")
            check_pin(root, {"path": b["release_path"], "sha256": b.get("public_sha256", b["sha256"])})
    result = check_coverage(root, manifest)
    published = root/"PUBLISHED_REPLAY.json"
    status = read(root/"release-status.json")
    need(status.get("v42_correspondence_checked") is True, "Release status does not identify the passed source-bound coverage gate")
    need(status.get("full_coverage_receipt_sha256") == sha(root/"FULL_COVERAGE_RECEIPT.json"),
         "Release status binds stale full-coverage evidence")
    if status.get("source_manifest_sha256"):
        need(status["source_manifest_sha256"] == sha(root/"SOURCE_MANIFEST.json"), "Release status binds a stale source manifest")
    if status.get("public_package_replay_complete"):
        need(published.is_file(), "Release reports completed replay without accepted replay evidence")
        need(status["public_package_replay"]["receipt_sha256"] == sha(published), "Release reports a different replay receipt")
    if published.exists():
        from check_replay import check_receipt
        check_receipt(root, read(published), published=True)
    checked=root/"PUBLISHED_CHECKED_BUILD.json"
    if status.get("canonical_checked_build_complete"):
        need(checked.is_file() and status["canonical_checked_build"]["receipt_sha256"]==sha(checked),
             "Release reports canonical checked build without matching evidence")
    if checked.exists():
        from checked_build import check_checked_receipt
        check_checked_receipt(root,read(checked),root/"published-checked-build-logs",published=True)
    print(f"Verified {len(entries)} identity-pinned files, {len(project)} exact local modules, and {result}.")
    print("Source identity and recorded correspondence do not replace the separately recorded build/audits or establish external source-interface fidelity.")
    return manifest

if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    args = parser.parse_args()
    try:
        verify()
    except (ValueError, OSError, KeyError) as error:
        raise SystemExit("FAIL: "+str(error))
