"""Portable release identity helpers; no proof or publication side effects."""
from pathlib import Path, PurePosixPath
import hashlib
import json

ROOT = Path(__file__).resolve().parent
ACCEPTED = {"verified_correspondence", "external_input", "definition_correspondence"}
PAPER_PREFIX = "papers/randomized-additive-hardness/versions/v42/"
OWNER = "papers/randomized-additive-hardness/formalization/current-v42/"
LIBRARIES = {
    "Workspace": "vendor/npc-cc", "NPCC": "vendor/npc-cc", "EthBridge": "vendor/npc-cc",
    "LegacyNPCC": "src", "EthInapproximability": "src",
    "Paper2": "papers/randomized-additive-hardness/formalization/lean",
    "CurrentAdditive": "papers/randomized-additive-hardness/formalization/current-v27/lean",
    "CurrentV42": "papers/randomized-additive-hardness/formalization/current-v42/lean",
}

def need(condition, message):
    if not condition:
        raise ValueError(message)

def safe(root, relative):
    need(isinstance(relative, str) and "\\" not in relative, f"Non-portable path: {relative}")
    p = PurePosixPath(relative)
    need(not p.is_absolute() and all(x not in {"", ".", ".."} for x in p.parts)
         and ":" not in relative, f"Invalid relative path: {relative}")
    path = root.joinpath(*p.parts)
    need(path.resolve().is_relative_to(root.resolve()), f"Path escapes package: {relative}")
    need(not path.is_symlink(), f"Symlink not admitted: {relative}")
    return path

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def find_project_root(start=ROOT):
    """Locate the checked Lake root without assuming scratch/durable depth."""
    for path in (start,*start.parents):
        if (path/"lakefile.toml").is_file() and (path/"lean-toolchain").is_file():
            return path
    raise ValueError("Pass --root explicitly; no containing Lake project was found")

def read(path):
    return json.loads(path.read_text(encoding="utf-8-sig"))

def write(path, value):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, indent=2, ensure_ascii=False)+"\n", encoding="utf-8")

def pin(root, relative, **extra):
    path = safe(root, relative)
    return {"path": relative, "sha256": sha(path), "bytes": path.stat().st_size, **extra}

def module_path(module):
    base = LIBRARIES.get(module.split(".")[0])
    return base+"/"+module.replace(".", "/")+".lean" if base else None

def check_pin(root, item):
    path = safe(root, item["path"])
    need(path.is_file(), "Missing file: "+item["path"])
    need(sha(path) == item["sha256"].lower(), "Hash mismatch: "+item["path"])
    if "bytes" in item:
        need(path.stat().st_size == item["bytes"], "Size mismatch: "+item["path"])
    return path

def binding_path(relative):
    """Translate only the manuscript namespace; Lean source paths stay exact."""
    return "manuscript-v42/"+relative[len(PAPER_PREFIX):] if relative.startswith(PAPER_PREFIX) else relative

def original_digest(root, relative):
    """Original private identity, distinct from projected public byte identity."""
    binding = read(root/"RELEASE_BINDING.json")
    matches = [b for b in binding["identity_bindings"] if b["release_path"] == relative]
    return matches[0]["sha256"] if matches else sha(root/relative)

def check_coverage(root, manifest):
    coverage = read(root/"manuscript-v42/V42_STATEMENT_MAP.json")
    source = root/"manuscript-v42/source/main.tex"
    need(coverage.get("version") == "v42" and coverage.get("source_sha256") == sha(source),
         "Coverage is bound to a different source")
    rows = coverage["blocks"]+coverage["unnumbered_requirements"]
    need(rows and len({r["id"] for r in rows}) == len(rows), "Empty or duplicate coverage rows")
    inventory = read(root/"manuscript-v42/SELECTED_STATEMENTS.v42.json")
    need(inventory["source_sha256"] == sha(source), "Stale source-statement inventory")
    blocks = sorted(inventory["formal_blocks"]+inventory["auxiliary_blocks"], key=lambda b:b["line"])
    need([b["id"] for b in blocks] == [b["id"] for b in coverage["blocks"]], "Map omits/reorders inventoried source blocks")
    for block, row in zip(blocks, coverage["blocks"]):
        need(all(row.get(k) == v for k,v in block.items()), "Changed source block in correspondence map: "+block["id"])
    lock = read(root/"manuscript-v42/SOURCE_LOCK.json")
    need(lock["source"]["sha256"] == sha(source) and lock.get("pdf_bound") and
         lock.get("manuscript_manifest_bound"), "Source/PDF/manifest lock is incomplete")
    need(all(r["status"] in ACCEPTED for r in rows), "Pending/unmapped manuscript obligations")
    need(coverage.get("correspondence_complete") is True,
         "Coverage global completion flag is stale; freeze it only after all independent rows close")
    project = {e["path"]: e for e in manifest["files"] if e.get("role") == "checked_proof_source"}
    bindings = read(root/"RELEASE_BINDING.json")["identity_bindings"]
    mapped = {e["original_path"]: e for e in bindings}
    authority_cache = {}
    def evidence_path(item):
        b = mapped.get(item["path"])
        need(b and b["sha256"] == item["sha256"], "Evidence binding missing/changed: "+item["path"])
        return check_pin(root, {"path": b["release_path"], "sha256": b.get("public_sha256", b["sha256"])})
    for row in rows:
        need(row.get("review_evidence"), "Missing independent review: "+row["id"])
        for evidence in row["review_evidence"]:
            evidence_path(evidence)
        if row["status"] != "external_input":
            need(row.get("accepted_declarations"), "Accepted row lacks declarations: "+row["id"])
        for decl in row.get("accepted_declarations", []):
            entry = project.get(decl["source"])
            need(entry and entry["sha256"] == decl["source_sha256"],
                 "Accepted declaration outside exact release closure: "+decl["name"])
            lines = safe(root, decl["source"]).read_text(encoding="utf-8-sig").splitlines()
            line = decl["line"]
            need(isinstance(line, int) and 0 < line <= len(lines) and
                 lines[line-1].strip() == decl["declaration_text"].strip(),
                 "Changed declaration anchor: "+decl["name"])
            authority = decl.get("build_authority")
            need(authority, "Accepted declaration lacks imported-build authority: "+decl["name"])
            key = authority["manifest"]["sha256"]+":"+authority["receipt"]["sha256"]
            if key not in authority_cache:
                build_manifest = read(evidence_path(authority["manifest"]))
                receipt = read(evidence_path(authority["receipt"]))
                need(receipt.get("source_manifest_sha256", "").lower() == authority["manifest"]["sha256"],
                     "Imported build receipt does not bind its source manifest")
                commands = receipt.get("commands", receipt.get("gates", []))
                target = "CurrentV42" if authority["kind"] == "current_v42_build" else "CurrentAdditive"
                command_text = json.dumps(commands)
                need(receipt.get("status") in (None, "passed") and commands and
                     all(c.get("exit_code") == 0 for c in commands) and
                     target in command_text and "AxiomAudit" in command_text,
                     "Missing/failed target build and axiom receipt")
                records = build_manifest.get("modules", build_manifest.get("files", []))
                authority_cache[key] = {e.get("path", e.get("source")):e for e in records
                                        if e.get("role", "checked_proof_source") == "checked_proof_source"}
                for relative, prior_source in authority_cache[key].items():
                    current_source = project.get(relative)
                    need(current_source and current_source["sha256"] == prior_source["sha256"].lower() and
                         ("bytes" not in prior_source or current_source["bytes"] == prior_source["bytes"]),
                         "Imported proof dependency drift since recorded authority: "+str(relative))
            prior = authority_cache[key].get(decl["source"])
            need(prior and prior["sha256"].lower() == decl["source_sha256"],
                 "Accepted source outside recorded imported build: "+decl["name"])
    inspector_path = root/"manuscript-v42/INSPECTOR_STATEMENTS.json"
    need(inspector_path.is_file(), "Missing final inspector statement data")
    inspector = read(inspector_path)
    pdf = root/"manuscript-v42/output/INTERLACING_AND_ADDITIVE_INAPPROXIMABILITY_v42.pdf"
    need(lock["pdf"]["sha256"] == sha(pdf), "Source lock PDF identity changed")
    paper_manifest = read(root/"manuscript-v42/MANIFEST.json")
    for item in paper_manifest["sources"]:
        check_pin(root/"manuscript-v42", item)
    check_pin(root/"manuscript-v42", paper_manifest["output"])
    need(inspector["paper"]["source_sha256"] == sha(source) and inspector["paper"]["pdf_sha256"] == sha(pdf),
         "Stale inspector manuscript identity")
    need([s["id"] for s in inspector["statements"]] == [r["id"] for r in rows],
         "Inspector omits/reorders source or construction obligations")
    statuses = {"verified_correspondence":"verified", "external_input":"external", "definition_correspondence":"definition"}
    for row, node in zip(rows, inspector["statements"]):
        status = statuses[row["status"]]
        need(node["status"] == status and all(d["status"] == status for d in node["lean"]),
             "Stale inspector proof status: "+row["id"])
        need([d["name"] for d in node["lean"]] == [d["name"] for d in row.get("accepted_declarations", [])],
             "Inspector substitutes historical candidate declarations: "+row["id"])
    return {"source_blocks": len(coverage["blocks"]), "unnumbered_requirements": len(coverage["unnumbered_requirements"])}
