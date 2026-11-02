"""Explicit path-only public projections of provenance, never proof sources.

Original bytes/hashes are retained in the private preparation archive. Public
hashes identify the projected bytes and must never be compared with the original
hashes as if the projection were byte-identical. Review conclusions, proof-source
hashes, executables/options, exit codes and mathematical text are not rewritten;
command path arguments can be mapped to explicitly labelled provenance IDs.
"""
from pathlib import Path
import hashlib
import json
import re
from release_common import ROOT, need, sha, write

POLICY = ("Path-only public projection. Original private bytes are archived locally by SHA256; "
          "original hashes are historical identity references, not hashes of projected public bytes. "
          "Review conclusions, proof-source hashes, executables/options and exit codes are retained; path arguments are mapped. "
          "Current public SOURCE_MANIFEST plus its canonical checked-build or optional fresh-replay receipt supplies the distinct portable build evidence.")
ABSOLUTE_PATH_START = re.compile(r"^(?:[A-Za-z]:[\\/]|/(?:home|Users|private|tmp)/)")
# A bare `A:\Gamma` can be mathematical TeX. Scan prose for machine-directory
# prefixes; structured path fields/code targets use the generic start test.
ABSOLUTE = re.compile(r"(?<![A-Za-z0-9])(?:[A-Za-z]:[\\/]+(?:Users|lean|My Drive|Documents|AppData|Program Files|Windows|Projects|repos|tmp|temp)[\\/]+|/(?:home|Users|private|tmp)/)", re.I)
SECRETS = {
    "private_key": re.compile(r"-----BEGIN (?:RSA |EC |OPENSSH )?PRIVATE KEY-----"),
    "github_token": re.compile(r"\b(?:gh[pousr]_[A-Za-z0-9]{30,}|github_pat_[A-Za-z0-9_]{30,})\b"),
    "api_key": re.compile(r"\bsk-(?:proj-|svcacct-)?[A-Za-z0-9_-]{30,}\b"),
    "browser_session_data": re.compile(r'"(?:access_token|refresh_token|storage_state|cookies)"\s*:'),
}
PATH_KEYS = {"path", "source", "file", "log", "root", "cwd", "provider", "project_root",
             "authoritative_attachment", "authorized_source_update_comparison", "prior_source_lock_preserved"}

def digest_bytes(data):
    return hashlib.sha256(data).hexdigest()

def suitability(text):
    findings = []
    for index, line in enumerate(text.splitlines(), 1):
        if ABSOLUTE.search(line):
            findings.append({"line": index, "category": "absolute_machine_path"})
        for label, expression in SECRETS.items():
            if expression.search(line):
                findings.append({"line": index, "category": label})
    return findings

class Projector:
    def __init__(self, checkout, archive=ROOT/"private-evidence-archive"):
        self.checkout = Path(checkout).resolve()
        self.archive = Path(archive)
        self.known = {}
        self.entries = []
        self.unpublished = {}

    def register(self, original, source, destination, role="evidence", preserve_namespace=False):
        source = Path(source)
        item = {"original_path": original, "source":source, "release_path":destination,
                "sha256":sha(source), "bytes":source.stat().st_size, "role":role,
                "reference_id": original if preserve_namespace else destination}
        self.entries.append(item)
        self.known[original.replace("\\", "/")] = item["reference_id"]
        self.known[str(source.resolve()).replace("\\", "/")] = item["reference_id"]
        return item

    def reference(self, value, force_path=False):
        normalized = value.replace("\\", "/")
        if normalized in self.known:
            return self.known[normalized]
        checkout = self.checkout.as_posix()+"/"
        if normalized.startswith(checkout):
            normalized = normalized[len(checkout):]
            if normalized in self.known:
                return self.known[normalized]
        # Lean and manuscript references retain the development-root namespace.
        # RELEASE_BINDING alone translates the physical manuscript location.
        if normalized.startswith(("papers/", "src/", "vendor/")):
            return normalized
        if (ABSOLUTE.match(normalized) or (force_path and ABSOLUTE_PATH_START.match(normalized)) or
            normalized.startswith(("scratch/", ".codex/"))):
            identity = digest_bytes(value.encode("utf-8"))
            basename = normalized.rstrip("/").split("/")[-1] or "directory"
            basename = re.sub(r"[^A-Za-z0-9_.-]", "_", basename)
            public_id = "private-provenance-refs/"+identity+"/"+basename
            self.unpublished[public_id] = {"evidence_id":public_id,
                "original_path_sha256":identity,
                "status":"Original private path omitted; this reference does not assert public availability."}
            return public_id
        return value

    def command(self, text):
        # Known full roots may include spaces. Replace them before tokenization.
        variants = [(str(self.checkout), ""), (self.checkout.as_posix(), "")]
        for prefix, replacement in variants:
            text = text.replace(prefix+"\\", replacement).replace(prefix+"/", replacement)
        text = re.sub(r"(\|)([A-Za-z]:[\\/][^\r\n]*)", lambda m:m.group(1)+self.reference(m.group(2)), text)
        # Quoted paths and command arguments only; flags and mathematical text
        # outside these structured command fields are untouched.
        tokens = re.compile(r'"([^"\r\n]+)"|\x27([^\x27\r\n]+)\x27|([^\s]+)')
        def substitute(match):
            quoted = match.group(1) if match.group(1) is not None else match.group(2)
            token = quoted if quoted is not None else match.group(3)
            mapped = token if token.startswith("build-logs/") else self.reference(token,force_path=True)
            if quoted is not None:
                quote = '"' if match.group(1) is not None else "'"
                return quote+mapped+quote
            return mapped
        return tokens.sub(substitute, text)

    def json_value(self, value, key=""):
        if isinstance(value, dict):
            result = {}
            for k,v in value.items():
                public_key = self.reference(k,force_path=True) if ABSOLUTE.match(k) or k.startswith(("scratch/", ".codex/")) else k
                need(public_key not in result, "Path projection would collide JSON keys")
                result[public_key] = self.json_value(v, k)
            return result
        if isinstance(value, list):
            return [self.json_value(v, key) for v in value]
        if not isinstance(value, str):
            return value
        if key in {"command", "commands", "compiler_flags", "compile_command"}:
            return self.command(value)
        # Exact registered references are always paths, even in input lists.
        if value.replace("\\", "/") in self.known:
            return self.reference(value)
        if key in PATH_KEYS or key.endswith(("_path", "_file", "_log", "_directory")):
            return self.reference(value,force_path=True)
        if ABSOLUTE.match(value) or value.startswith(("scratch/", ".codex/")):
            return self.reference(value)
        return value

    def markdown(self, text):
        # Only link targets, inline code path/command spans, and compiler-command
        # lines in fenced blocks are changed. Surrounding prose is untouched.
        text = re.sub(r"(\]\()(<[^>]*>|[^)\r\n]+)(\))", lambda m:m.group(1)+
                      ("<"+self.reference(m.group(2)[1:-1],force_path=True)+">" if m.group(2).startswith("<")
                       else self.reference(m.group(2),force_path=True))+m.group(3), text)
        lines = []
        fenced = False
        for line in text.splitlines(keepends=True):
            if line.lstrip().startswith("```"):
                fenced = not fenced
                lines.append(line)
                continue
            if fenced:
                if line.lstrip().startswith(("lake ", "lean ", "python ", "git ", "& ", "pwsh ", "powershell ")):
                    line = self.command(line)
            else:
                line = re.sub(r"`([^`\r\n]+)`", lambda m:"`"+
                              (self.command(m.group(1)) if m.group(1).startswith(("lake ","lean ","python ","git "))
                               else self.reference(m.group(1)))+"`", line)
            lines.append(line)
        return "".join(lines)

    def project_bytes(self, source):
        source = Path(source)
        data = source.read_bytes()
        suffix = source.suffix.lower()
        if suffix == ".json":
            original = json.loads(data.decode("utf-8-sig"))
            result = self.json_value(original)
            public = data if result == original else (json.dumps(result, indent=2, ensure_ascii=False)+"\n").encode("utf-8")
        elif suffix in {".md", ".txt", ".log"}:
            text = data.decode("utf-8-sig")
            if suffix == ".md":
                text = self.markdown(text)
            else:
                # Plain logs are command/provider records; keep every line and
                # conclusion, mapping only explicit path tokens. No filtering.
                text = "".join(self.command(line) for line in text.splitlines(keepends=True))
            public = text.encode("utf-8")
        else:
            public = data
        findings = suitability(public.decode("utf-8", errors="replace"))
        need(not findings, f"Public suitability rejection in {source.name}: {findings[:5]}; original bytes retained privately")
        return public

    def archive_original(self, item):
        target = self.archive/item["sha256"]/item["source"].name
        target.parent.mkdir(parents=True, exist_ok=True)
        original = item["source"].read_bytes()
        if target.exists():
            need(target.read_bytes() == original, "Private archive identity collision")
        else:
            target.write_bytes(original)

    def emit(self, output):
        bindings = []
        for item in self.entries:
            self.archive_original(item)
            data = self.project_bytes(item["source"])
            destination = Path(output)/item["release_path"]
            destination.parent.mkdir(parents=True, exist_ok=True)
            destination.write_bytes(data)
            # Public references use the stable repository-relative evidence ID.
            # The original local path is intentionally absent from this record.
            bindings.append({"original_path":item["reference_id"],
                "evidence_id":item["reference_id"], "release_path":item["release_path"],
                "sha256":item["sha256"], "original_bytes":item["bytes"],
                "public_sha256":digest_bytes(data), "public_bytes":len(data),
                "projection":"identity" if data == item["source"].read_bytes() else "path_only_public_projection",
                "original_path_sha256":digest_bytes(item["original_path"].encode("utf-8"))})
        index = {"schema_version":2, "policy":POLICY,
                 "identity_bindings":bindings,
                 "unpublished_private_path_references":list(self.unpublished.values())}
        private_index = {"policy":"Private originals only; never copy this directory into the public package.",
                         "files":[{k:str(v) if isinstance(v,Path) else v for k,v in e.items()} for e in self.entries]}
        index_identity=digest_bytes(json.dumps(private_index,sort_keys=True).encode("utf-8"))
        write(self.archive/("PRIVATE_INDEX."+index_identity+".json"), private_index)
        write(self.archive/"PRIVATE_INDEX.json", private_index)
        return index
