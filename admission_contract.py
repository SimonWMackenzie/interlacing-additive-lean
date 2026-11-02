"""Check exact new-source admissions relative to an immutable v42 closure."""


def check_delta(previous, current, admissions):
    def need(ok, message):
        if not ok:
            raise ValueError(message)
    need(previous.get("target") == "CurrentV42", "Prior manifest must identify CurrentV42")
    prior = [e for e in previous["files"] if e.get("role") == "checked_proof_source"]
    need(prior and len({e["module"] for e in prior}) == len(prior), "Empty/duplicate inherited closure")
    need(len({e["module"] for e in current}) == len(current), "Duplicate current source module")
    observed = {e["module"]: e for e in current}
    for entry in prior:
        item = observed.get(entry["module"])
        need(item is not None and all(item.get(k) == entry.get(k) for k in ("path", "sha256", "bytes")),
             "Inherited v42 proof source changed or left closure: " + entry["module"])
    need("CurrentV43" in observed, "Missing new CurrentV43 aggregate")
    new = set(observed) - {e["module"] for e in prior} - {"CurrentV43"}
    need(new, "Empty v43 runtime proof supplement")
    need(len({e["module"] for e in admissions}) == len(admissions), "Duplicate new admission")
    need(new == {e["module"] for e in admissions}, "Unadmitted/missing new source proof module")
    for admission in admissions:
        item = observed[admission["module"]]
        need(item["path"] == admission["source"] and item["sha256"] == admission["sha256"],
             "Admission source identity mismatch: " + admission["module"])
        need(admission.get("review") and admission.get("review_sha256"), "New module lacks independent review binding")
    return {m: observed[m] for m in new}
