"""Build and validate the Version 6 source-application inventory.

This checks document identity, explicit citation coverage, references and
per-span inheritance. It does not decide the truth of mathematical proofs.
All paths are repository-relative. Old inventories are read, never edited.
"""
import argparse
import bisect
import hashlib
import json
import re
from pathlib import Path

HERE = Path(__file__).resolve().parent
DEFAULT_REPO = HERE.parents[1]
OLD_TEX = "quartic_4973.tex"
BASE = "docs/theorem-application-audit/"
V4 = "docs/quartic-4973/"
V5 = "docs/quartic-1272/"
V5_TEX = "quartic_1272.tex"
NEW = "docs/quartic-962/"
REGISTER_SCHEMA = "quartic-v6-authored-applications-v1"
DERIVED = ["theorem-applications.json", "inherited-bridge.json", "citations.json",
           "internal-results.json", "bibliography.json", "dependency-graph.json", "coverage.json"]
ENVIRONMENTS = {"theorem", "proposition", "lemma", "corollary", "definition", "remark",
                "assumption", "hypothesis"}
CITE_RE = re.compile(r"\\cite(?:[a-zA-Z]*\*?)\s*(?:\[([^\]]*)\]\s*)?(?:\[([^\]]*)\]\s*)?\{([^{}]+)\}")
REF_RE = re.compile(r"\\(?:eqref|ref|autoref|cref|Cref)\*?\s*\{([^{}]+)\}")
LABEL_RE = re.compile(r"\\label\s*\{([^{}]+)\}")


def fail(condition, message):
    if not condition:
        raise ValueError(message)


def digest(data):
    return hashlib.sha256(data).hexdigest()


def encoded(data):
    return (json.dumps(data, indent=2, ensure_ascii=False, sort_keys=True) + "\n").encode("utf-8")


def read(repo, path):
    # Historical acceptance records retain their original logical paths.
    # File relocation does not change any accepted manuscript byte or hash.
    if path in {'quartic_12504.tex', 'quartic_9625.tex', 'quartic_4973.tex', 'quartic_1272.tex'} and not (repo / path).exists():
        path = 'manuscripts/archive/' + path
    if path == 'manuscripts/quartic_v7.tex' and not (repo / path).exists():
        path = 'manuscripts/archive/quartic_v7.tex'
    target = (repo / path).resolve()
    fail(target.is_relative_to(repo.resolve()), "Path escapes repository: " + path)
    return target.read_bytes()


def load(repo, path):
    return json.loads(read(repo, path).decode("utf-8-sig"))


def pin(repo, path):
    raw = read(repo, path)
    return {"path": path, "bytes": len(raw), "sha256": digest(raw)}


def verify_pin(repo, spec, context):
    actual = pin(repo, spec["path"])
    fail(actual["sha256"] == spec["sha256"], context + ": " + spec["path"])
    if "bytes" in spec:
        fail(actual["bytes"] == spec["bytes"], context + " byte count: " + spec["path"])
    return actual


def json_pointer(value, pointer):
    fail(isinstance(pointer, str) and pointer.startswith("/"), "Expected JSON pointer")
    for item in pointer[1:].split("/"):
        item = item.replace("~1", "/").replace("~0", "~")
        try:
            value = value[int(item)] if isinstance(value, list) else value[item]
        except (KeyError, IndexError, ValueError, TypeError) as exc:
            raise ValueError("Unresolved review JSON pointer: " + pointer) from exc
    return value


def validate_predecessor(repo, register):
    required = [V5_TEX, V5 + "theorem-applications.json", V5 + "new-applications.json",
                V5 + "coverage.json"]
    specs = register.get("predecessor_v5", [])
    fail(len({s["path"] for s in specs}) == len(specs), "Duplicate V5 predecessor pin")
    fail(set(required).issubset({s["path"] for s in specs}), "Missing explicit V5 predecessor pins")
    pins = [verify_pin(repo, s, "V5 predecessor changed") for s in specs]
    inv = load(repo, V5 + "theorem-applications.json")
    coverage = load(repo, V5 + "coverage.json")
    fail(coverage.get("status") == "PASS_DOCUMENT_BINDING", "V5 predecessor inventory is not closed")
    for spec in inv.get("input_pins", []) + [inv["manuscript"], coverage["manuscript"]]:
        pins.append(verify_pin(repo, spec, "V5 accepted input changed"))
    return Tex(read(repo, V5_TEX), V5_TEX), inv, pins


def bind_fragment_provenance(repo, spec, fragment, predecessor, inv5, evidence):
    provenance = spec.get("provenance", {})
    kind = provenance.get("kind")
    if kind == "exact_predecessor_span":
        location = provenance["span"]
        fail(location["path"] == V5_TEX, "Fragment predecessor path differs: " + spec["id"])
        start, end = location["start_character"], location["end_character"]
        fail(0 <= start < end <= len(predecessor.text), "Invalid predecessor span: " + spec["id"])
        excerpt = predecessor.text[start:end]
        fail(digest(excerpt.encode()) == location["text_sha256"], "Predecessor span hash differs: " + spec["id"])
        fail(excerpt.strip() == fragment, "Inherited fragment text changed: " + spec["id"])
        accepted = [f["current"] for f in inv5.get("reviewed_fragments", [])]
        fail(any(s["start_character"] <= start < end <= s["end_character"] for s in accepted),
             "Predecessor fragment is outside accepted V5 review: " + spec["id"])
    elif kind == "reviewed":
        path = provenance.get("receipt_path")
        fail(path in evidence, "Fragment review receipt is not pinned: " + spec["id"])
        receipt = load(repo, path)
        fail(json_pointer(receipt, provenance["sha256_pointer"]) == spec["sha256"],
             "Review receipt does not accept exact fragment bytes: " + spec["id"])
        fail(provenance.get("accepted_status") is not None, "Missing accepted review status: " + spec["id"])
        fail(json_pointer(receipt, provenance["status_pointer"]) == provenance["accepted_status"],
             "Review receipt status differs: " + spec["id"])
    else:
        fail(False, "Missing recognized fragment provenance: " + spec["id"])


def predecessor_dispositions(inv5, register):
    old = {a["id"]: a for a in inv5.get("new_applications", [])}
    active = {a["id"] for a in register.get("applications", [])}
    inherited = register.get("inherit_v5_applications", [])
    retired = register.get("retired_applications", [])
    retired_ids = [a["id"] for a in retired]
    fail(len(inherited) == len(set(inherited)), "Duplicate inherited V5 application")
    fail(len(retired_ids) == len(set(retired_ids)), "Duplicate retired application")
    fail(set(inherited).issubset(old), "Unknown inherited V5 application")
    fail(set(retired_ids).issubset(old), "Unknown retired V5 application")
    fail(not (set(inherited) & active or set(retired_ids) & active or set(inherited) & set(retired_ids)),
         "Conflicting V5 application dispositions")
    fail(set(old).issubset(active | set(inherited) | set(retired_ids)),
         "V5 application lacks explicit disposition: " + ", ".join(sorted(set(old) - active - set(inherited) - set(retired_ids))))
    for rec in retired:
        fail(bool(rec.get("reason")), "Retired application lacks reason: " + rec["id"])
        fail(rec.get("replacement_ids") or rec.get("not_consumed") is True,
             "Retired application lacks replacement or not_consumed: " + rec["id"])
        fail(set(rec.get("replacement_ids", [])).issubset(active | set(inherited)),
             "Retired application names unknown replacement: " + rec["id"])
    fail("V5-SUN-FT-LINEAR" not in active | set(inherited), "Version 6 cannot retain FT as an assumed theorem")
    fail("V5-SUN-DK-RELATIVE-INVERSE" not in active | set(inherited),
         "Version 6 DK application must be separately reviewed under a new ID")
    return old, retired


def tex_text(raw):
    return raw.decode("utf-8-sig").replace("\r\n", "\n")


def uncomment(text):
    # Preserve offsets and line numbers. A percent preceded by an odd number
    # of backslashes is escaped. All other percent signs start a TeX comment.
    out = list(text)
    for m in re.finditer("%", text):
        j = m.start() - 1
        while j >= 0 and text[j] == "\\":
            j -= 1
        if (m.start() - 1 - j) % 2:
            continue
        end = text.find("\n", m.start())
        if end < 0:
            end = len(text)
        out[m.start():end] = " " * (end - m.start())
    return "".join(out)


class Tex:
    def __init__(self, raw, path):
        self.raw = raw
        self.text = tex_text(raw)
        self.code = uncomment(self.text)
        self.path = path
        self.starts = [0] + [m.end() for m in re.finditer("\n", self.text)]
        self.labels = {}
        for m in LABEL_RE.finditer(self.code):
            fail(m.group(1) not in self.labels, "Duplicate TeX label: " + m.group(1))
            self.labels[m.group(1)] = m.start()
        self.results = self.parse_results()
        self.sections = []
        for m in re.finditer(r"\\(section|subsection|subsubsection|paragraph)\*?\s*\{", self.code):
            self.sections.append((m.start(), m.group(1)))

    def span(self, start, end):
        return {"path": self.path, "start_character": start, "end_character": end,
                "first_line": bisect.bisect_right(self.starts, start),
                "last_line": bisect.bisect_right(self.starts, max(start, end - 1)),
                "text_sha256": digest(self.text[start:end].encode())}

    def paragraph(self, position):
        begin = self.text.rfind("\n\n", 0, position) + 2
        if begin == 1:
            begin = 0
        end = self.text.find("\n\n", position)
        if end < 0:
            end = len(self.text)
        return begin, end

    def enclosing(self, position):
        result = [r for r in self.results if r["start"] <= position < r["end"]]
        return min(result, key=lambda r: r["end"] - r["start"]) if result else None

    def label_span(self, label):
        fail(label in self.labels, "Missing label " + label)
        pos = self.labels[label]
        result = self.enclosing(pos)
        if result:
            return result["start"], result["end"]
        # Non-result labels receive an exact paragraph anchor, not an inferred
        # theorem-sized range. Authors can register larger explicit snippets.
        return self.paragraph(pos)

    def section_span(self, label):
        fail(label in self.labels, "Missing section label " + label)
        pos = self.labels[label]
        earlier = [(p, k) for p, k in self.sections if p <= pos]
        fail(earlier, "No section command for " + label)
        start, kind = earlier[-1]
        ranks = {"section": 1, "subsection": 2, "subsubsection": 3, "paragraph": 4}
        later = [p for p, k in self.sections if p > start and ranks[k] <= ranks[kind]]
        end = later[0] if later else self.code.find(r"\begin{thebibliography}", pos)
        if end < 0:
            end = len(self.text)
        return start, end

    def parse_results(self):
        token = re.compile(r"\\(begin|end)\{(" + "|".join(sorted(ENVIRONMENTS | {"proof"})) + r")\}")
        stack, envs = [], []
        for m in token.finditer(self.code):
            if m.group(1) == "begin":
                stack.append((m.group(2), m.start()))
            else:
                fail(stack and stack[-1][0] == m.group(2), "Unbalanced result environment at " + str(m.start()))
                name, start = stack.pop()
                envs.append({"environment": name, "start": start, "end": m.end()})
        fail(not stack, "Unclosed result environment")
        envs.sort(key=lambda r: r["start"])
        results = []
        for i, env in enumerate(envs):
            if env["environment"] == "proof":
                continue
            r = dict(env)
            r["statement_end"] = env["end"]
            r["labels"] = [m.group(1) for m in LABEL_RE.finditer(self.code[r["start"]:r["statement_end"]])]
            r["proof_spans"] = []
            j = i + 1
            while j < len(envs) and envs[j]["environment"] == "proof":
                gap = self.code[r["end"]:envs[j]["start"]]
                if gap.strip():
                    break
                title = re.match(r"\\begin\{proof\}\s*\[([^\]]*)\]", self.code[envs[j]["start"]:envs[j]["end"]])
                targets = {label.strip() for m in REF_RE.finditer(title.group(1))
                           for label in m.group(1).split(',')} if title else set()
                # A delayed proof names its own result; adjacency cannot also
                # assign it to an unrelated intervening proposition.
                if targets and not targets.intersection(r["labels"]):
                    break
                r["proof_start"] = r.get("proof_start", envs[j]["start"])
                r["proof_spans"].append((envs[j]["start"], envs[j]["end"]))
                r["end"] = envs[j]["end"]
                j += 1
            results.append(r)
        for env in envs:
            if env["environment"] != "proof":
                continue
            title = re.match(r"\\begin\{proof\}\s*\[([^\]]*)\]", self.code[env["start"]:env["end"]])
            if not title:
                continue
            targets = {label.strip() for m in REF_RE.finditer(title.group(1)) for label in m.group(1).split(',')}
            for r in results:
                span = (env["start"], env["end"])
                if targets.intersection(r["labels"]) and span not in r["proof_spans"]:
                    r["proof_spans"].append(span)
        return results


def exact_bridge(old, current, location, identifier):
    start, end = location["start_character"], location["end_character"]
    excerpt = old.text[start:end]
    fail(digest(excerpt.encode()) == location["text_sha256"], "Historical span hash differs: " + identifier)
    occurrences = [m.start() for m in re.finditer(re.escape(excerpt), current.text)] if excerpt else []
    result = {"id": identifier, "historical": location,
              "text_sha256": digest(excerpt.encode()), "match_count": len(occurrences)}
    if len(occurrences) == 1:
        result.update(status="exact_unchanged_text", current=current.span(occurrences[0], occurrences[0] + len(excerpt)))
    elif not occurrences:
        result.update(status="changed_or_missing", current=None)
    else:
        # A unique labeled container can disambiguate repeated short formulas.
        result.update(status="ambiguous_repeated_text", current=None,
                      candidate_lines=[bisect.bisect_right(current.starts, p) for p in occurrences])
    return result


def collect(repo, manuscript, new_input):
    fail(new_input.get("schema") == REGISTER_SCHEMA, "Expected Version 6 authored-register schema")
    predecessor, inv5, predecessor_pins = validate_predecessor(repo, new_input)
    v5_apps, retired = predecessor_dispositions(inv5, new_input)
    app_ids_input = [a["id"] for a in new_input.get("applications", [])]
    fail(len(app_ids_input) == len(set(app_ids_input)), "Duplicate current application ID")
    fragment_ids = [f["id"] for f in new_input.get("reviewed_fragments", [])]
    fail(len(fragment_ids) == len(set(fragment_ids)), "Duplicate reviewed fragment ID")
    policy = new_input.get("dependency_policy", {})
    fail(policy.get("uses_frei_tinkova_as_assumed_theorem") is False,
         "Version 6 requires explicit no-FT-assumed-theorem policy")
    fail(policy.get("all_final_published_versions_checked") is False,
         "Do not claim all final published versions were checked")
    fail(isinstance(policy.get("all_assumed_external_results_published"), bool),
         "Missing authored publication status")
    for app in new_input.get("applications", []):
        fail("v5ft" not in app.get("citation_keys", []),
             "FT citation must be attribution, not an assumed application: " + app["id"])
    old = Tex(read(repo, OLD_TEX), OLD_TEX)
    current = Tex(read(repo, manuscript), manuscript)
    if new_input.get("candidate_pin"):
        fail(new_input["candidate_pin"]["path"] == manuscript, "Authored candidate path differs")
        verify_pin(repo, new_input["candidate_pin"], "Authored candidate changed")
    bridge4 = load(repo, V4 + "baseline-bridge.json")
    inv4 = load(repo, V4 + "theorem-applications.json")
    apps0 = load(repo, BASE + "applications.json")
    cites0 = {c["id"]: c for c in load(repo, BASE + "citations.json")}
    sources0 = load(repo, BASE + "sources.json")
    fail(digest(old.raw) == bridge4["current_sha256"], "V4 manuscript differs from its accepted bridge")
    pins = predecessor_pins + [pin(repo, path) for path in [OLD_TEX, BASE + "applications.json", BASE + "citations.json",
            BASE + "sources.json", V4 + "baseline-bridge.json", V4 + "theorem-applications.json",
            V4 + "dependency-closure.json", NEW + "new-applications.json"]]
    reviewed_fragments = []
    for spec in new_input.get("reviewed_fragments", []):
        actual = pin(repo, spec["path"])
        fail(actual["sha256"] == spec["sha256"], "Reviewed fragment changed: " + spec["id"])
        fragment = tex_text(read(repo, spec["path"])).strip()
        fail(bool(fragment), "Empty reviewed fragment: " + spec["id"])
        bind_fragment_provenance(repo, spec, fragment, predecessor, inv5,
                                 {p["path"] for p in new_input.get("evidence_pins", [])})
        positions = [m.start() for m in re.finditer(re.escape(fragment), current.text)]
        fail(len(positions) == 1, "Reviewed fragment must occur exactly once: " + spec["id"])
        reviewed_fragments.append({**spec, "current": current.span(positions[0], positions[0] + len(fragment))})
        pins.append(actual)
    for spec in new_input.get("evidence_pins", []):
        actual = pin(repo, spec["path"])
        fail(actual["sha256"] == spec["sha256"], "Review evidence changed: " + spec["path"])
        pins.append(actual)
    proof_subaudits = []
    for spec in new_input.get("external_proof_subaudits", []):
        audit = load(repo, spec["path"])
        fail(any(p["path"] == spec["path"] for p in new_input.get("evidence_pins", [])),
             "External proof subaudit is not pinned: " + spec["path"])
        proof_subaudits.append({**spec, "audit": audit})
    bridges, inherited_apps, source_ledgers = [], [], []
    application_bridges = {}
    for rec in bridge4["anchors"]:
        b = exact_bridge(old, current, rec["version4_location"], rec["id"])
        b["application_id"] = rec["application_id"]
        bridges.append(b)
        application_bridges.setdefault(rec["application_id"], []).append(b)
    for app in apps0:
        bs = application_bridges.get(app["id"], [])
        inherited_apps.append({
            "id": app["id"], "kind": "inherited_external_application",
            "status": "inherited_scoped_review_text_revalidated" if bs and all(b["current"] for b in bs) else "text_bridge_requires_review",
            "exact_source_versions": [s for s in sources0 if s["id"] in app["sources"]],
            "theorem_or_source_locator": app["source_locator"],
            "objects_and_maps": app["objects_and_maps"],
            "hypotheses_and_discharge": app["hypotheses_and_discharge"],
            "conventions": app["conventions"],
            "translation": app["translation_justification"],
            "historical_record": app,
            "current_sites": [b["current"] for b in bs if b["current"]],
            "bridge_ids": [b["id"] for b in bs],
            "review_limit": "Earlier scoped decision applies only through the individually checked unchanged excerpts; no new proof or blanket whole-manuscript approval is inferred.",
        })
    historical_cites = []
    for rec in bridge4["citation_paragraphs"]:
        b = exact_bridge(old, current, rec["version4_location"], rec["id"])
        b.update(kind="historical_citation", keys=rec["keys"], role=rec["role"],
                 application_ids=cites0.get(rec["id"], {}).get("application_ids", []))
        historical_cites.append(b)
    extras = []
    for rec in inv4["inherited_additional_published_applications"] + inv4["additional_published_applications"]:
        locations = [s["version4_location"] for s in rec.get("current_sites", [])]
        if rec.get("current_source"):
            locations.append(rec["current_source"])
        bs = [exact_bridge(old, current, loc, rec["id"] + "-" + str(i)) for i, loc in enumerate(locations)]
        for b in bs:
            b["application_id"] = rec["id"]
        bridges.extend(bs)
        extras.append({"id": rec["id"], "kind": "inherited_additional_application",
                       "status": "inherited_scoped_review_text_revalidated" if bs and all(b["current"] for b in bs) else "text_bridge_requires_review",
                       "historical_record": rec, "current_sites": [b["current"] for b in bs if b["current"]]})
    inherited_v5 = []
    for app_id in new_input.get("inherit_v5_applications", []):
        rec = v5_apps[app_id]
        fail(bool(rec.get("current_sites")), "Inherited V5 application has no reviewed sites: " + app_id)
        bs = [exact_bridge(predecessor, current, loc, app_id + ":v5:" + str(i))
              for i, loc in enumerate(rec["current_sites"])]
        for b in bs:
            b["application_id"] = app_id
            b["predecessor_version"] = 5
        bridges.extend(bs)
        inherited_v5.append({"id": app_id, "kind": "inherited_v5_application",
            "status": "inherited_scoped_review_text_revalidated" if bs and all(b["current"] for b in bs) else "text_bridge_requires_review",
            "historical_record": rec, "citation_keys": rec.get("citation_keys", []),
            "current_sites": [b["current"] for b in bs if b["current"]],
            "review_limit": "Version 5 review follows only its exact unchanged application excerpts."})
    for spec in new_input.get("inherited_ledgers", []):
        ledger = load(repo, spec["path"])
        pins.append(pin(repo, spec["path"]))
        bs = []
        for label in spec.get("labels", []) + spec.get("section_labels", []):
            a, z = old.section_span(label) if label in spec.get("section_labels", []) else old.label_span(label)
            b = exact_bridge(old, current, old.span(a, z), spec["id"] + ":" + label)
            b["application_id"] = spec["id"]
            bs.append(b)
        bridges.extend(bs)
        source_ledgers.append({**spec, "historical_ledger": ledger,
                              "status": "registered_scoped_ledger_text_revalidated" if bs and all(b["current"] for b in bs) else "text_bridge_requires_review",
                              "current_sites": [b["current"] for b in bs if b["current"]]})
    new_apps = []
    for rec in new_input.get("applications", []):
        for key in ["id", "exact_source_versions", "theorem_or_source_locator", "objects_and_maps",
                    "hypotheses_and_discharge", "conventions", "translation", "status", "current_labels"]:
            fail(rec.get(key), "New application lacks " + key + ": " + rec.get("id", "?"))
        sites = []
        for label in rec.get("current_labels", []):
            if label not in current.labels:
                continue
            a, z = current.label_span(label)
            sites.append({**current.span(a, z), "label": label})
        fragment = next((f for f in reviewed_fragments if f["id"] == rec.get("reviewed_fragment")), None)
        fail(fragment is not None, "New application lacks reviewed fragment: " + rec["id"])
        fail(all(fragment["current"]["start_character"] <= s["start_character"] < s["end_character"] <= fragment["current"]["end_character"] for s in sites),
             "New application escapes reviewed fragment: " + rec["id"])
        new_apps.append({**rec, "current_sites": sites,
                         "binding_status": "bound" if len(sites) == len(rec.get("current_labels", [])) and sites else "missing_current_labels"})
    consumption = []
    for rec in new_input.get("current_consumption", []):
        labels = rec.get("current_labels", [])
        sites = [{**current.span(*current.label_span(label)), "label": label} for label in labels if label in current.labels]
        consumption.append({**rec, "current_sites": sites,
                            "binding_status": "bound" if len(sites) == len(labels) and sites else "missing_current_labels"})
    metadata_rows = new_input.get("internal_results", [])
    result_metadata = {r["label"]: r for r in metadata_rows if r.get("label")}
    statement_metadata = {}
    fail(len(result_metadata) == sum(bool(r.get("label")) for r in metadata_rows),
         "Duplicate internal-result label metadata")
    for rec in metadata_rows:
        if rec.get("label"):
            continue
        key = rec.get("statement_sha256")
        fail(key and key not in statement_metadata, "Missing or duplicate unlabeled statement hash")
        matches = [r for r in current.results if digest(current.text[r["start"]:r["statement_end"]].encode()) == key]
        fail(len(matches) == 1 and not matches[0]["labels"], "Unlabeled metadata must match exactly one unlabeled statement")
        r = matches[0]
        fail(rec.get("current_statement") == current.span(r["start"], r["statement_end"]),
             "Unlabeled metadata statement span differs")
        statement_metadata[key] = rec
    old_results_by_label = {label: r for r in old.results for label in r["labels"]}
    v5_results_by_label = {label: r for r in predecessor.results for label in r["labels"]}
    v5_review_ranges = [f["current"] for f in inv5.get("reviewed_fragments", [])]
    internal = []
    for index, r in enumerate(current.results, 1):
        labels = r["labels"]
        primary = labels[0] if labels else "unlabeled-" + str(index)
        excerpt = current.text[r["start"]:r["statement_end"]] + "\n" + "\n".join(current.text[a:z] for a,z in r["proof_spans"])
        old_matches = [old_results_by_label[l] for l in labels if l in old_results_by_label]
        unchanged = any(old.text[o["start"]:o["statement_end"]] + "\n" + "\n".join(old.text[a:z] for a,z in o["proof_spans"]) == excerpt for o in old_matches)
        v5_matches = [v5_results_by_label[l] for l in labels if l in v5_results_by_label]
        unchanged5 = any(
            predecessor.text[o["start"]:o["statement_end"]] + "\n" + "\n".join(predecessor.text[a:z] for a,z in o["proof_spans"]) == excerpt
            and all(any(s["start_character"] <= a < z <= s["end_character"] for s in v5_review_ranges)
                    for a,z in [(o["start"],o["statement_end"])] + o["proof_spans"])
            for o in v5_matches)
        metadata = next((result_metadata[l] for l in labels if l in result_metadata), None)
        if metadata is None and not labels:
            metadata = statement_metadata.get(digest(current.text[r["start"]:r["statement_end"]].encode()))
        status = "inherited_internal_result_text_unchanged" if unchanged else "new_or_changed_result_requires_review"
        if unchanged5:
            status = "inherited_v5_reviewed_result_text_unchanged"
        if metadata:
            fragment = next((f for f in reviewed_fragments if f["id"] == metadata.get("reviewed_fragment")), None)
            fail(fragment is not None, "Internal result lacks reviewed fragment: " + primary)
            ranges = [(r["start"], r["statement_end"])] + r["proof_spans"]
            fail(all(fragment["current"]["start_character"] <= a < z <= fragment["current"]["end_character"] for a,z in ranges),
                 "Internal result escapes reviewed fragment: " + primary)
            status = metadata["status"]
        internal.append({"id": primary, "labels": labels, "environment": r["environment"],
                         "statement": current.span(r["start"], r["statement_end"]),
                         "statement_and_proof": current.span(r["start"], r["end"]),
                         "proof_spans": [current.span(a,z) for a,z in r["proof_spans"]],
                         "has_following_proof": "proof_start" in r, "status": status,
                         "metadata": metadata, "inherited_body_equal": unchanged,
                         "inherited_v5_reviewed_body_equal": unchanged5,
                         "explicit_internal_dependencies": sorted(set(x for m in REF_RE.finditer(uncomment(excerpt)) for x in m.group(1).split(','))),
                         "explicit_citation_keys": sorted(set(k.strip() for m in CITE_RE.finditer(uncomment(excerpt)) for k in m.group(3).split(','))),
                         "review_limit": "Text identity and explicit references are checked mechanically; inherited internal propositions keep their existing proof status."})
    bibliography = []
    bib_matches = list(re.finditer(r"\\bibitem(?:\[[^\]]*\])?\s*\{([^{}]+)\}", current.code))
    bibkeys = [m.group(1) for m in bib_matches]
    fail(len(bibkeys) == len(set(bibkeys)), "Duplicate bibliography key")
    for i, m in enumerate(bib_matches):
        end = bib_matches[i + 1].start() if i + 1 < len(bib_matches) else current.code.find(r"\end{thebibliography}", m.end())
        fail(end >= m.end(), "Missing bibliography end")
        bibliography.append({"key": m.group(1), "span": current.span(m.start(), end),
                             "text": current.text[m.start():end],
                             "historical_source_records": [s for s in sources0 if s["id"] == m.group(1)]})
    citations = []
    old_cites = list(CITE_RE.finditer(old.code))
    for i, m in enumerate(CITE_RE.finditer(current.code), 1):
        keys = [k.strip() for k in m.group(3).split(',')]
        fail(all(k in bibkeys for k in keys), "Citation key absent from bibliography: " + str(keys))
        a, z = current.paragraph(m.start())
        applications = set()
        inherited_citation_ids = []
        for b in historical_cites:
            s = b["current"]
            if s and s["start_character"] <= m.start() < s["end_character"] and set(keys).intersection(b["keys"]):
                applications.update(b["application_ids"])
                inherited_citation_ids.append(b["id"])
        for app in extras + inherited_v5 + source_ledgers + new_apps:
            allowed = app.get("citation_keys") or app.get("historical_record", {}).get("citation_keys")
            for s in app["current_sites"]:
                if s["start_character"] <= m.start() < s["end_character"] and (not allowed or set(keys).intersection(allowed)):
                    applications.add(app["id"])
        # Even paragraphs absent from the old registry get a per-occurrence
        # identity check, but that is not automatically a source review.
        command = current.text[m.start():m.end()]
        paragraph = current.text[a:z]
        old_paragraph_equal = any(old.text[old.paragraph(om.start())[0]:old.paragraph(om.start())[1]] == paragraph
                                  and old.text[om.start():om.end()] == command for om in old_cites)
        containing = current.enclosing(m.start())
        roles = [b["role"] for b in historical_cites if b["id"] in inherited_citation_ids]
        role = roles[0] if roles else "application"
        status = "registered_application" if applications else "inherited_nonapplication_citation" if role in ("provenance", "summary", "source_scope", "source-scope declaration", "conventions") else "unregistered_application"
        # Explicit author classifications cover new attribution/scope prose.
        exact_source_applications = None
        for rec in new_input.get("citation_classifications", []):
            if set(keys) == set(rec["keys"]) and rec["contains"] in paragraph:
                fail(rec["role"] in {"provenance", "summary", "source_scope", "source-scope declaration", "conventions"}
                     or rec.get("application_ids"), "Application classification lacks application IDs")
                role, status = rec["role"], "explicitly_classified_" + rec["role"]
                if rec["role"] == "source_statement":
                    # Exact authored occurrence assignments distinguish several
                    # source theorems used inside one large current result.
                    if exact_source_applications is None:
                        exact_source_applications = set()
                    exact_source_applications.update(rec.get("application_ids", []))
                applications.update(rec.get("application_ids", []))
        if exact_source_applications is not None:
            applications.difference_update(a["id"] for a in new_apps)
            applications.update(exact_source_applications)
        if "v5ft" in keys:
            fail(role in {"provenance", "summary", "source_scope", "source-scope declaration"},
                 "Version 6 FT citation is not explicitly non-assumed: line " + str(current.span(m.start(), m.end())["first_line"]))
        citations.append({"id": "V6-C" + str(i).zfill(4), "keys": keys,
                          "locator": m.group(2) if m.group(2) is not None else m.group(1),
                          "command": command, "span": current.span(m.start(), m.end()),
                          "paragraph": current.span(a, z), "paragraph_text": paragraph,
                          "applications": sorted(applications), "historical_citation_ids": inherited_citation_ids,
                          "old_paragraph_equal": old_paragraph_equal,
                          "enclosing_result": containing["labels"][0] if containing and containing["labels"] else None,
                          "role": role, "status": status})
    references = [{"label": label.strip(), "line": bisect.bisect_right(current.starts, m.start()),
                   "resolved": label.strip() in current.labels}
                  for m in REF_RE.finditer(current.code) for label in m.group(1).split(',')]
    unresolved = [b for b in bridges if not b["current"]]
    unknown_cites = [c["id"] for c in citations if c["status"] == "unregistered_application"]
    unknown_results = [r["id"] for r in internal if r["status"] == "new_or_changed_result_requires_review"]
    missing_new = [a["id"] for a in new_apps if a["binding_status"] != "bound"]
    missing_consumption = [a["id"] for a in consumption if a["binding_status"] != "bound"]
    pending = [a["id"] for a in new_apps + internal if any(word in a["status"] for word in ["pending", "requires_review", "unreviewed"])]
    identifiers = set(current.labels) | {a["id"] for a in inherited_apps + extras + inherited_v5 + source_ledgers + new_apps + consumption}
    unresolved_declared = []
    for node in consumption + [dict(r["metadata"], id=r["id"]) for r in internal if r["metadata"]]:
        for dep in node.get("depends_on", []) + node.get("declared_dependencies", []):
            if dep not in identifiers:
                unresolved_declared.append({"node": node["id"], "dependency": dep})
    app_ids = {a["id"] for a in inherited_apps + extras + inherited_v5 + source_ledgers + new_apps}
    application_rows = inherited_apps + extras + inherited_v5 + source_ledgers + new_apps
    fail(len(app_ids) == len(application_rows), "Duplicate application ID across inherited and current registers")
    for audit in proof_subaudits:
        fail(audit.get("current_application") in app_ids,
             "External proof subaudit names inactive application: " + audit["id"])
    unknown_application_ids = [{"citation": c["id"], "application": app_id}
                               for c in citations for app_id in c["applications"] if app_id not in app_ids]
    graph = {"schema": "quartic-v6-explicit-dependency-graph-v1",
             "scope": "Explicit TeX references plus authored interface dependencies; not a semantic completeness proof.",
             "internal_nodes": [{"id": r["id"], "status": r["status"], "references": r["explicit_internal_dependencies"],
                                 "citations": r["explicit_citation_keys"],
                                 "declared_dependencies": (r["metadata"] or {}).get("declared_dependencies", [])} for r in internal],
             "interface_nodes": consumption,
             "external_proof_subaudits": proof_subaudits,
             "application_nodes": [{"id": a["id"], "status": a["status"], "current_sites": a["current_sites"]}
                                   for a in inherited_apps + extras + inherited_v5 + source_ledgers + new_apps],
             "retired_v5_applications": retired}
    coverage = {"schema": "quartic-v6-inventory-coverage-v1", "manuscript": pin(repo, manuscript),
                "external_application_families": len(inherited_apps) + len(extras) + len(inherited_v5) + len(new_apps),
                "inherited_v5_applications": len(inherited_v5), "retired_v5_applications": retired,
                "inherited_source_ledgers": len(source_ledgers), "explicit_citations": len(citations),
                "cited_keys": len(set(k for c in citations for k in c["keys"])),
                "bibliography_entries": len(bibliography), "internal_results": len(internal),
                "references": len(references), "unresolved_references": [r for r in references if not r["resolved"]],
                "unresolved_application_bridges": [b["id"] for b in unresolved],
                "unregistered_citations": unknown_cites, "new_results_without_review_record": unknown_results,
                "new_applications_missing_labels": missing_new,
                "interfaces_missing_labels": missing_consumption, "pending_review_records": pending,
                "unresolved_declared_dependencies": unresolved_declared,
                "unknown_citation_application_ids": unknown_application_ids,
                "reviewed_fragments": reviewed_fragments,
                "new_source_qualifications": new_input.get("new_source_qualifications", []),
                "all_external_inputs_published": policy["all_assumed_external_results_published"],
                "all_final_published_versions_checked": False,
                "uses_frei_tinkova_as_assumed_theorem": False,
                "external_proofs_independently_closed": False,
                "external_proof_subaudits": [{"id": a["id"], "path": a["path"],
                    "proof_closed": a["audit"].get("proofClosed", False),
                    "nodes": len(a["audit"].get("nodes", [])),
                    "published_parent_records": len(a["audit"].get("externalParents", []))} for a in proof_subaudits],
                "external_proof_scope": "This inventory checks exact source applications and reviewed fragment identity, not mathematical truth. The authored Version 6 register retires the Frei–Tinkova assumed theorem and records its replacement proofs. Published-result status does not assert comparison with every final typeset version or re-prove all external papers.",
                "source_qualifications": inv4["source_version_requirements"],
                "scope": "Mechanically exhaustive explicit citations and declared result environments; semantic theorem use and mathematical truth require the recorded reviews."}
    coverage["status"] = "PASS_DOCUMENT_BINDING" if not (unresolved or unknown_cites or unknown_results or missing_new or missing_consumption or pending or unresolved_declared or unknown_application_ids or coverage["unresolved_references"]) else "REVIEW_ITEMS_REMAIN"
    return {
        "theorem-applications.json": {"schema": "quartic-v6-theorem-applications-v1", "manuscript": pin(repo, manuscript),
                                      "input_pins": pins, "inherited_applications": inherited_apps,
                                      "inherited_additional_applications": extras, "inherited_scoped_ledgers": source_ledgers,
                                      "inherited_v5_applications": inherited_v5, "retired_v5_applications": retired,
                                      "new_applications": new_apps, "current_consumption": consumption,
                                      "external_proof_subaudits": proof_subaudits,
                                      "reviewed_fragments": reviewed_fragments,
                                      "source_qualifications": inv4["source_version_requirements"]},
        "inherited-bridge.json": {"schema": "quartic-v6-exact-span-bridge-v1", "old_manuscript": pin(repo, OLD_TEX),
                                  "version5_manuscript": pin(repo, V5_TEX),
                                  "current_manuscript": pin(repo, manuscript), "application_spans": bridges,
                                  "citation_spans": historical_cites},
        "citations.json": citations, "internal-results.json": internal,
        "bibliography.json": bibliography, "dependency-graph.json": graph, "coverage.json": coverage,
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("command", choices=["build", "validate"])
    parser.add_argument("--repo", type=Path, default=DEFAULT_REPO)
    parser.add_argument("--manuscript", default="manuscripts/quartic_v7.tex")
    parser.add_argument("--allow-review-items", action="store_true")
    parser.add_argument("--expected-input-sha256")
    args = parser.parse_args()
    input_path = NEW + "new-applications.json"
    if args.expected_input_sha256:
        fail(pin(args.repo, input_path)["sha256"] == args.expected_input_sha256,
             "Input register differs from externally selected hash")
    input_data = load(args.repo, input_path)
    documents = collect(args.repo, args.manuscript, input_data)
    if args.command == "build":
        for name, data in documents.items():
            (args.repo / NEW / name).write_bytes(encoded(data))
    else:
        for name, data in documents.items():
            fail(read(args.repo, NEW + name) == encoded(data), "Derived inventory differs: " + name)
    print(json.dumps(documents["coverage.json"], indent=2))
    if not args.allow_review_items:
        fail(documents["coverage.json"]["status"] == "PASS_DOCUMENT_BINDING", "Unresolved inventory review items")


if __name__ == "__main__":
    main()
