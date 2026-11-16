#!/usr/bin/env python3
"""Validate the current inventory's bindings, not its mathematical assertions.

Run from the repository root: python docs/quartic-12504/validate.py
The separate certificate/source checkers perform the finite algebraic checks.
"""
import argparse, gzip, hashlib, json, re
from pathlib import Path

def load(p): return json.loads(p.read_text(encoding="utf-8-sig"))
def digest(data): return hashlib.sha256(data).hexdigest()
def sha(p): return digest(p.read_bytes())
def require(ok, message):
    if not ok: raise ValueError(message)
def within(root, rel):
    p=(root/rel).resolve()
    require(p.is_relative_to(root.resolve()), "Path escapes repository: "+rel)
    return p
def span(value, length):
    require(isinstance(value,list) and len(value)==2 and all(type(x) is int for x in value) and 1<=value[0]<=value[1]<=length,"Invalid excerpt range")
    return value

def validate(repo):
    docs=repo/"docs/quartic-12504"; pkg=repo/"quartics/quartic-12504"
    inv=load(docs/"theorem-applications.json"); spec=load(docs/"inventory-spec.json")
    closure=load(docs/"dependency-closure.json"); bridge=load(docs/"baseline-bridge.json")
    require(inv["source_contract"]==spec["source_contract"],"Source contract mismatch")
    expected=spec["expected_final"]
    require(expected["variables"]==12504 and expected["rows"]==11939 and expected["degree"]==4,"Wrong release")
    manuscript=within(repo,inv["manuscript"]); raw=manuscript.read_bytes(); text=raw.decode("utf-8-sig"); lines=text.splitlines()
    require(digest(raw)==inv["manuscript_source_sha256"]==bridge["current_sha256"],"Current manuscript changed")
    labels={}
    for i,line in enumerate(lines,1):
        for m in re.finditer(r"\\label\{([^}]+)\}",line):labels.setdefault(m[1],[]).append(i)
    for label in ["thm:quartic","thm:quartic-source-arithmetic","lem:quartic-reciprocal-log","lem:quartic-reciprocal-nonzero","lem:quartic-compressed-primary"]:
        require(len(labels.get(label,[]))==1,"Missing or duplicate label: "+label)
    for label,value in inv["label_lines"].items():require(labels.get(label)==value,"Moved label: "+label)
    for family in closure["inherited_families"]:
        for label in family.get("labels",[]): require(len(labels.get(label,[]))==1,"Missing inherited label: "+label)

    entry=load(pkg/"source-entry.json"); contract=spec["source_contract"]
    for key in ["source_id","source_sha256","source_variables","source_rows","high"]:
        require(entry[key]==contract[key],"Source entry: "+key)
    require(entry["label"]==16 and entry["compressed"] is True and entry["source_header"]["anchor_squarings"]==24,"Source variant")
    require(entry["uncompressed_sha256"]==contract["source_uncompressed_sha256"],"Raw source hash")
    for rel,pin in entry["inspected_files_sha256"].items():
        path=within(pkg/"source",rel)
        if path.is_file(): actual=sha(path)
        elif rel=="residuals.jsonl" and Path(str(path)+".gz").is_file(): actual=digest(gzip.decompress(Path(str(path)+".gz").read_bytes()))
        else: raise ValueError("Missing inspected source: "+rel)
        require(actual==pin,"Inspected source changed: "+rel)
    for name,key in [("source-audit.json","source_audit_sha256"),("construction-map.json","construction_map_sha256")]:
        require(sha(pkg/name)==entry[key],"Source audit binding: "+name)
    require(sha(pkg/"reproducibility/source-audit/check_source.py")==entry["source_audit_checker_sha256"],"Source audit checker changed")
    require(sha(pkg/"source-residuals.jsonl.gz")==contract["source_sha256"],"Compressed source")
    require(digest(gzip.decompress((pkg/"source-residuals.jsonl.gz").read_bytes()))==contract["source_uncompressed_sha256"],"Raw source")
    receipt=load(pkg/"evidence/wave13-verification.json")
    for key,value in expected.items():
        require(str(receipt[key])==str(value) if key=="max_abs_coefficient" else receipt[key]==value,"Receipt mismatch: "+key)
        require(inv["certificate_binding"][key]==value,"Inventory finite binding: "+key)
    for name,key in [("certificate.jsonl.gz","certificate_sha256"),("verify_certificate.py","checker_sha256"),("polynomial.expanded.txt","expanded_sha256")]:
        require(sha(pkg/name)==expected[key],"Finite artifact changed: "+name)
    require(digest(gzip.decompress((pkg/"polynomial.expanded.txt.gz").read_bytes()))==expected["expanded_sha256"],"Expanded gzip disagrees")
    weights=load(pkg/"weights.json"); vm=load(pkg/"variable-map.json")
    require(weights==[1]*11939,"Square weights")
    require(len(vm)==12504 and len(set(vm))==12504 and vm[0]==0,"Variable map")

    checked=set()
    for item in closure["source_application_documents"]:
        require(sha(within(repo,item["path"]))==item["sha256"],"Dependency evidence changed: "+item["path"]);checked.add(item["path"])
    imports=load(docs/"evidence-import-manifest.json")
    require("source_repository" not in imports,"Absolute provenance field")
    for item in imports["files"]:
        rel=item["destination_relative"];require(sha(within(repo,rel))==item["sha256"],"Imported evidence changed: "+rel);checked.add(rel)
    release_files=load(docs/"release-evidence.json")
    for item in release_files["files"]:
        require(sha(within(repo,item["path"]))==item["sha256"],"Release evidence changed: "+item["path"]);checked.add(item["path"])

    ids=set(closure["local_lemmas"]); fids={x["id"] for x in closure["inherited_families"]}
    require(ids=={x["id"] for x in inv["elementary_lemmas"]},"Local lemma lists disagree")
    known=ids|fids|{"thm:quartic","thm:quartic-source-arithmetic","certificate_binding"}
    edges=closure["edges"]
    require(all(e["from"] in known and e["to"] in known for e in edges),"Dangling dependency")
    expected_edges={("thm:quartic","thm:quartic-source-arithmetic","arithmetic"),("thm:quartic","certificate_binding","finite"),("thm:quartic-source-arithmetic","reciprocal_source_integer_projection","local")}
    expected_edges|={("thm:quartic",d,"local") for d in inv["declarations"][0]["elementary_dependencies"]}
    expected_edges|={(x["id"],d,"local") for x in inv["elementary_lemmas"] for d in x.get("elementary_dependencies",[])}
    expected_edges|={(x["id"],d,"inherited") for x in inv["elementary_lemmas"] for d in x.get("inherited_dependencies",[])}
    expected_edges|={(x["id"],d,"inherited") for x in closure["inherited_families"] for d in x.get("depends_on",[])}
    actual_edges={(e["from"],e["to"],e["kind"]) for e in edges}
    require(actual_edges==expected_edges and len(actual_edges)==len(edges),"Dependency edge set disagrees with declarations")
    reached={"thm:quartic"}
    while True:
        nxt=reached|{e["to"] for e in edges if e["from"] in reached}
        if nxt==reached:break
        reached=nxt
    require(known<=reached,"Unreachable inventory nodes: "+str(sorted(known-reached)))

    hist=within(repo,bridge["historical_manuscript"]); hraw=hist.read_bytes(); old=hraw.decode("utf-8-sig").splitlines()
    cov=load(repo/"docs/theorem-application-audit/coverage.json")
    require(sha(hist)==bridge["historical_sha256"]==cov["manuscript_sha256"],"Historical manuscript hash")
    require(cov["manuscript_path"]==bridge["historical_manuscript"],"Historical coverage path")
    apps=load(repo/"docs/theorem-application-audit/applications.json")
    expected_anchors={f"{a['id']}-S{j:02}":x for a in apps for j,x in enumerate(a["manuscript_anchors"],1)}
    require(len(bridge["anchors"])==len(expected_anchors) and {x["id"] for x in bridge["anchors"]}==set(expected_anchors),"Bridge anchor coverage")
    require(bridge["status"]=="PASS" and not bridge["unresolved"],"Unreviewed changed applications")
    for item in bridge["anchors"]:
        anchor=expected_anchors[item["id"]];lo,hi=span(item["old_lines"],len(old));nlo,nhi=span(item["current_lines"],len(lines))
        require([lo,hi]==[anchor["line_start"],anchor["line_end"]],"Historical anchor moved")
        require(old[lo-1:hi]==lines[nlo-1:nhi],"Bridge excerpt changed: "+item["id"])
        require(digest("\n".join(lines[nlo-1:nhi]).encode())==item["excerpt_sha256"]==anchor["excerpt_sha256"],"Bridge excerpt hash")
    citations=load(repo/"docs/theorem-application-audit/citations.json")
    expected_citations={c["id"]:c for c in citations}
    require(len(bridge["citation_paragraphs"])==len(expected_citations) and {x["id"] for x in bridge["citation_paragraphs"]}==set(expected_citations),"Citation bridge coverage")
    for item in bridge["citation_paragraphs"]:
        original=expected_citations[item["id"]]
        require(item["keys"]==original["keys"] and item["role"]==original["role"] and item["old_line"]==original["line"] and item["paragraph_sha256"]==original["paragraph_sha256"],"Citation provenance changed")
        olo,ohi=original["paragraph_start"],original["paragraph_end"]
        require(digest("\n".join(old[olo-1:ohi]).encode())==original["paragraph_sha256"],"Historical citation hash")
        lo,hi=span(item["current_paragraph_lines"],len(lines))
        require(lines[lo-1:hi]==old[olo-1:ohi],"Citation text changed")
        require(digest("\n".join(lines[lo-1:hi]).encode())==item["paragraph_sha256"],"Citation excerpt changed")
    return {"status":"PASS","scope":"Inventory hashes, exact text bridge, dependency reachability and source/artifact bindings only; no mathematical truth or fresh certificate replay asserted.","manuscript_sha256":digest(raw),"historical_application_anchors":len(expected_anchors),"unmapped_citation_paragraphs":[x["id"] for x in bridge["citation_paragraphs"] if not x["current_paragraph_lines"]],"local_lemmas":len(ids),"inherited_families":len(fids),"evidence_files":len(checked)}

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--repo",type=Path,default=Path(__file__).resolve().parents[2])
    ap.add_argument("--output",type=Path)
    a=ap.parse_args();result=validate(a.repo.resolve())
    out=a.output or a.repo/"build/quartic-inventory.json";out.parent.mkdir(parents=True,exist_ok=True)
    out.write_text(json.dumps(result,indent=2)+"\n",encoding="utf-8");print(json.dumps(result))
if __name__=="__main__":main()
