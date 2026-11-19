"""Pure validation of a deferred gate merge before post-merge dispatch.

Callers must obtain all
records through authenticated GitHub API reads and verify artifact provenance.
This module makes no requests, executes no candidate content, and never decides
that an uncertain prior operation is safe to retry.
"""
import datetime
import json
import re
from urllib.parse import urlparse

SHA = re.compile(r"[0-9a-f]{40}")
WORKFLOWS = ("research-checks.yml", "kernel-lean.yml")


def _sha(value):
    return isinstance(value, str) and SHA.fullmatch(value) is not None


def _validate_publication(repo, app_id, pr, check, publisher, decision, deferred):
    """Return immutable operation identities, or fail closed with a reason.

    `decision` and `deferred` are original artifacts from the
    authenticated publisher run. Archive download, attempt binding and digest
    verification belong to the I/O layer, which is not implemented here.
    """
    def fail(reason):
        return {"eligible": False, "reason": reason, "operations": []}

    if not isinstance(repo, str) or re.fullmatch(r"[A-Za-z0-9_.-]+/[A-Za-z0-9_.-]+", repo) is None:
        return fail("repository")
    if type(app_id) is not int or app_id <= 0 or app_id == 15368:
        return fail("required_app")
    if any(not isinstance(x, dict) for x in (pr, check, publisher, decision, deferred)):
        return fail("malformed_record")
    number = pr.get("number")
    head = (pr.get("head") or {}).get("sha")
    merge = pr.get("merge_commit_sha")
    base = pr.get("base") or {}
    if (type(number) is not int or number <= 0 or pr.get("state") != "closed"
            or pr.get("merged") is not True or not _sha(head) or not _sha(merge)):
        return fail("unconfirmed_merge")
    if base.get("ref") != "main" or (base.get("repo") or {}).get("full_name") != repo:
        return fail("wrong_base")
    actor = pr.get("merged_by") or {}
    if actor.get("login") != "github-actions[bot]" or actor.get("type") != "Bot":
        return fail("not_workflow_merge")
    if (check.get("name") != "Protocol B / review" or check.get("head_sha") != head
            or check.get("status") != "completed" or check.get("conclusion") != "success"
            or (check.get("app") or {}).get("id") != app_id
            or type(check.get("id")) is not int):
        return fail("no_exact_head_app_acceptance")
    try:
        stored = json.loads((check.get("output") or {}).get("text") or "")
    except (TypeError, ValueError):
        return fail("invalid_app_record")
    if not isinstance(stored, dict) or stored.get("schema") != "protocol-b-decisions/v1" or stored.get("head") != head:
        return fail("invalid_app_record")
    url = urlparse(check.get("details_url") or "")
    match = re.fullmatch(r"/" + re.escape(repo) + r"/actions/runs/([1-9][0-9]*)", url.path)
    if url.scheme != "https" or url.netloc != "github.com" or url.query or url.fragment or match is None:
        return fail("invalid_publisher_link")
    run_id = int(match.group(1))
    if (publisher.get("id") != run_id or (publisher.get("repository") or {}).get("full_name") != repo
            or publisher.get("path") != ".github/workflows/protocol-b.yml"
            or publisher.get("event") not in {"pull_request_target", "issue_comment", "workflow_dispatch", "schedule", "workflow_run"}):
        return fail("wrong_publisher")
    # Failed publishers may have successfully enabled auto-merge, then failed
    # during an unrelated upload. Their original receipts must still be read.
    if publisher.get("status") != "completed":
        return fail("publisher_still_running")
    if type(publisher.get("run_attempt")) is not int or publisher["run_attempt"] <= 0:
        return fail("invalid_publisher_attempt")
    if (decision.get("number") != number or decision.get("head") != head
            or decision.get("check") != check["id"] or decision.get("conclusion") != "success"
            or decision.get("mode") != "live" or decision.get("name") != "Protocol B / review"):
        return fail("decision_mismatch")
    if deferred.get("number") != number or deferred.get("head") != head:
        return fail("deferred_receipt_mismatch")
    operations = [{"repository": repo, "number": number, "head": head, "merge": merge,
                   "publisher_run": run_id, "publisher_attempt": publisher["run_attempt"],
                   "app_check": check["id"], "workflow": workflow, "ref": "main"}
                  for workflow in WORKFLOWS]
    return {"eligible": True, "reason": "confirmed_deferred_gate_merge", "operations": operations}


def _confirmed_request(pr, auto_result):
    if not isinstance(auto_result, dict):
        return False
    data = auto_result.get("data")
    mutation = data.get("enablePullRequestAutoMerge") if isinstance(data, dict) else None
    result = mutation.get("pullRequest") if isinstance(mutation, dict) else None
    return (not auto_result.get("errors") and isinstance(result, dict)
            and isinstance(pr.get("node_id"), str) and result.get("id") == pr["node_id"])


def validate_deferred_source(repo, app_id, pr, check, publisher, decision, deferred, auto_result):
    """Compatibility entry for an acceptance and request from one publication."""
    result = _validate_publication(repo, app_id, pr, check, publisher, decision, deferred)
    if not result["eligible"]:
        return result
    if not _confirmed_request(pr, auto_result):
        return {"eligible": False, "reason": "auto_merge_request_unconfirmed", "operations": []}
    return result


def validate_deferred_chain(repo, app_id, pr, accepted, requester):
    """Bind a later acceptance to the original auto-merge request publication.

    Both record bundles must already have passed artifact authentication. This
    does not discover or trust a requester merely because another record names
    it. The caller supplies each original check, run and artifact separately.
    """
    def fail(reason):
        return {"eligible": False, "reason": reason, "operations": []}
    results = []
    for name, source in (("accepted", accepted), ("requester", requester)):
        if not isinstance(source, dict):
            return fail(name + ":malformed_record")
        try:
            result = _validate_publication(repo, app_id, pr, *[source[k] for k in
                ("check", "publisher", "decision", "deferred")])
        except (KeyError, TypeError, AttributeError):
            return fail(name + ":malformed_record")
        if not result["eligible"]:
            return fail(name + ":" + result["reason"])
        results.append(result)
    if not _confirmed_request(pr, requester.get("auto_result")):
        return fail("auto_merge_request_unconfirmed")
    try:
        requested = datetime.datetime.fromisoformat(requester["publisher"]["created_at"].replace('Z', '+00:00'))
        accepted_at = datetime.datetime.fromisoformat(accepted["publisher"]["created_at"].replace('Z', '+00:00'))
        merged = datetime.datetime.fromisoformat(pr["merged_at"].replace('Z', '+00:00'))
        if any(t.utcoffset() is None for t in (requested, accepted_at, merged)) or not requested <= accepted_at <= merged:
            return fail("publication_chronology")
    except (KeyError, TypeError, ValueError, AttributeError):
        return fail("publication_chronology")
    result = results[0]
    original = results[1]["operations"][0]
    for operation in result["operations"]:
        operation["requester_run"] = original["publisher_run"]
        operation["requester_attempt"] = original["publisher_attempt"]
        operation["requester_check"] = original["app_check"]
    return result
