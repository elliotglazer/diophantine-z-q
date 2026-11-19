"""Bounded reader for original gate records. """
import hashlib
import io
import json
import stat
import zipfile

MAX_ZIP = 32 * 1024 * 1024
MAX_RECORD = 16 * 1024 * 1024
RECORDS = ("decision.json", "post-merge-manual.json", "auto-merge-result.json")


def read_original_records(raw, artifact, publisher, expected_repository_id):
    """Validate supplied API metadata, then read JSON without extracting files.

    The caller still authenticates the publisher, obtains bytes through the
    GitHub API and validates the App decision. A valid ZIP is not acceptance.
    """
    def require(value, message):
        if not value:
            raise ValueError(message)
    require(isinstance(raw, bytes) and 0 < len(raw) <= MAX_ZIP, "archive size")
    require(isinstance(artifact, dict) and isinstance(publisher, dict), "metadata type")
    run, attempt = publisher.get("id"), publisher.get("run_attempt")
    require(type(run) is int and run > 0 and type(attempt) is int and attempt > 0, "publisher identity")
    require(type(expected_repository_id) is int and expected_repository_id > 0, "repository identity")
    binding = artifact.get("workflow_run")
    require(isinstance(binding, dict), "artifact run binding")
    require(artifact.get("name") == f"protocol-b-{run}-{attempt}" and artifact.get("expired") is False,
            "artifact name, attempt or expiry")
    require(binding.get("id") == run and binding.get("repository_id") == expected_repository_id
            and binding.get("head_sha") == publisher.get("head_sha") and bool(publisher.get("head_sha")),
            "artifact source mismatch")
    require(type(artifact.get("size_in_bytes")) is int and 0 < artifact["size_in_bytes"] <= MAX_ZIP,
            "declared archive size")
    require(artifact.get("digest") == "sha256:" + hashlib.sha256(raw).hexdigest(), "artifact digest")
    with zipfile.ZipFile(io.BytesIO(raw)) as archive:
        entries = archive.infolist()
        require(len(entries) <= 4096, "too many archive entries")
        names = [entry.filename for entry in entries]
        require(len(names) == len(set(names)), "duplicate archive entry")
        result = {}
        for name in RECORDS:
            if name not in names:
                # A later override publication may inherit an existing auto-
                # merge request. Its missing receipt is not proof of absence.
                continue
            entry = archive.getinfo(name)
            mode = entry.external_attr >> 16
            require(not entry.is_dir() and not stat.S_ISLNK(mode) and not entry.flag_bits & 1,
                    "non-regular or encrypted record")
            require(0 < entry.file_size <= MAX_RECORD, "record size")
            with archive.open(entry) as source:
                data = source.read(MAX_RECORD + 1)
            require(len(data) == entry.file_size and len(data) <= MAX_RECORD, "record read size")
            value = json.loads(data.decode("utf-8"))
            require(isinstance(value, dict), "record is not an object")
            result[name] = value
    return {"records": result, "missing": [name for name in RECORDS if name not in result],
            "artifact_id": artifact.get("id"), "digest": artifact["digest"],
            "publisher_run": run, "publisher_attempt": attempt}
