import copy
import hashlib
import io
import json
import unittest
import warnings
import zipfile
from unittest.mock import patch
import deferred_artifact as subject


class ArtifactTests(unittest.TestCase):
    def setUp(self):
        self.publisher = {"id": 123, "run_attempt": 2, "head_sha": "a" * 40}
        self.records = {name: b'{"fixture":true}' for name in subject.RECORDS}
        self.artifact = {"id": 4, "name": "protocol-b-123-2", "expired": False,
                         "workflow_run": {"id": 123, "repository_id": 7, "head_sha": "a" * 40}}

    def pack(self, records=None):
        out = io.BytesIO()
        with zipfile.ZipFile(out, 'w') as archive:
            for name, value in (self.records if records is None else records).items():
                archive.writestr(name, value)
        raw = out.getvalue()
        self.artifact.update(size_in_bytes=len(raw), digest='sha256:' + hashlib.sha256(raw).hexdigest())
        return raw

    def read(self, raw):
        return subject.read_original_records(raw, self.artifact, self.publisher, 7)

    def test_original_records_are_read_without_filesystem_extraction(self):
        raw = self.pack()
        with patch.object(zipfile.ZipFile, 'extract', side_effect=AssertionError), \
             patch.object(zipfile.ZipFile, 'extractall', side_effect=AssertionError):
            result = self.read(raw)
        self.assertEqual(result['missing'], [])
        self.assertEqual(set(result['records']), set(subject.RECORDS))

    def test_missing_receipt_is_explicit_not_an_empty_success(self):
        raw = self.pack({'decision.json': b'{}', 'post-merge-manual.json': b'{}'})
        self.assertEqual(self.read(raw)['missing'], ['auto-merge-result.json'])

    def test_digest_mismatch_refused(self):
        raw = self.pack()
        self.artifact['digest'] = 'sha256:' + '0' * 64
        with self.assertRaisesRegex(ValueError, 'digest'): self.read(raw)

    def test_wrong_attempt_expired_or_wrong_name_refused(self):
        for key, value in [('name', 'protocol-b-123-1'), ('expired', True), ('name', 'lookalike')]:
            with self.subTest(key=key), patch.dict(self.artifact, {key:value}):
                raw = self.pack()
                with self.assertRaises(ValueError): self.read(raw)

    def test_wrong_run_repository_or_source_refused(self):
        for key, value in [('id', 124), ('repository_id', 8), ('head_sha', 'b' * 40)]:
            with self.subTest(key=key), patch.dict(self.artifact['workflow_run'], {key:value}):
                raw = self.pack()
                with self.assertRaisesRegex(ValueError, 'source'): self.read(raw)

    def test_duplicate_critical_record_refused(self):
        out = io.BytesIO(self.pack())
        with warnings.catch_warnings():
            warnings.simplefilter('ignore', UserWarning)
            with zipfile.ZipFile(out, 'a') as archive: archive.writestr('decision.json', b'{}')
        raw = out.getvalue()
        self.artifact.update(size_in_bytes=len(raw), digest='sha256:' + hashlib.sha256(raw).hexdigest())
        with self.assertRaisesRegex(ValueError, 'duplicate'): self.read(raw)

    def test_path_lookalike_never_used_or_extracted(self):
        raw = self.pack({'../decision.json': b'{}', '/decision.json': b'{}'})
        self.assertEqual(self.read(raw)['missing'], list(subject.RECORDS))

    def test_invalid_json_nonobject_and_oversized_record_refused(self):
        for data in [b'{', b'[]', b'x' * 129]:
            with self.subTest(data=data[:10]), patch.object(subject, 'MAX_RECORD', 128):
                with self.assertRaises(ValueError): self.read(self.pack({'decision.json':data}))

    def test_empty_or_oversized_archive_refused(self):
        for raw in [b'', b'x' * 129]:
            with patch.object(subject, 'MAX_ZIP', 128):
                with self.assertRaisesRegex(ValueError, 'archive size'): self.read(raw)


if __name__ == '__main__': unittest.main()
