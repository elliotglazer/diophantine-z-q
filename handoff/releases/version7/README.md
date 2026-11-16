# Version 7 publication record

The [public release](https://github.com/elliotglazer/diophantine-z-q/releases/tag/quartic-962-version-7) and [private release](https://github.com/elliotglazer/private-diophantine/releases/tag/quartic-962-version-7) contain the updated TeX, 252-page PDF, full research handoff and current-only handoff. The archives include the four Gaussian component audits and their integrated repairs. No conversational transcript is included.

The handoffs freeze public commit `00fee0fea917bda1140215624f2276db9a410ed4`. The private release tag freezes `f815d11e6ddf1443cfc9c9517dc44191085b0e5b`, which retains private-only research. Both releases carry identical public-source artifacts. These publication receipts were committed afterward and are not part of the frozen snapshot.

| Archive | Bytes | SHA-256 |
| --- | ---: | --- |
| `z-in-q-version7-full-handoff.zip` | 502942588 | `0f0374d7faff85a0bc62db1b61a44340ce3fa1171377b20a190fcea8eff5b2d8` |
| `z-in-q-version7-current-handoff.zip` | 62607372 | `18387d52201abffa456049922198b87c02d2df888738877e175df3e6596c858d` |

`BUILD_RECEIPT.json` records every-member integrity checks. `EXTRACTED_REPLAY.json` records authenticated extraction and the full fourteen-stage polynomial reproduction from the extracted tree. `EXTRACTED_INVENTORY.json` records source binding and 25 adversarial inventory tests. `HANDOFF_TESTS_FINAL.json` records the 120 archive and release checks. `ASSET_VERIFICATION.json` records the exact tags and GitHub-reported SHA-256 digests for all uploaded assets.

The public Version 7 integration workflow passed all jobs, including the historical 4,973-variable reproduction. The corresponding private job stopped before reproduction because its runner lacked the required 8 GiB of available memory. Its memory guard was preserved; the other private integration jobs passed. `CI_STATUS.json` records the observed workflow states, including later replay-tool checks.

After the filename and folder cleanup, the renamed manuscript built successfully in both repositories. The final source Research checks also passed in both repositories, including the historical inventory tests through their relocation adapter. Release-tag pushes started additional copies of the same checks, which may still be running in the recorded snapshot.

The audits are internal model reviews with the source-version qualifications recorded in the manuscript and inventory. These release and finite-computation checks do not constitute a formal proof or external human validation.
