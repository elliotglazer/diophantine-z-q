# Version 6 release verification

The [Version 6 release](https://github.com/elliotglazer/diophantine-z-q/releases/tag/quartic-962-version-6) is pinned to public source snapshot `a9e834bac43b17e3f8415791f4adbd904f686b9d`. Its manuscript, polynomial, inventory and handoffs come from that snapshot. This directory records the later publication checks and is not part of the archives it identifies.

Both archives passed whole-file and member verification. The current-only handoff passed authenticated extraction, all 14 polynomial checks, inventory validation and 25 adversarial inventory tests. `PUBLICATION.json` records asset hashes checked against GitHub's server digests. `CI.json` records the successful Linux research and complete manuscript-integration workflows.

The manuscript retains the original construction and the fully expanded Version 4 quartic, adds the 962-variable quartic and degree-four lower bound, and proves the required Gaussian ray-field result without assuming Frei–Tinková's theorem. The source inventory preserves the exact scope and source-version qualifications. These are informal mathematical reviews and finite checks, not completed Lean verification or independent human peer review.
