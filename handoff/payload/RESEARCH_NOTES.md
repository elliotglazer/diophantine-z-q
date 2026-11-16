# Version 7 research guide

Contributors: Stefan Baranczuk, Jose Brox, Gabe Conant, Sohail Farhangi, James Freitag, Elliot Glazer, Jennifer Park, and Caroline Terry.

Start with `current/manuscripts/quartic_v7.pdf`, its TeX source, and `current/docs/quartic-962/README.md`. The source inventory records the current theorem applications and review scope. `current/docs/quartic-962-validation/` contains the independent release reviews.

The exact finite construction is in `current/quartics/quartic-962/`. Its table has 962 coordinates including the input, 919 quadratic residuals before the sum of squares, and 55,409 quartic monomials. The package preserves the reviewed transformation evidence and a pinned link to the Version 5 construction. Run `python scripts/check_quartic962.py --out NEW_DIRECTORY` from `current/`, keeping the output directory outside the extracted snapshot. Python 3.10+ and Node.js 18+ are required.

`current/research/version6/lower-bound/` contains the lower-bound audit. `current/research/version6/optimization/` contains the path to the 962-coordinate construction, including alternatives and reviews. `current/research/version6/analytic-proof/` contains the analytic replacement proof work and its source audits. The frozen research manifest records all inclusions, exclusions and canonical-package mappings.

Earlier constructions remain at their existing repository paths. The unchanged Version 6 full archive supplies the previous handoff inventory and its nested revision-2 archive. Their `current/` directories describe their historical snapshots, not Version 7.

The release's finite computation and the manuscript's arithmetic argument have separate review records. Read the current source contract and independent reviews for the precise scope of each result. The main Lean theorem remains unproved; retained helper formalizations do not change that status.

Version 7 adds the four Gaussian audits and exact repairs under `docs/quartic-962/evidence/gaussian-four-audit-20261106/`, with an overview in `research/version7/README.md`. `V6_RESEARCH_MANIFEST.json` continues to describe the unchanged Version 6 research collection; `V7_AUDIT_MANIFEST.json` binds the new audit collection.
