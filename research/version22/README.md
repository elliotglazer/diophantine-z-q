# Version 22 preparation

This draft adopts Jose Brox's explicit 175-variable quartic from the contribution note merged in PR175 at `dda0439aa44a63a05d4ef7c58230caed6df8e628`. The contribution was merged on an owner override; that was not acceptance of a new record. Version 21 remains the published release until this version completes the release policy.

The new manuscript prints all 147 quadratic rows and their direct field-coordinate interpretation. Their squared sum has 3,196 monomials, content one, coefficient bound `< 2^802`, and a 73,080-byte decimal expression. Counts include the rational input. The retained 195-variable Busy Beaver polynomial remains in the body as an earlier construction, rather than as a competing record.

The main new arithmetic is the application of Bhargava–Burungale arXiv:2611.16130v2, Theorem 2.3 through native pole equations; the projective ten-contact height estimate; the scalar 331 anchor; and their simultaneous completeness. The draft treats midpoint, zero auxiliary and finite torsion cases. [DEPENDENCIES.md](DEPENDENCIES.md) identifies the sources and consumers. [ARITHMETIC-AUDIT.md](ARITHMETIC-AUDIT.md) distinguishes this author's checks from external theorem assumptions and independent acceptance.

Reproduce finite checks from the repository root:

```sh
python -B research/version22/construction/check.py
python -B research/version21/construction/check.py
```

The first command parses all 147 rows printed in the actual TeX, checks their direct interpretation independently of the historical compiler chain, expands them exactly, reconstructs the canonical decimal expression, and checks the contact and scalar constants. It reads contributor data but does not run contributor programs. The second replays the retained finite checks. These checks do not certify the arithmetic proof.

The PDF is built by the serial procedure recorded in BUILD.json. All released manuscripts and research folders remain unchanged. No workflow, script under scripts/, kernel contract, or file owned by gate PR176/177 is edited. CI registration of this new checker is a separate follow-up. A new independent builder-binding review, protected gate acceptance and exact-head release approval remain necessary. The author does not issue these approvals.

The `builder_sha256` in BUILD.json identifies
`research/version18/build_pdf.py`, the serial release-PDF builder.
It does not identify `scripts/build_paper.py`, the CI selection/rebuild
program separately pinned by the non-author builder-binding review.

Claude Fable 5.2 reviewed head a735f6b within the scopes of the three
preserved reports under reviews/. No blocking error was found within
those scopes. The revised head needs the final source/PDF binding;
the earlier verdict is not automatically acceptance of these repairs.
