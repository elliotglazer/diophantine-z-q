# Frozen 962-coordinate quartic

This package specifies an integer polynomial of degree four with 962 active rational coordinates, including its unchanged input coordinate. Its rational zero projection equals the frozen 1,272-variable baseline. The separate claim that this projection equals the integers retains the baseline arithmetic qualifications, including the current Frei–Tinková input. This package is not a publication approval.

The polynomial has 55,409 monomials, primitive coefficient content one, and maximum coefficient magnitude 64*S², where S=3^(2^27) is a fixed integer coefficient. The raw system has 994 coordinates and 951 quadratic residuals. The compiler removes 32 coordinates, leaving 962 coordinates and 919 quadratic residuals. There are 961 existential witness coordinates in addition to the input.

`polynomial.json` is the complete coefficient table. `compiled-ir.json` and `reduction-certificate.json` provide the exact residual system and reversible elimination certificate. `PROOF.md` proves the rational witness maps for every change. The evidence directory records independent checks and component proofs. `MANIFEST.json` hashes every packaged file except itself.

Reproduce in a fresh temporary directory with Python 3 and Node:

    python reproduce.py --node /path/to/node

No nonstandard Python or Node library is needed. The script validates package integrity, regenerates both raw systems and the complete table, independently replays every gate and compiler operation, and compares seven deterministic artifacts byte for byte. S is never expanded into decimal digits.

The producer, compiler, checker, source text and evidence are bundled. No production repository or network access is needed. The baseline builder and manifest are included for comparison; their own relative source paths are historical and they are not run during reproduction.
