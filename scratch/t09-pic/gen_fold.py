"""Regenerate FoldCheck.lean from Pic.lean: import TailZ19 instead of TailB, drop the #print lines,
append the fold section kept in fold_section.lean."""
src = open('scratch/t09-pic/Pic.lean').read()
body = src.replace("import ZInQKernel.OneProof.H.TailB\n", "import ZInQKernel.OneProof.H.TailZ19\n", 1)
body = body[:body.index("#print axioms")]
fold = open('scratch/t09-pic/fold_section.lean').read()
open('scratch/t09-pic/FoldCheck.lean', 'w').write(
    "-- GENERATED from Pic.lean by scratch/t09-pic/gen_fold.py (import TailZ19 instead of TailB) + fold section.\n"
    + body + fold)
