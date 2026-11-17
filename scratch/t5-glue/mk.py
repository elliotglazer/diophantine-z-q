#!/usr/bin/env python3
"""Assemble T5Glue.lean = kernel imports + Elliptic.lean body + parts/*.lean (in order)."""
import sys, os
here = os.path.dirname(os.path.abspath(__file__))
ell = open(os.path.join(here, 'Elliptic.lean')).read()
# drop the `import Mathlib` line and the module docstring of Elliptic.lean
body = ell.split('\n', 1)[1]
i = body.index('-/') + 2
body = body[i:]
fld = open(os.path.join(here, 'Field.lean')).read()
fbody = fld.split('\n', 1)[1]
fbody = fbody[fbody.index('-/') + 2:]
dsc = open(os.path.join(here, 'Disc.lean')).read()
dbody = dsc.split('\n', 1)[1]
dbody = dbody[dbody.index('-/') + 2:]
header = open(os.path.join(here, 'parts', 'Header.lean')).read()
parts = ['X0.lean', 'CM.lean', 'Heeg.lean', 'LatHat.lean', 'Strong.lean', 'Artin.lean', 'AbsArtin.lean', 'Colon.lean', 'Scale.lean', 'Invert.lean', 'Row.lean', 'Closed.lean', 'Footer.lean']
out = header + '\n-- ===== Elliptic.lean body (verbatim) =====\n' + body + '\n-- ===== Field.lean body (verbatim) =====\n' + fbody + '\n-- ===== Disc.lean body (verbatim) =====\n' + dbody
for p in parts:
    fp = os.path.join(here, 'parts', p)
    if os.path.exists(fp):
        out += '\n-- ===== parts/' + p + ' =====\n' + open(fp).read()
open(os.path.join(here, 'T5Glue.lean'), 'w').write(out)
print('wrote T5Glue.lean', len(out.splitlines()), 'lines')
# Headline variant: same body over the kernel's one-proof theorem
hh = open(os.path.join(here, 'parts', 'HeadlineHeader.lean')).read()
hb = out.split('\n-- ===== Elliptic.lean body (verbatim) =====\n', 1)[1]
hb = hb.split('\n-- ===== parts/Footer.lean =====\n', 1)[0]
hout = hh + '\n-- ===== Elliptic.lean body (verbatim) =====\n' + hb + '\n-- ===== parts/Headline.lean =====\n' + open(os.path.join(here, 'parts', 'Headline.lean')).read()
open(os.path.join(here, 'T5Headline.lean'), 'w').write(hout)
print('wrote T5Headline.lean', len(hout.splitlines()), 'lines')
