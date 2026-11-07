"""Isolated scaled-norm experiment on the 900-variable candidate."""
import importlib.util
from pathlib import Path
ROOT=Path(__file__).resolve().parents[2]
spec=importlib.util.spec_from_file_location('mixed',ROOT/'research/mixed-weights-20261107/explore.py')
mixed=importlib.util.module_from_spec(spec);spec.loader.exec_module(mixed)

def scaled_norm(source,level):
    source=mixed.mixed_weights(source,level)
    old="let wi=inv('detector'+r+'.w0Inverse',w[0]),nw=rquot('detector'+r+'.normOver2w0',scale(sub(sq(w[0]),scale(sq(w[1]),2)),Q(1,2)),w[0],'retained_w0Inverse'),eDelta=rm('detector'+r+'.eDelta',ep,delta),bv=rquot('detector'+r+'.B',sq(nw),eDelta,'retained_w0_inverse_and_nonsquare_two_force_nonzero_norm');"
    new="let wi=inv('detector'+r+'.w0Inverse',w[0]),wd2=rm('detector'+r+'.w0Delta2',w[0],delta2),nw=rquot('detector'+r+'.scaledNorm',scale(sub(sq(w[0]),scale(sq(w[1]),2)),Q(1,2)),wd2,'retained_w0_inverse_and_norm_identity_force_nonzero_delta'),bv=rquot('detector'+r+'.B',sq(nw),q1,'scaled_norm_and_B_equation_force_nonzero_q1');"
    return mixed.v.h.replace_once(source,old,new)

if __name__=='__main__':
    mixed.v.variant=scaled_norm
    mixed.v.main()
