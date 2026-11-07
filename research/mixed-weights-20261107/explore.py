"""Eight-gate mixed detector weights, atop the separate direct-target candidate."""
import argparse
import importlib.util
import sys
from pathlib import Path
ROOT = Path(__file__).resolve().parents[2]
spec = importlib.util.spec_from_file_location('direct', ROOT/'research/overnight-20261106/unit_target.py')
direct = importlib.util.module_from_spec(spec)
spec.loader.exec_module(direct)
v = direct.v
TARGET_SHIFT = 1

def mixed_weights(source, level):
    source = (direct.direct_targets if TARGET_SHIFT == 1 else direct.original)(source, level)
    start = source.index(" let e2=rsq('detector'+r+'.e2'")
    end = source.index(" let w=fmul('detector'+r+'.W'", start)
    return source[:start] + """ let e2=rsq('detector'+r+'.e2',ep),e4=rsq('detector'+r+'.e4',e2),e8=rsq('detector'+r+'.e8',e4),e16=rsq('detector'+r+'.e16',e8);
 let e30=rquot('detector'+r+'.e30',sq(e16),e2,'norm_equation_forces_nonzero_weight'),e60=rsq('detector'+r+'.e60',e30);
 let q12=rquot('detector'+r+'.q12',mul(q1,e30),e8,'norm_equation_forces_nonzero_weight'),q40=rquot('detector'+r+'.q40',mul(q12,e60),e4,'norm_equation_forces_nonzero_weight');
""" + source[end:]

if __name__ == '__main__':
    parser = argparse.ArgumentParser(add_help=False)
    parser.add_argument('--target-shift', type=int, choices=(1,2), default=1)
    options, rest = parser.parse_known_args()
    TARGET_SHIFT = options.target_shift
    sys.argv = [sys.argv[0]] + rest
    v.variant = mixed_weights
    v.main()
