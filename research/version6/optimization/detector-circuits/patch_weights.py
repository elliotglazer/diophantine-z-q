"""Optional detector weight redesign, independent of basic detector patch."""
from pathlib import Path

def patch(text):
    start=text.index(" let fi=inv('detector'+r+'.FInverse'")
    end=text.index(" let e2=rsq('detector'+r+'.e2'",start)
    return text[:start]+''' let fi=inv('detector'+r+'.FInverse',Fv);
 let a5=rp('detector'+r+'.scalePower5',A,5),d2=rsq('detector'+r+'.deltaSquare',delta);
 let q1=rquot('detector'+r+'.q1',mul(a5,d2),Fv,'existing_F_inverse');
 let d3=rm('detector'+r+'.deltaCube',d2,delta),ep=rm('detector'+r+'.eWeight',q1,d3);
 let Rv=inv('detector'+r+'.R',rm('detector'+r+'.Rdenominator',ep,delta));
'''+text[end:]

if __name__=='__main__':
    here=Path(__file__).resolve().parent
    import argparse
    p=argparse.ArgumentParser();p.add_argument('input',type=Path);p.add_argument('output',type=Path);a=p.parse_args()
    a.output.write_text(patch(a.input.read_text()))
