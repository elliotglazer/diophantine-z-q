"""Share q1*e6 between q16 and q52 without changing any weight domains."""
from pathlib import Path
def patch(text):
    old="let q16=rm('detector'+r+'.q16',q1,rm('detector'+r+'.e30',e24,e6)),q52=rm('detector'+r+'.q52',q1,rm('detector'+r+'.e102',e96,e6));"
    new="let common=rm('detector'+r+'.q1e6',q1,e6),q16=rm('detector'+r+'.q16',common,e24),q52=rm('detector'+r+'.q52',common,e96);"
    assert old in text
    return text.replace(old,new)
if __name__=='__main__':
    import argparse
    p=argparse.ArgumentParser();p.add_argument('input',type=Path);p.add_argument('output',type=Path);a=p.parse_args()
    a.output.write_text(patch(a.input.read_text()))
