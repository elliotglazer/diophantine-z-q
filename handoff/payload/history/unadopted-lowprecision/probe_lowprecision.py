"""Produce the fixed low-precision circuit packet. Root dispatches execution."""
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import sys
from lowprecision_kernel import coefficients, emit_g, profiles, profile_name

sys.dont_write_bytecode = True
BUILDER_SHA = 'c7ef798894a106e3c6b02816583be2b6e966e4e701f73ee670c9a0de52a70912'


def encode(expression):
    return [{'coefficient': [c.numerator, c.denominator], 'monomial': list(mon)}
            for mon, c in sorted(expression.d.items())]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--builder', type=Path, required=True)
    parser.add_argument('--out', type=Path, required=True)
    args = parser.parse_args()
    assert hashlib.sha256(args.builder.read_bytes()).hexdigest() == BUILDER_SHA
    assert not args.out.exists()
    spec = importlib.util.spec_from_file_location('lowprecision_frozen_builder', args.builder)
    b = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(b)
    b.CURVE_DROOT = (3, -1)
    b.CURVE_D2 = (11, -6)
    args.out.mkdir(parents=True)
    entries = []
    for profile in profiles():
        precision, scheme, normalization, scale, bound = profile
        name = profile_name(profile)
        m = b.M(name[:-5], 2)
        output = emit_g(b, b.Field(m), (b.P.v(0), b.P.v(1)), precision,
                        bind_output=bound, hscale=scale, scheme=scheme, normalization=normalization)
        count = m.count
        assert len(m.rows) == count-2
        assert all(len(mon) <= 2 for row in m.rows for _, mon in row)
        assert all(len(mon) <= 2 for expression in output for mon in expression.d)
        # Add the actual shape of the later field-product equality. This
        # catches output denominators absent from a direct circuit's rows.
        left = (b.P.v(count), b.P.v(count+1))
        right = (b.P.v(count+2), b.P.v(count+3))
        product = b.raw_fmul(left, right)
        fusion = [(p-g).row() for p, g in zip(product, output)]
        data = {'kind': 'lowprecision-reciprocal-G/v1', 'precision': precision,
                'input_count': 2, 'targets': list(range(2, count)),
                'scheme': scheme, 'normalization': normalization, 'hscale': scale,
                'bound_output': bound, 'coefficient_list': [str(c) for c in coefficients(precision//4)],
                'rows': m.rows, 'outputs': [encode(g) for g in output],
                'fusion_variables': list(range(count, count+4)), 'fusion_rows': fusion}
        content = (json.dumps(data, sort_keys=True, separators=(',', ':'))+'\n').encode('ascii')
        (args.out/name).write_bytes(content)
        entries.append({'file': name, 'sha256': hashlib.sha256(content).hexdigest(),
                        'targets': count-2})
    (args.out/'index.json').write_text(json.dumps(entries, indent=2)+'\n')
    print(json.dumps({'status': 'UNVERIFIED CIRCUIT PACKET', 'cases': len(entries),
                      'output': str(args.out), 'source_arithmetic_accepted': False}, indent=2))


if __name__ == '__main__':
    main()
