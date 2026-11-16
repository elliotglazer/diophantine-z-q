"""Independent exact polynomial checker for the 44 low-precision circuits.

Imports neither the producer, its kernel, nor the frozen source builder.
Derives coefficients by binomial convolution and checks a generic final
field-product equality as well as the internal circuit rows.
"""
import argparse
from copy import deepcopy
from fractions import Fraction as F
import hashlib
import json
from math import comb, gcd, lcm
from pathlib import Path

if not __debug__:
    raise RuntimeError('Keep assertion checks enabled; do not use python -O')


def add(*parts):
    result = {}
    for scalar, poly in parts:
        for mon, coefficient in poly.items():
            result[mon] = result.get(mon, F(0))+scalar*coefficient
    return {mon: coefficient for mon, coefficient in result.items() if coefficient}


def mul(left, right):
    result = {}
    for a, c in left.items():
        for b, d in right.items():
            mon = tuple(sorted(a+b))
            result[mon] = result.get(mon, F(0))+c*d
    return {mon: coefficient for mon, coefficient in result.items() if coefficient}


def field_product(left, right):
    return (add((1, mul(left[0], right[0])), (2, mul(left[1], right[1]))),
            add((1, mul(left[0], right[1])), (1, mul(left[1], right[0]))))


def variable(v):
    return {(v,): F(1)}


def normalize(poly):
    if not poly:
        return ()
    denominator = lcm(*(c.denominator for c in poly.values()))
    integers = {mon: int(c*denominator) for mon, c in poly.items()}
    factor = gcd(*integers.values())
    if integers[min(integers)] < 0:
        factor = -factor
    return tuple(sorted((mon, c//factor) for mon, c in integers.items()))


def monomial(data, limit):
    assert type(data) is list
    assert all(type(v) is int and 0 <= v < limit for v in data)
    mon = tuple(data)
    assert mon == tuple(sorted(mon)) and len(mon) <= 2
    return mon


def decode_row(data, limit):
    assert type(data) is list
    result = {}
    for coefficient, variables in data:
        assert type(coefficient) is int and coefficient != 0
        mon = monomial(variables, limit)
        assert mon not in result
        result[mon] = F(coefficient)
    return result


def decode_output(data, limit):
    assert type(data) is list
    result = {}
    for term in data:
        assert type(term) is dict and set(term) == {'coefficient', 'monomial'}
        numerator, denominator = term['coefficient']
        assert type(numerator) is int and numerator != 0
        assert type(denominator) is int and denominator > 0
        mon = monomial(term['monomial'], limit)
        assert mon not in result
        result[mon] = F(numerator, denominator)
    return result


def substitute(poly, env):
    result = {}
    for mon, coefficient in poly.items():
        term = {(): coefficient}
        for v in mon:
            assert v in env
            term = mul(term, env[v])
        result = add((1, result), (1, term))
    return result


def coefficients(count):
    # sqrt(1-w) * integral_0^1 (1-w*t^4)^(-1/2) dt.
    root = [F(1)]
    for j in range(1, count):
        root.append(root[-1]*(F(j-1)-F(1, 2))/j)
    integral = [F(comb(2*j, j), 4**j*(4*j+1)) for j in range(count)]
    return [sum((root[i]*integral[j-i] for i in range(j+1)), F(0)) for j in range(count)]


def contract():
    result = {}
    def insert(precision, scheme, normalization, scale, bound, targets):
        name = f'g{precision}-{scheme}-{normalization}-s{scale}-'+('bound' if bound else 'direct')+'.json'
        result[name] = (precision, scheme, normalization, scale, bound, targets)
    for bound in (False, True):
        insert(12, 'direct', 'unit', 1, bound, 2+2*bound)
    for precision in (40, 44, 48):
        for normalization in ('a3', 'a6'):
            for scale in (1, 2):
                for bound in (False, True):
                    insert(precision, 'block3', normalization, scale, bound,
                           (8 if precision == 40 else 10)+2*bound)
        scheme = 'powers45' if precision in (40, 44) else 'powers56'
        for normalization in ('unit', 'coefficient', 'reciprocal_denominator'):
            for bound in (False, True):
                insert(precision, scheme, normalization, 1, bound,
                       (8 if precision in (40, 44) else 10)+2*bound)
    assert len(result) == 44
    return result


def validate(data, expected):
    precision, scheme, normalization, scale, bound, count = expected
    assert type(data) is dict and data['kind'] == 'lowprecision-reciprocal-G/v1'
    assert type(data['precision']) is int and data['precision'] == precision
    assert type(data['input_count']) is int and data['input_count'] == 2
    assert data['scheme'] == scheme and data['normalization'] == normalization
    assert type(data['hscale']) is int and data['hscale'] == scale
    assert type(data['bound_output']) is bool and data['bound_output'] == bound
    targets = data['targets']
    assert type(targets) is list and all(type(v) is int for v in targets)
    assert targets == list(range(2, 2+count))
    assert len(data['rows']) == count
    independent = coefficients(precision//4)
    assert data['coefficient_list'] == [str(c) for c in independent]
    env = {0: variable(0), 1: variable(1)}
    rows = []
    for target, encoded in zip(targets, data['rows']):
        row = decode_row(encoded, target+1)
        coefficient = row.get((target,), F(0))
        assert coefficient
        rhs = {mon: -c/coefficient for mon, c in row.items() if mon != (target,)}
        assert all(target not in mon for mon in rhs)
        env[target] = substitute(rhs, env)
        rows.append(row)
    assert len(data['outputs']) == 2
    outputs = [decode_output(output, count+2) for output in data['outputs']]
    if bound:
        assert outputs == [variable(count), variable(count+1)]
    actual = [substitute(output, env) for output in outputs]
    w = field_product(({(): F(11)}, {(): F(-6)}), field_product((env[0], env[1]), (env[0], env[1])))
    power, wanted = ({(): F(1)}, {}), ({}, {})
    for coefficient in independent:
        wanted = tuple(add((1, current), (coefficient, term)) for current, term in zip(wanted, power))
        power = field_product(power, w)
    assert tuple(actual) == wanted
    ids = data['fusion_variables']
    assert type(ids) is list and all(type(v) is int for v in ids)
    assert ids == list(range(count+2, count+6))
    expected_product = field_product((variable(ids[0]), variable(ids[1])),
                                     (variable(ids[2]), variable(ids[3])))
    assert len(data['fusion_rows']) == 2
    fusion = [decode_row(encoded, count+6) for encoded in data['fusion_rows']]
    for row, product, output in zip(fusion, expected_product, outputs):
        assert normalize(row) == normalize(add((1, product), (-1, output)))
    def expansion_report(items):
        expanded = {}
        for row in items:
            expanded = add((1, expanded), (1, mul(row, row)))
        maximum = max((abs(c) for c in expanded.values()), default=F(0))
        assert maximum.denominator == 1
        return {'monomials': len(expanded), 'max_abs_coefficient': str(maximum.numerator),
                'coefficient_bits': maximum.numerator.bit_length(), 'below_2_80': maximum < 2**80}
    return {'status': 'EXACT IDENTITY VERIFIED', 'precision': precision, 'scheme': scheme,
            'normalization': normalization, 'hscale': scale, 'bound_output': bound,
            'rational_targets': count, 'isolated_rows': len(rows),
            'internal': expansion_report(rows), 'with_generic_field_product': expansion_report(rows+fusion),
            'scope': 'Isolated G circuit and generic product equality only; no source or arithmetic acceptance'}


def verify_packet(index, contents):
    wanted = contract()
    assert type(index) is list and len(index) == len(wanted)
    seen, entries = set(), []
    for entry in index:
        assert type(entry) is dict and set(entry) == {'file', 'sha256', 'targets'}
        name = entry['file']
        assert type(name) is str and name in wanted and name not in seen
        seen.add(name)
        assert type(entry['targets']) is int and entry['targets'] == wanted[name][-1]
        assert type(entry['sha256']) is str and len(entry['sha256']) == 64
        content = contents[name]
        assert type(content) is bytes and hashlib.sha256(content).hexdigest() == entry['sha256']
        data = json.loads(content)
        entries.append((name, data, wanted[name]))
    assert seen == set(wanted)
    return entries


def malformed_circuits(data, expected):
    tests = []
    def change(name, edit):
        bad = deepcopy(data)
        edit(bad)
        tests.append((name, bad))
    change('wrong precision', lambda d: d.update(precision=64))
    change('wrong coefficient', lambda d: d['coefficient_list'].__setitem__(-1, '0'))
    change('overwrite input', lambda d: d['targets'].__setitem__(0, 0))
    change('missing definition', lambda d: d['rows'].pop())
    change('changed defining coefficient', lambda d: d['rows'][0][0].__setitem__(0, d['rows'][0][0][0]+1))
    change('duplicate monomial', lambda d: d['rows'][0].append(deepcopy(d['rows'][0][0])))
    change('cubic definition', lambda d: d['rows'][0].append([1, [0, 0, 0]]))
    change('future dependency', lambda d: d['rows'][0].append([1, [999999]]))
    change('wrong output', lambda d: d['outputs'][0][0]['coefficient'].__setitem__(0, d['outputs'][0][0]['coefficient'][0]+1))
    change('negative denominator', lambda d: d['outputs'][0][0]['coefficient'].__setitem__(1, -1))
    change('negative coordinate', lambda d: d['outputs'][0].append({'coefficient': [1, 1], 'monomial': [-1]}))
    change('swap components', lambda d: d['outputs'].reverse())
    change('wrong fusion variable', lambda d: d['fusion_variables'].__setitem__(0, 0))
    change('missing fusion row', lambda d: d['fusion_rows'].pop())
    change('changed fusion row', lambda d: d['fusion_rows'][0][0].__setitem__(0, d['fusion_rows'][0][0][0]+1))
    rejected = []
    for name, bad in tests:
        try:
            validate(bad, expected)
        except (AssertionError, ValueError, TypeError, KeyError, ZeroDivisionError):
            rejected.append(name)
        else:
            raise AssertionError('Malformed circuit accepted: '+name)
    return rejected


def malformed_packets(index, contents):
    tests = [('empty packet', [], contents), ('missing case', index[:-1], contents)]
    bad = deepcopy(index); bad[-1] = deepcopy(bad[0]); tests.append(('duplicate case', bad, contents))
    bad = deepcopy(index); bad[0]['file'] = '../escape.json'; tests.append(('unknown filename', bad, contents))
    bad = deepcopy(index); bad[0]['sha256'] = '0'*64; tests.append(('wrong digest', bad, contents))
    bad = deepcopy(index); bad[0]['targets'] += 2; tests.append(('wrong target count', bad, contents))
    changed = dict(contents); changed[index[0]['file']] += b' '; tests.append(('changed bytes', index, changed))
    rejected = []
    for name, bad, files in tests:
        try:
            verify_packet(bad, files)
        except (AssertionError, ValueError, TypeError, KeyError):
            rejected.append(name)
        else:
            raise AssertionError('Malformed packet accepted: '+name)
    return rejected


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('directory', type=Path)
    args = parser.parse_args()
    index = json.loads((args.directory/'index.json').read_bytes())
    contents = {name: (args.directory/name).read_bytes() for name in contract()}
    entries = verify_packet(index, contents)
    reports = []
    for name, data, expected in entries:
        report = validate(data, expected)
        report['file'] = name
        report['sha256'] = hashlib.sha256(contents[name]).hexdigest()
        report['malformed_circuits_rejected'] = malformed_circuits(data, expected)
        reports.append(report)
    summary = {'status': 'PASS', 'cases': len(reports),
               'malformed_packets_rejected': malformed_packets(index, contents),
               'best_with_generic_product': {}}
    for precision in (12, 40, 44, 48):
        eligible = [r for r in reports if r['precision'] == precision and r['with_generic_field_product']['below_2_80']]
        best = min(eligible, key=lambda r: (r['rational_targets'], int(r['with_generic_field_product']['max_abs_coefficient']), r['file'])) if eligible else None
        summary['best_with_generic_product'][str(precision)] = best
    (args.directory/'independent-check.json').write_text(json.dumps(reports, indent=2)+'\n')
    (args.directory/'independent-summary.json').write_text(json.dumps(summary, indent=2)+'\n')
    print(json.dumps(summary, indent=2))


if __name__ == '__main__':
    main()
