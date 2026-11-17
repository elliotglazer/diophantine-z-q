"""Tests for sync_claims.py: fixtures only, no network.

Run from the repository root: python3 -I -m unittest discover -s scripts/claims -p 'test_*.py'
"""
import contextlib
import datetime
import io
import json
import os
import shutil
import subprocess
import sys
import tempfile
import unittest
from unittest import mock

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import sync_claims as sc  # noqa: E402

FX = os.path.join(HERE, 'fixtures')
LIVE = os.path.join(FX, 'live.json')
OPEN = os.path.join(FX, 'open-statements.json')
CROSSWALK = os.path.join(FX, 'frontier-crosswalk.tsv')
KINDS = os.path.join(FX, 'kinds.tsv')
CLAIMS = os.path.join(FX, 'claims.tsv')
NO_ISSUES = os.path.join(FX, 'no-such-issues.json')
FORK14 = 'https://github.com/Deicyde/diophantine-z-q/issues/14'
UP = 'https://github.com/elliotglazer/diophantine-z-q/issues/'
BATCH2 = ['mumfordTorsionAlgClosed', 'mulEtaleAbelianScheme', 'cartierSmooth', 'geomConnOfRationalPoint',
          'groupSchemeEquidim', 'uniformizationLeafAll', 'gagaMorphism', 'igusaGL2', 'regularSmoothPerfect',
          'shimuraGoodReductionNoGuard', 'tateTwistInvariants', 'axSenTate', 'geomConnOfAlgClosure']


def run(*args, claims=CLAIMS, kinds=KINDS, crosswalk=CROSSWALK, live=LIVE):
    argv = ['--from-json', live, '--claims', claims, '--kinds', kinds, '--open', OPEN,
            '--crosswalk', crosswalk, '--issues', NO_ISSUES] + list(args)
    buf = io.StringIO()
    with contextlib.redirect_stdout(buf):
        code = sc.main(argv)
    return code, buf.getvalue()


def read_json(path):
    with open(path, encoding='utf-8') as fh:
        return json.load(fh)


def read_text(path):
    with open(path, encoding='utf-8') as fh:
        return fh.read()


def holds(crosswalk=CROSSWALK):
    fields = sc.Fields(OPEN, crosswalk, KINDS)
    threads = sc.load_threads(read_json(LIVE))
    events, unmatched, _ = sc.parse_events(threads, fields)
    return sc.compute_holds(events), unmatched


def active(st):
    return {(s, k) for (s, k), h in st.items() if h['active']}


class Parsing(unittest.TestCase):
    def setUp(self):
        self.fields = sc.Fields(OPEN, CROSSWALK, KINDS)

    def names(self, line):
        verb, rest = next(sc.parse_lines(line))
        return sc.names_in(sc.claim_parts(rest, self.fields)[0], self.fields)

    def test_single_claim(self):
        self.assertEqual(self.names('Claiming igusaPsi4 at 2171de2bc'), (['igusaPsi4'], []))

    def test_backticks(self):
        self.assertEqual(self.names('Claiming `igusaPsi4` at `2171de2bc`'), (['igusaPsi4'], []))

    def test_multiple_claims(self):
        found, bad = self.names('Claiming igusaChi10, `gagaMorphism` at 2171de2bc')
        self.assertCountEqual(found, ['igusaChi10', 'gagaMorphism'])
        self.assertEqual(bad, [])

    def test_frontier_ids_through_crosswalk(self):
        found, _ = self.names('Claiming H-70, H-71, H-72 again at the owner’s explicit request')
        self.assertEqual(found, ['homFreeFiniteAlgClosed', 'charPolyIndepOfEllAlgClosed', 'poincareComplement'])

    def test_ids_without_hyphen(self):
        self.assertEqual(self.names('Claiming H101')[0], ['mulEtaleAbelianScheme'])
        self.assertEqual(self.names('Claiming T1 and T3')[0], ['h11', 'h29'])

    def test_ranges(self):
        five = ['cartierSmooth', 'geomConnOfRationalPoint', 'groupSchemeEquidim', 'mulEtaleAbelianScheme',
                'mumfordTorsionAlgClosed']
        self.assertEqual(self.names('Claiming H98-H102'), (five, []))
        self.assertEqual(self.names('Claiming H-98-H-102 at abc1234'), (five, []))
        self.assertEqual(self.names('Claiming H-98–H-102'), (five, []))
        found, bad = self.names('Claiming H-102-H-98')
        self.assertEqual((found, bad), ([], [('H-102-H-98', 'range not supported')]))

    def test_slash_list_and_names_after_ids(self):
        self.assertEqual(self.names('Claiming H120/H121')[0], ['tateTwistInvariants', 'axSenTate'])
        self.assertEqual(self.names('Claiming H120 TateTwistInvariants and H121 AxSenTate.'),
                         (['tateTwistInvariants', 'axSenTate'], []))

    def test_dotted_name_is_not_an_id(self):
        self.assertEqual(self.names('Claiming AvSplit.T4.MulEtaleAbelianScheme'), (['mulEtaleAbelianScheme'], []))

    def test_leading_label_before_colon(self):
        self.assertEqual(self.names('Claiming W11: H120 TateTwistInvariants and H121 AxSenTate.')[0],
                         ['tateTwistInvariants', 'axSenTate'])
        self.assertEqual(self.names('Claiming lane G: H120 TateTwistInvariants and H121 AxSenTate.')[0],
                         ['tateTwistInvariants', 'axSenTate'])
        self.assertEqual(len(self.names('Claiming W16 H98-H102: MumfordTorsionAlgClosed first; later X')[0]), 5)

    def test_frontier_id_with_empty_field_uses_lean_name(self):
        # the crosswalk row H-5 has no field but lean_name 'r7a : PkgI2.NeronOggShafarevich'
        found, bad = self.names('Claiming the original H-5 and H-4 exact proof tasks again at x')
        self.assertEqual(found, ['r7a'])
        self.assertEqual([n for n, _ in bad], ['H-4'])

    def test_frontier_id_without_crosswalk_is_reported(self):
        fields = sc.Fields(OPEN, os.path.join(FX, 'no-such-crosswalk.tsv'), KINDS)
        found, bad = sc.names_in('H-70', fields)
        self.assertEqual(found, [])
        self.assertEqual(bad, [('H-70', 'frontier ID, and no crosswalk file to map it')])

    def test_lean_constant_names(self):
        self.assertEqual(self.names('Claiming `AvSplit.T4.MulEtaleAbelianScheme` at x')[0], ['mulEtaleAbelianScheme'])
        self.assertEqual(self.names('Claiming ShimuraSplit.GonzalezRotgerCountX6Ab')[0], ['gonzalezRotgerCountX6Ab'])
        self.assertEqual(self.names('Claiming `ZInQ.Contrib.HodgeSplit.BdRInvariants`')[0], ['bdRInvariants'])
        self.assertEqual(self.names('Claiming YuThm11')[0], ['yuThm11'])

    def test_unmatched_names_are_reported(self):
        found, bad = self.names('Claiming `ZInQ.HomLattice.NoSuchThing` and H-999 at 2171de2bc')
        self.assertEqual(found, [])
        self.assertEqual([n for n, _ in bad], ['ZInQ.HomLattice.NoSuchThing', 'H-999'])
        found, bad = self.names('Claiming H90 FiniteQuotientExists (then H91 TameQuotientSmooth after it)')
        self.assertEqual(found, [])
        self.assertEqual([n for n, _ in bad], ['H-90', 'H-91', 'FiniteQuotientExists', 'TameQuotientSmooth'])
        self.assertEqual(self.names('Claiming H117 via exact X0Transitive')[1],
                         [('X0Transitive', 'names no open field')])

    def test_html_markers_quotes_and_fences_ignored(self):
        self.assertEqual(list(sc.parse_lines('<!-- Claiming igusaPsi4 -->\nhello')), [])
        self.assertEqual(list(sc.parse_lines('> Claiming igusaPsi4\n  > Claiming igusaChi10')), [])
        self.assertEqual(list(sc.parse_lines('```\nClaiming igusaPsi4\n```\n~~~\nClaiming r9a\n~~~\nClaiming r9b')),
                         [('Claiming', 'r9b')])

    def test_release_progress_and_ping_lines(self):
        self.assertEqual(list(sc.parse_lines('Releasing gagaMorphism: needs GAGA\nProgress yuThm11: half done\n'
                                             'Ping (claim lapse): r9a')),
                         [('Releasing', 'gagaMorphism: needs GAGA'), ('Progress', 'yuThm11: half done'),
                          ('Ping', 'r9a')])
        self.assertEqual(sc.PING_TEXT.format(field='r9a'), 'Ping (claim lapse): r9a')


class Holds(unittest.TestCase):
    def setUp(self):
        self.st, self.unmatched = holds()

    def test_release_releases(self):
        self.assertIn(('igusaChi10', 'dave-ff'), active(self.st))
        h = self.st[('gagaMorphism', 'dave-ff')]
        self.assertFalse(h['active'])
        self.assertEqual(h['release']['blocker'], 'needs GAGA for proper morphisms, which Mathlib lacks')

    def test_last_action_wins(self):
        h = self.st[('yuThm11', 'erin-q')]
        self.assertTrue(h['active'])
        self.assertEqual(h['claim']['url'], FORK14 + '#issuecomment-1008')

    def test_project_claims_upstream(self):
        for f in ['homFreeFiniteAlgClosed', 'charPolyIndepOfEllAlgClosed', 'poincareComplement', 'r7a', 'h11',
                  'h29', 'egaIV_8_10_5_xii', 'neronSchemeExtensionExists'] + BATCH2:
            self.assertIn((f, 'project'), active(self.st), f)
        # the newest claim on #81 is the hold's claim
        self.assertTrue(self.st[('homFreeFiniteAlgClosed', 'project')]['claim']['url'].endswith('6885321564'))
        # named after the list of names: not claimed
        self.assertNotIn(('milneIsogenyQuasiInverse', 'project'), self.st)
        self.assertNotIn(('deligneComponentsX6PrintedAb', 'project'), self.st)

    def test_batch2_claim_lines(self):
        url = self.st[('cartierSmooth', 'project')]['claim']['url']
        self.assertEqual(url, UP + '81#issuecomment-6887798791')
        self.assertEqual(self.st[('axSenTate', 'project')]['claim']['url'], UP + '84#issuecomment-6887798335')
        self.assertEqual(self.st[('igusaGL2', 'project')]['claim']['url'], UP + '83#issuecomment-6887798638')
        bad = {u['name'] for u in self.unmatched if u['url'].startswith(UP + '79') or u['url'].startswith(UP + '83')}
        self.assertEqual(bad, {'H-90', 'H-91', 'FiniteQuotientExists', 'TameQuotientSmooth', 'X0Transitive'})

    def test_quoted_and_fenced_claims_do_not_count(self):
        self.assertNotIn(('igusaPsi4', 'project'), self.st)
        self.assertNotIn(('bostLowerBound', 'project'), self.st)

    def test_project_release_naming_a_holder(self):
        h = self.st[('thetaRatiosAlgebraic', 'pete-s')]
        self.assertFalse(h['active'])
        self.assertEqual(h['release']['blocker'], 'no reply within 7 days of the lapse ping')
        self.assertNotIn(('thetaRatiosAlgebraic', 'project'), self.st)

    def test_pr_claim_needs_link_to_14(self):
        self.assertIn(('javanpeykarBound', 'hana-dev'), active(self.st))
        self.assertNotIn(('bdRInvariants', 'lena-z'), active(self.st))

    def test_edited_claim_dates_from_the_edit(self):
        self.assertEqual(self.st[('phiAmpleIsogeny', 'sam-v')]['claim']['date'].strftime('%Y-%m-%d'), '2026-11-10')

    def test_reading_claim(self):
        self.assertIn(('reading R3', 'kim-l'), active(self.st))

    def test_logins(self):
        self.assertEqual(sc.kind_of('Deicyde'), 'project')
        self.assertEqual(sc.kind_of('deicyde'), 'project')
        self.assertEqual(sc.kind_of('ElliotGlazer'), 'maintainer')
        self.assertEqual(sc.kind_of('alice-nt'), 'outside')
        self.assertEqual(sc.holder_name('Deicyde'), 'project')
        self.assertEqual(sc.holder_name('elliotglazer'), 'elliotglazer')
        self.assertEqual(sc.holder_key('Alice-NT'), 'alice-nt')


class Report(unittest.TestCase):
    def test_report_rows(self):
        code, out = run('--today', '2026-11-14')
        self.assertEqual(code, 0)
        self.assertIn('igusaPsi4\toutside\talice-nt\theld\t2026-10-20\tDeicyde/diophantine-z-q#14\t'
                      + FORK14 + '#issuecomment-1001', out)
        self.assertIn('gonzalezRotgerCountX6Ab\tmaintainer\telliotglazer', out)
        self.assertIn('H-999\tfrontier ID not in the crosswalk\tfrank-x', out)
        self.assertIn('X0Transitive\tnames no open field\tproject', out)
        self.assertIn('milneIsogenyQuasiInverse: named on a claim line after its list of names, not counted', out)
        self.assertIn('neronSchemeExtensionExists: project claim with no claims.tsv row', out)

    def test_report_has_no_markers_or_worker_labels(self):
        _, out = run('--today', '2026-11-14')
        for bad in ('<!--', 'Worker', 'synthetic-marker', 'W4'):
            self.assertNotIn(bad, out)


class Write(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.mkdtemp()
        self.claims = os.path.join(self.tmp, 'claims.tsv')
        shutil.copy(CLAIMS, self.claims)

    def tearDown(self):
        shutil.rmtree(self.tmp)

    def write(self, today='2026-11-14'):
        code, out = run('--write', '--today', today, claims=self.claims)
        self.assertEqual(code, 0)
        header, rows = sc.read_tsv(self.claims)
        return header, {r['field']: r for r in rows}, out

    def test_project_rows_never_change(self):
        before_header, before = sc.read_tsv(CLAIMS)
        header, by, out = self.write()
        self.assertEqual(header, before_header)
        for r in before:
            if r['holder_kind'] == 'project':
                self.assertEqual(by[r['field']], r, r['field'])
        # a row from before the hold column starts from the evidence
        r = by['homFreeFiniteAlgClosed']
        self.assertEqual((r['task'], r['holder_kind'], r['public_holder'], r['hold'], r['claim_url']),
                         ('round 2', 'project', 'project', 'held', UP + '81#issuecomment-6885321564'))
        # an interest row is not moved to held by a project claim, only reported
        self.assertEqual(by['mumfordTorsionAlgClosed']['hold'], 'interest')
        self.assertIn('mumfordTorsionAlgClosed: project row is interest, but a project claim backs it', out)
        self.assertEqual(by['milneIsogenyQuasiInverse']['hold'], 'interest')
        # a deleted branch, or a comment with no parsed claim: kept held and reported
        self.assertEqual(by['shimuraFamilyAb']['hold'], 'held')
        self.assertIn('shimuraFamilyAb: held project row, but its branch or pull request is gone', out)
        self.assertEqual(by['deligneComponentsX6PrintedAb']['hold'], 'held')
        self.assertIn('deligneComponentsX6PrintedAb: held project row; no parsed claim on that thread backs', out)
        self.assertIn('gagaMorphism: held project row cites ' + UP + '82#issuecomment-1;', out)
        self.assertNotIn(('neronSchemeExtensionExists'), by)
        for f in BATCH2[1:]:
            self.assertEqual(by[f]['hold'], 'held', f)

    def test_outside_rows(self):
        _, by, out = self.write()
        # a held outside row with no parsed claim is not downgraded; the other claimant is reported
        self.assertEqual((by['yuThm11']['public_holder'], by['yuThm11']['hold']), ('zed-old', 'held'))
        self.assertIn('yuThm11: kept held by zed-old; no parsed claim backs it (unbacked)', out)
        self.assertIn('yuThm11: claimed by erin-q', out)
        # logins match case-insensitively; the canonical login is written back
        self.assertEqual((by['bostLowerBound']['public_holder'], by['bostLowerBound']['hold']), ('gina-h', 'held'))
        # a pull request URL is kept over a newer claim comment
        self.assertEqual(by['javanpeykarBound']['claim_url'], 'https://github.com/Deicyde/diophantine-z-q/pull/20')
        # released by the holder: the blocker goes into status
        r = by['weilPairingMumford']
        self.assertEqual((r['hold'], r['status'], r['public_holder']),
                         ('released', 'the Weil pairing API for abelian schemes is missing', 'tina-w'))
        # a released row is taken by a new claim
        r = by['r9b']
        self.assertEqual((r['hold'], r['public_holder'], r['status'], r['since'], r['claim_url']),
                         ('held', 'uma-x', 'claimed', '2026-11-05', FORK14 + '#issuecomment-1041'))

    def test_new_rows(self):
        _, by, _ = self.write()
        r = by['igusaPsi4']
        self.assertEqual((r['task'], r['status'], r['since'], r['issue'], r['holder_kind'], r['hold']),
                         ('', 'claimed', '2026-10-20', 'Deicyde/diophantine-z-q#14', 'outside', 'held'))
        self.assertEqual(by['semistableUnipotent']['hold'], 'held')
        self.assertEqual(by['picZeroAbVar']['claim_url'], 'https://github.com/Deicyde/diophantine-z-q/pull/23')
        self.assertEqual(by['phiAmpleIsogeny']['since'], '2026-11-10')
        self.assertEqual(by['gonzalezRotgerCountX6Ab']['holder_kind'], 'maintainer')
        # released by a project line naming the holder
        r = by['thetaRatiosAlgebraic']
        self.assertEqual((r['public_holder'], r['hold'], r['status']),
                         ('pete-s', 'released', 'no reply within 7 days of the lapse ping'))
        # released by the lapse rule: a ping, then 7 days with no reply
        r = by['r9a']
        self.assertEqual((r['public_holder'], r['hold'], r['status']),
                         ('carol-ag', 'released', 'lapsed: no reply within 7 days of the ping of 2026-10-20'))
        self.assertEqual(by['quotientP1Coordinate']['hold'], 'released')
        self.assertNotIn('bdRInvariants', by)

    def test_write_adds_columns_to_an_old_file(self):
        with open(self.claims, 'w', encoding='utf-8') as fh:
            fh.write('field\ttask\tstatus\tsince\tissue\n'
                     'mumfordTorsionAlgClosed\tbatch 2\tbriefed\t2026-11-14\telliotglazer/diophantine-z-q#81\n')
        run('--write', claims=self.claims)
        header, rows = sc.read_tsv(self.claims)
        self.assertEqual(header[-4:], sc.NEW_COLUMNS)
        self.assertEqual((rows[0]['public_holder'], rows[0]['hold'], rows[0]['claim_url']),
                         ('project', 'held', UP + '81#issuecomment-6887798791'))
        with open(self.claims, 'w', encoding='utf-8') as fh:
            fh.write('field\ttask\tstatus\tsince\tissue\n'
                     'milneIsogenyQuasiInverse\tbatch 2\tbriefed\t2026-11-14\telliotglazer/diophantine-z-q#81\n')
        run('--write', claims=self.claims)
        self.assertEqual(sc.read_tsv(self.claims)[1][0]['hold'], 'interest')

    def test_write_is_idempotent(self):
        run('--write', '--today', '2026-11-14', claims=self.claims)
        first = read_text(self.claims)
        run('--write', '--today', '2026-11-14', claims=self.claims)
        self.assertEqual(read_text(self.claims), first)

    def test_one_row_per_field(self):
        run('--write', '--today', '2026-11-14', claims=self.claims)
        fields = [r['field'] for r in sc.read_tsv(self.claims)[1]]
        self.assertEqual(len(fields), len(set(fields)))


class Check(unittest.TestCase):
    def test_free_field(self):
        code, out = run('--check', 'mumfordTorsionAlgClosed', 'homFreeFiniteAlgClosed')
        self.assertEqual(code, 0, out)

    def test_held_by_outsider(self):
        code, out = run('--check', 'igusaPsi4')
        self.assertEqual(code, 1)
        self.assertIn('held by alice-nt (outside)', out)

    def test_held_by_maintainer(self):
        code, out = run('--check', 'gonzalezRotgerCountX6Ab')
        self.assertEqual(code, 1)
        self.assertIn('maintainer', out)

    def test_outside_first_and_good_first_labels(self):
        code, out = run('--check', 'pazukiCor13Upper')
        self.assertEqual(code, 1)
        self.assertIn('labelled outside-first', out)
        code, out = run('--check', 'gaudronRemondThm14', 'mumfordTorsionAlgClosed')
        self.assertEqual(code, 1)
        self.assertIn('labelled good-first', out)

    def test_labels_absent_in_old_kinds(self):
        tmp = tempfile.mkdtemp()
        try:
            claims = os.path.join(tmp, 'claims.tsv')
            with open(claims, 'w', encoding='utf-8') as fh:
                fh.write('field\ttask\tstatus\tsince\tissue\n')
            code, out = run('--check', 'mumfordTorsionAlgClosed', claims=claims,
                            kinds=os.path.join(FX, 'kinds-8col.tsv'))
            self.assertEqual(code, 0, out)
        finally:
            shutil.rmtree(tmp)

    def test_claims_tsv_outside_hold(self):
        # zed-old's hold is only in claims.tsv; the check still refuses it
        code, out = run('--check', 'yuThm11')
        self.assertEqual(code, 1)
        self.assertIn('claims.tsv lists it held by zed-old', out)

    def test_frontier_id_and_unknown(self):
        self.assertEqual(run('--check', 'H-70')[0], 0)
        code, out = run('--check', 'noSuchField')
        self.assertEqual(code, 1)
        self.assertIn('names no open field', out)


class Sweep(unittest.TestCase):
    def queue(self, today):
        code, out = run('--sweep', '--today', today)
        self.assertEqual(code, 0)
        lines = out.strip().splitlines()
        self.assertEqual(lines[0], 'action\tfield\tholder\tthread\tlast_activity')
        return {tuple(l.split('\t')[:3]): l.split('\t') for l in lines[1:]}

    def test_ping_and_release(self):
        q = self.queue('2026-11-14')
        self.assertEqual(q[('ping', 'igusaPsi4', 'alice-nt')][3:], [FORK14, '2026-10-20'])
        self.assertEqual(q[('release', 'r9a', 'carol-ag')][3:], [FORK14, '2026-10-01'])
        # replied after the first ping: idle again since the reply, so a new ping
        self.assertIn(('ping', 'gaudronRemondThm14', 'ivan-r'), q)
        # a ping on the claim's pull request, then no reply: release
        self.assertIn(('release', 'quotientP1Coordinate', 'quinn-t'), q)
        # a ping on the pull request, then a reply there: idle since the reply, so a new ping
        self.assertIn(('ping', 'picZeroAbVar', 'rosa-u'), q)
        self.assertEqual(len(q), 5, q)

    def test_no_action_cases(self):
        fields = {k[1] for k in self.queue('2026-11-14')}
        self.assertNotIn('pazukiCor13Upper', fields)   # pinged 4 days ago: waiting
        self.assertNotIn('bostLowerBound', fields)     # a Progress line 4 days ago
        self.assertNotIn('javanpeykarBound', fields)   # commits on the draft PR
        self.assertNotIn('igusaChi10', fields)         # comment by the holder (a release of a sibling)
        self.assertNotIn('phiAmpleIsogeny', fields)    # the claim was edited into the PR 4 days ago
        self.assertNotIn('thetaRatiosAlgebraic', fields)   # released by the project, naming the holder
        self.assertNotIn('weilPairingMumford', fields)     # released by the holder

    def test_early_mention_is_not_a_ping(self):
        # alice-nt was welcomed (no marker) one day after her claim; that is not a ping
        self.assertNotIn('igusaPsi4', {k[1] for k in self.queue('2026-10-30')})

    def test_early_ping_and_datetime_intervals(self):
        # olga-m claimed at 2026-11-01T23:59Z; the marker ping two days later is too early to count
        self.assertNotIn('semistableUnipotent', {k[1] for k in self.queue('2026-11-10')})
        # 13 days and 1 minute at 2026-11-15T00:00Z: not yet idle for 14 days
        self.assertNotIn('semistableUnipotent', {k[1] for k in self.queue('2026-11-15')})
        self.assertIn(('ping', 'semistableUnipotent', 'olga-m'), self.queue('2026-11-16'))

    def test_pr_ping_waits_seven_days(self):
        self.assertNotIn('quotientP1Coordinate', {k[1] for k in self.queue('2026-10-27')})
        self.assertIn(('release', 'quotientP1Coordinate', 'quinn-t'), self.queue('2026-10-28'))

    def test_draft_pr_lapses_without_commits(self):
        q = self.queue('2026-12-01')
        self.assertIn(('ping', 'javanpeykarBound', 'hana-dev'), q)
        self.assertIn(('release', 'pazukiCor13Upper', 'judy-p'), q)
        self.assertIn(('project-stale', 'homFreeFiniteAlgClosed', 'project'), q)


class Config(unittest.TestCase):
    def test_issues_json(self):
        cfg = sc.Config({'claims_issue': 'Deicyde/diophantine-z-q#14',
                         'statement_checks_issue': 'Deicyde/diophantine-z-q#30',
                         'packet_issues': {'R5': 'Deicyde/diophantine-z-q#31'}})
        self.assertEqual(cfg.role('Deicyde/diophantine-z-q', 30), 'checks')
        self.assertEqual(cfg.role('Deicyde/diophantine-z-q', 31), 'packet')
        self.assertEqual(cfg.role('elliotglazer/diophantine-z-q', 81), 'area')
        self.assertIsNone(cfg.role('Deicyde/diophantine-z-q', 3))
        self.assertEqual(cfg.fetch_plan()['Deicyde/diophantine-z-q'], [14, 30, 31])

    def test_defaults_without_file(self):
        cfg = sc.Config.load(NO_ISSUES)
        self.assertEqual(cfg.claims, ('Deicyde/diophantine-z-q', 14))
        self.assertIsNone(cfg.checks)

    def test_reading_claim_on_statement_checks_issue(self):
        data = {'repos': {'Deicyde/diophantine-z-q': {'issues': [{'number': 30, 'comments': [
            {'url': 'u', 'author': {'login': 'kim-l'}, 'createdAt': '2026-11-12T08:00:00Z',
             'body': 'Claiming reading R5'}]}]}}}
        cfg = sc.Config({'statement_checks_issue': 'Deicyde/diophantine-z-q#30'})
        fields = sc.Fields(OPEN, CROSSWALK, KINDS)
        events = sc.parse_events(sc.load_threads(data, cfg), fields)[0]
        self.assertIn(('reading R5', 'kim-l'), active(sc.compute_holds(events)))
        self.assertEqual(sc.load_threads(data), {})


class Fetch(unittest.TestCase):
    def test_graphql_errors_keep_the_data(self):
        out = json.dumps({'data': {'repository': {'i14': None}}, 'errors': [{'type': 'NOT_FOUND'}]})
        done = subprocess.CompletedProcess([], 1, stdout=out, stderr='gh: Could not resolve to an Issue')
        err = io.StringIO()
        with mock.patch.object(sc.subprocess, 'run', return_value=done), contextlib.redirect_stderr(err):
            self.assertEqual(sc.gh_graphql('query'), {'i14': None})
        self.assertIn('Could not resolve', err.getvalue())
        self.assertIn('NOT_FOUND', err.getvalue())

    def test_no_data_fails(self):
        done = subprocess.CompletedProcess([], 1, stdout='', stderr='gh: HTTP 401')
        with mock.patch.object(sc.subprocess, 'run', return_value=done), \
                contextlib.redirect_stderr(io.StringIO()):
            with self.assertRaises(SystemExit):
                sc.gh_graphql('query')


if __name__ == '__main__':
    unittest.main()
