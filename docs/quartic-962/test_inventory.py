"""Adversarial document-binding tests. These do not certify mathematics.

The first eight tests retain the Version 5 integrity cases. Additional cases
cover predecessor pins, exact review receipts, retirement and V5 inheritance.
No release repository or authored register is required or mutated.
"""
import copy
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

import inventory as I


OLD_BODY = r'''\section{Old section}

\begin{lemma}\label{legacy:result}An inherited use of \cite{legacy}.\end{lemma}
\begin{proof}An unchanged old proof.\end{proof}

'''
ARITH = r'''\begin{lemma}\label{v5:arithmetic}The arithmetic uses \cite{modern}.\end{lemma}
\begin{proof}Exact Version 5 arithmetic proof.\end{proof}'''
NEW_BODY = r'''\begin{lemma}\label{new:result}A new use of \cite{newsource}.\end{lemma}
\begin{proof}A newly reviewed proof.\end{proof}'''
BIB = r'''\begin{thebibliography}{9}
\bibitem{legacy}Old published source.
\bibitem{modern}Arithmetic source.
\bibitem{newsource}New published source.
\bibitem{v5ft}Methodological attribution only.
\end{thebibliography}
'''


class InventoryBindingTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory(prefix='v6-inventory-test-')
        self.addCleanup(self.temp.cleanup)
        self.repo = Path(self.temp.name)
        self.path = 'manuscripts/quartic_v7.tex'
        self.write(I.OLD_TEX, OLD_BODY + BIB)
        self.write(I.V5_TEX, OLD_BODY + ARITH + '\n\n' + BIB)
        self.raw = (OLD_BODY + ARITH + '\n\n' + NEW_BODY + '\n\n' + BIB).encode()
        self.write(self.path, self.raw)
        old = I.Tex(I.read(self.repo, I.OLD_TEX), I.OLD_TEX)
        predecessor = I.Tex(I.read(self.repo, I.V5_TEX), I.V5_TEX)
        loc = old.span(*old.label_span('legacy:result'))
        self.write(I.BASE+'applications.json', [{'id':'A001','sources':['legacy'],
            'source_locator':'Theorem 1','objects_and_maps':'objects',
            'hypotheses_and_discharge':'hypotheses','conventions':'conventions',
            'translation_justification':'translation'}])
        self.write(I.BASE+'citations.json', [{'id':'C001','application_ids':['A001']}])
        self.write(I.BASE+'sources.json', [{'id':'legacy','version':'published'}])
        self.write(I.V4+'baseline-bridge.json', {'current_sha256':I.digest(old.raw),
            'anchors':[{'id':'old-anchor','application_id':'A001','version4_location':loc}],
            'citation_paragraphs':[{'id':'C001','version4_location':loc,'keys':['legacy'],'role':'application'}]})
        self.write(I.V4+'theorem-applications.json', {'inherited_additional_published_applications':[],
            'additional_published_applications':[],'source_version_requirements':['exact old versions']})
        self.write(I.V4+'dependency-closure.json', {})
        arithloc=predecessor.span(*predecessor.label_span('v5:arithmetic'))
        priorapps=[{'id':'V5-ARITH','current_sites':[arithloc],'citation_keys':['modern']},
                   {'id':'V5-SUN-FT-LINEAR','current_sites':[]},
                   {'id':'V5-SUN-DK-RELATIVE-INVERSE','current_sites':[]}]
        self.write(I.V5+'new-applications.json', {'applications':priorapps})
        self.write(I.V5+'theorem-applications.json', {'manuscript':I.pin(self.repo,I.V5_TEX),
            'input_pins':[I.pin(self.repo,I.BASE+'sources.json')], 'new_applications':priorapps,
            'reviewed_fragments':[{'id':'old-arithmetic','current':arithloc}]})
        self.write(I.V5+'coverage.json', {'status':'PASS_DOCUMENT_BINDING','manuscript':I.pin(self.repo,I.V5_TEX)})
        self.write(I.NEW+'evidence/new.tex', NEW_BODY)
        fragment=I.pin(self.repo,I.NEW+'evidence/new.tex')
        self.write(I.NEW+'evidence/review.json', {'decision':'accepted','fragment':fragment})
        self.inputs={'schema':I.REGISTER_SCHEMA,
            'predecessor_v5':[I.pin(self.repo,p) for p in [I.V5_TEX,I.V5+'theorem-applications.json',
                I.V5+'new-applications.json',I.V5+'coverage.json']],
            'dependency_policy':{'uses_frei_tinkova_as_assumed_theorem':False,
                'all_final_published_versions_checked':False,'all_assumed_external_results_published':True},
            'inherit_v5_applications':['V5-ARITH'],
            'retired_applications':[{'id':x,'reason':'Replaced by a separately reviewed proof',
                'replacement_ids':['V6-NEW']} for x in ['V5-SUN-FT-LINEAR','V5-SUN-DK-RELATIVE-INVERSE']],
            'applications':[{'id':'V6-NEW','exact_source_versions':[{'id':'newsource'}],
                'theorem_or_source_locator':'Theorem 2','objects_and_maps':'objects',
                'hypotheses_and_discharge':'discharged','conventions':'conventions',
                'translation':'translation','status':'reviewed','citation_keys':['newsource'],
                'current_labels':['new:result'],'reviewed_fragment':'new'}],
            'reviewed_fragments':[dict(fragment,id='new',provenance={'kind':'reviewed',
                'receipt_path':I.NEW+'evidence/review.json','sha256_pointer':'/fragment/sha256',
                'status_pointer':'/decision','accepted_status':'accepted'})],
            'evidence_pins':[I.pin(self.repo,I.NEW+'evidence/review.json')],
            'internal_results':[{'label':'new:result','status':'reviewed','reviewed_fragment':'new'}],
            'current_consumption':[{'id':'interface','current_labels':['new:result'],'depends_on':['V5-ARITH']}],
            'citation_classifications':[]}
        self.write(I.NEW+'new-applications.json', self.inputs)

    def write(self,path,data):
        target=self.repo/path;target.parent.mkdir(parents=True,exist_ok=True)
        if isinstance(data,bytes):target.write_bytes(data)
        elif isinstance(data,str):target.write_text(data,encoding='utf-8')
        else:target.write_bytes(I.encoded(data))

    def collect_modified(self,replacement=None,inputs=None):
        real_read=I.read
        replacement=self.raw if replacement is None else replacement
        def read(repo,path):return replacement if path==self.path else real_read(repo,path)
        with patch.object(I,'read',read):
            return I.collect(self.repo,self.path,self.inputs if inputs is None else inputs)['coverage.json']

    def append_before_bibliography(self,text):
        needle=b'\\begin{thebibliography}'
        self.assertEqual(self.raw.count(needle),1)
        return self.raw.replace(needle,text.encode()+b'\n\n'+needle)

    def test_current_inventory_closes_document_checks(self):
        coverage=self.collect_modified()
        self.assertEqual(coverage['status'],'PASS_DOCUMENT_BINDING')
        self.assertFalse(coverage['uses_frei_tinkova_as_assumed_theorem'])
        self.assertFalse(coverage['all_final_published_versions_checked'])

    def test_reviewed_mathematics_cannot_be_rebuilt_without_review(self):
        with self.assertRaisesRegex(ValueError,'Reviewed fragment must occur exactly once'):
            self.collect_modified(self.raw.replace(b'new:result}',b'new:result} altered',1))

    def test_new_citation_needs_application_record(self):
        result=self.collect_modified(self.append_before_bibliography(r'An unreviewed use of \cite{legacy}.'))
        self.assertTrue(result['unregistered_citations'])
        self.assertEqual(result['status'],'REVIEW_ITEMS_REMAIN')

    def test_new_lemma_needs_review(self):
        result=self.collect_modified(self.append_before_bibliography(r'\begin{lemma}\label{test:unreviewed}1=1.\end{lemma}'))
        self.assertIn('test:unreviewed',result['new_results_without_review_record'])

    def test_broken_reference_is_reported(self):
        result=self.collect_modified(self.append_before_bibliography(r'\ref{test:missing}'))
        self.assertIn('test:missing',[x['label'] for x in result['unresolved_references']])

    def test_old_source_excerpt_change_breaks_bridge(self):
        result=self.collect_modified(self.raw.replace(b'unchanged old proof',b'changed old proof'))
        self.assertTrue(result['unresolved_application_bridges'])

    def test_pinned_review_evidence_cannot_change_silently(self):
        changed=copy.deepcopy(self.inputs);changed['evidence_pins'][0]['sha256']='0'*64
        with self.assertRaisesRegex(ValueError,'Review evidence changed'):
            self.collect_modified(inputs=changed)

    def test_undeclared_dependency_is_reported(self):
        changed=copy.deepcopy(self.inputs);changed['current_consumption'][0]['depends_on'].append('test:missing')
        self.assertTrue(self.collect_modified(inputs=changed)['unresolved_declared_dependencies'])

    def test_v5_arithmetic_change_loses_inherited_review(self):
        result=self.collect_modified(self.raw.replace(b'Exact Version 5 arithmetic proof',b'Altered Version 5 arithmetic proof'))
        self.assertTrue(result['unresolved_application_bridges'])
        self.assertIn('v5:arithmetic',result['new_results_without_review_record'])

    def test_v5_predecessor_bytes_are_pinned(self):
        self.write(I.V5_TEX,'changed')
        with self.assertRaisesRegex(ValueError,'V5 predecessor changed'):
            self.collect_modified()

    def test_v5_original_evidence_is_still_pinned(self):
        self.write(I.BASE+'sources.json',[{'id':'legacy','version':'silently changed'}])
        with self.assertRaisesRegex(ValueError,'V5 accepted input changed'):
            self.collect_modified()

    def test_v5_application_cannot_disappear_without_disposition(self):
        changed=copy.deepcopy(self.inputs);changed['inherit_v5_applications']=[]
        with self.assertRaisesRegex(ValueError,'lacks explicit disposition'):
            self.collect_modified(inputs=changed)

    def test_ft_cannot_remain_an_assumed_application(self):
        changed=copy.deepcopy(self.inputs)
        changed['retired_applications']=changed['retired_applications'][1:]
        changed['inherit_v5_applications'].append('V5-SUN-FT-LINEAR')
        with self.assertRaisesRegex(ValueError,'cannot retain FT'):
            self.collect_modified(inputs=changed)

    def test_review_receipt_must_accept_exact_fragment_hash(self):
        changed=copy.deepcopy(self.inputs)
        changed['reviewed_fragments'][0]['provenance']['sha256_pointer']='/decision'
        with self.assertRaisesRegex(ValueError,'exact fragment bytes'):
            self.collect_modified(inputs=changed)

    def test_unaccepted_review_decision_fails(self):
        changed=copy.deepcopy(self.inputs)
        changed['reviewed_fragments'][0]['provenance']['accepted_status']='not accepted'
        with self.assertRaisesRegex(ValueError,'status differs'):
            self.collect_modified(inputs=changed)

    def test_detached_proof_cannot_escape_reviewed_fragment(self):
        extra=r'\begin{proof}[Another proof of \ref{new:result}]An unreviewed replacement.\end{proof}'
        with self.assertRaisesRegex(ValueError,'escapes reviewed fragment'):
            self.collect_modified(self.append_before_bibliography(extra))

    def test_delayed_named_proof_does_not_attach_to_intervening_lemma(self):
        raw = (r'\begin{lemma}\label{early}First.\end{lemma}' + '\n'
               + r'\begin{lemma}\label{late}Second.\end{lemma}' + '\n'
               + r'\begin{proof}Second proof.\end{proof}' + '\n'
               + r'\begin{proof}[Proof of \ref{early}]First proof.\end{proof}')
        results = I.Tex(raw.encode(), 'fixture.tex').results
        first = next(r for r in results if 'early' in r['labels'])
        second = next(r for r in results if 'late' in r['labels'])
        self.assertEqual(len(first['proof_spans']), 1)
        self.assertEqual(len(second['proof_spans']), 1)
        self.assertIn('First proof.', raw[slice(*first['proof_spans'][0])])
        self.assertIn('Second proof.', raw[slice(*second['proof_spans'][0])])

    def test_exact_predecessor_fragment_provenance(self):
        changed=copy.deepcopy(self.inputs)
        old=I.Tex(I.read(self.repo,I.V5_TEX),I.V5_TEX)
        self.write(I.NEW+'evidence/arithmetic.tex',ARITH)
        changed['reviewed_fragments'].append(dict(I.pin(self.repo,I.NEW+'evidence/arithmetic.tex'),
            id='arith',provenance={'kind':'exact_predecessor_span','span':old.span(*old.label_span('v5:arithmetic'))}))
        self.assertEqual(self.collect_modified(inputs=changed)['status'],'PASS_DOCUMENT_BINDING')

    def test_ft_attribution_must_be_explicit(self):
        raw=self.append_before_bibliography(r'Method attributed to \cite{v5ft}.')
        with self.assertRaisesRegex(ValueError,'FT citation is not explicitly non-assumed'):
            self.collect_modified(raw)
        changed=copy.deepcopy(self.inputs)
        changed['citation_classifications']=[{'keys':['v5ft'],'contains':'Method attributed','role':'provenance'}]
        self.assertEqual(self.collect_modified(raw,changed)['status'],'PASS_DOCUMENT_BINDING')

    def test_no_claim_all_final_typeset_versions_checked(self):
        changed=copy.deepcopy(self.inputs);changed['dependency_policy']['all_final_published_versions_checked']=True
        with self.assertRaisesRegex(ValueError,'Do not claim all final'):
            self.collect_modified(inputs=changed)

    def test_explicit_definition_conventions_are_not_theorem_applications(self):
        raw=self.append_before_bibliography(r'We use the notation conventions of \cite{modern}.')
        changed=copy.deepcopy(self.inputs)
        changed['citation_classifications']=[{'keys':['modern'],
            'contains':'We use the notation conventions','role':'conventions'}]
        self.assertEqual(self.collect_modified(raw,changed)['status'],'PASS_DOCUMENT_BINDING')

    def test_authored_candidate_pin_is_enforced_when_supplied(self):
        changed=copy.deepcopy(self.inputs)
        changed['candidate_pin']=I.pin(self.repo,self.path)
        with self.assertRaisesRegex(ValueError,'Authored candidate changed'):
            self.collect_modified(self.append_before_bibliography('Unreviewed prose.'),changed)

    def test_exact_source_statement_overrides_broad_new_application_scope(self):
        changed=copy.deepcopy(self.inputs)
        extra=copy.deepcopy(changed['applications'][0]);extra['id']='V6-OTHER'
        changed['applications'].append(extra)
        changed['citation_classifications']=[{'keys':['newsource'],
            'contains':'A new use of','role':'source_statement','application_ids':['V6-NEW']}]
        documents=I.collect(self.repo,self.path,changed)
        citation=next(c for c in documents['citations.json'] if c['keys']==['newsource'])
        self.assertEqual(citation['applications'],['V6-NEW'])

    def test_unlabeled_result_requires_exact_unique_statement_and_span(self):
        body = NEW_BODY + '\n' + r'\begin{remark}An exact reviewed remark.\end{remark}'
        raw = self.raw.replace(NEW_BODY.encode(), body.encode())
        self.write(I.NEW+'evidence/new.tex',body)
        fragment=I.pin(self.repo,I.NEW+'evidence/new.tex')
        self.write(I.NEW+'evidence/review.json',{'decision':'accepted','fragment':fragment})
        changed=copy.deepcopy(self.inputs)
        changed['reviewed_fragments'][0].update(fragment)
        changed['evidence_pins']=[I.pin(self.repo,I.NEW+'evidence/review.json')]
        parsed=I.Tex(raw,self.path)
        remark=next(r for r in parsed.results if r['environment']=='remark')
        span=parsed.span(remark['start'],remark['statement_end'])
        rec={'statement_sha256':span['text_sha256'],'current_statement':span,
             'status':'reviewed','reviewed_fragment':'new'}
        changed['internal_results'].append(rec)
        self.assertEqual(self.collect_modified(raw,changed)['status'],'PASS_DOCUMENT_BINDING')
        rec['current_statement']=dict(span,first_line=999)
        with self.assertRaisesRegex(ValueError,'statement span differs'):
            self.collect_modified(raw,changed)

    def test_repository_path_escape_rejected(self):
        with self.assertRaisesRegex(ValueError,'Path escapes repository'):
            I.read(self.repo,'../outside.tex')


if __name__=='__main__':unittest.main()
