import unittest
from tally_candidates import evaluate_candidates


class CandidateHardening(unittest.TestCase):
    def packet(self):
        return {'candidates':[{'id':'p','source':'let x = 1'}],
                'tests':[{'id':'q','expression':'x + 2','expected':{'type':'number','decimal':'3'}}]}

    def test_budget_shared_by_setup_and_expression(self):
        p=self.packet();p['max_steps']=4
        r=evaluate_candidates(p)
        self.assertEqual(r['accepted'],[])
        self.assertEqual(r['candidates'][0]['checks'][0]['error']['code'],'E_LIMIT')

    def test_step_receipt_and_larger_budget_control(self):
        p=self.packet();p['max_steps']=100
        r=evaluate_candidates(p);check=r['candidates'][0]['checks'][0]
        self.assertEqual(r['accepted'],['p'])
        self.assertGreater(check['steps'],0)
        self.assertLessEqual(check['steps'],100)
        self.assertEqual(r['budget_scope'],'candidate setup plus expression per test')

    def test_roots_rejected_consistently(self):
        for p in (None,[],True):
            with self.subTest(p=p),self.assertRaises(ValueError):evaluate_candidates(p)

    def test_host_arithmetic_error_becomes_candidate_feedback(self):
        p=self.packet();p['tests'][0]['expression']='1 / 0'
        r=evaluate_candidates(p)
        self.assertEqual(r['accepted'],[])
        self.assertIsNotNone(r['candidates'][0]['checks'][0]['error'])

    def test_provenance_and_exact_zero_control(self):
        p=self.packet();p['tests'][0].update(expression='$0.00 from "z"',expected={'type':'money','cents':'0'},sources=['z'])
        self.assertEqual(evaluate_candidates(p)['accepted'],['p'])

