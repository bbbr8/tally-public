import copy
import unittest
from tally_candidates import evaluate_candidates


class ProgramCandidates(unittest.TestCase):
    def packet(self):
        return {'candidates':[{'id':'good','source':'fn total(a,b) { return a + b }'},
                              {'id':'bad','source':'fn total(a,b) { return a - b }'}],
                'tests':[{'id':'money','expression':'total($1.25 from "A",$2.75 from "B")',
                          'expected':{'type':'money','cents':'400'},'sources':['A','B']},
                         {'id':'number','expression':'total(0.1,0.2)',
                          'expected':{'type':'number','decimal':'0.3'},'sources':[]}]}

    def test_exact_oracle_and_source_checks(self):
        packet=self.packet();old=copy.deepcopy(packet);r=evaluate_candidates(packet)
        self.assertEqual(r['accepted'],['good']);self.assertEqual(packet,old)
        self.assertEqual(len(r['counterexamples']),2)

    def test_execution_budget_produces_feedback(self):
        packet=self.packet();packet['max_steps']=100
        packet['candidates']=[{'id':'loop','source':'while true { let x = 1 }'}]
        r=evaluate_candidates(packet);self.assertEqual(r['accepted'],[])
        self.assertTrue(all(c['error']['code']=='E_LIMIT' for c in r['candidates'][0]['checks']))

    def test_imports_and_file_adapters_unavailable(self):
        packet=self.packet();packet['candidates']=[{'id':'import','source':'import "missing.tly" as lib'}]
        self.assertIn('Imports',evaluate_candidates(packet)['candidates'][0]['diagnostic'])
        packet['candidates']=[{'id':'reader','source':'fn total(a,b) { return read("missing.txt") }'}]
        self.assertEqual(evaluate_candidates(packet)['accepted'],[])

    def test_fresh_state_per_test_and_source_mismatch(self):
        packet=self.packet();packet['tests'][0]['sources']=['A']
        self.assertEqual(evaluate_candidates(packet)['accepted'],[])

    def test_decimal_precision_survives_candidate_transport(self):
        packet={'candidates':[{'id':'identity','source':'fn identity(x) { return x }'}],
                'tests':[{'id':'exact','expression':'identity(0.123456789012345678901)',
                          'expected':{'type':'number','decimal':'0.123456789012345678901'}}]}
        self.assertEqual(evaluate_candidates(packet)['accepted'],['identity'])

    def test_smallest_rejection_certificate_and_preflight_exclusions(self):
        packet = self.packet()
        packet['candidates'].append({'id': 'invalid', 'source': 'import "missing.tly" as lib'})
        result = evaluate_candidates(packet)
        cert = result['rejection_certificate']
        self.assertEqual(cert['tests'], ['money'])
        self.assertEqual(cert['witnesses'], {'money': ['bad']})
        self.assertEqual(cert['preflight_rejections'], ['invalid'])

    def test_certificate_matches_exhaustive_subsets(self):
        from itertools import combinations
        from random import Random
        from tally_candidates import rejection_certificate
        rng = Random(194)
        for _ in range(50):
            matrix = [[rng.randrange(2) for _ in range(6)] for _ in range(5)]
            rows = [dict(id=str(i), checks=[dict(id=str(j), passed=not x)
                                            for j, x in enumerate(row)])
                    for i, row in enumerate(matrix)]
            expected = next(subset for size in range(7)
                            for subset in combinations(range(6), size)
                            if all(not any(row) or any(row[j] for j in subset) for row in matrix))
            actual = rejection_certificate(rows, [dict(id=str(j)) for j in range(6)])
            self.assertEqual(actual['tests'], list(map(str, expected)))

    def test_global_minimum_can_omit_the_largest_single_rejection(self):
        from tally_candidates import rejection_certificate
        failures = [{0, 1, 2, 3}, {0, 1, 4}, {2, 3, 5}]
        tests = [dict(id=key) for key in ('largest', 'left', 'right')]
        rows = [dict(id=str(i), checks=[dict(id=t['id'], passed=i not in group)
                                        for t, group in zip(tests, failures)])
                for i in range(6)]
        self.assertEqual(rejection_certificate(rows, tests)['tests'], ['left', 'right'])
