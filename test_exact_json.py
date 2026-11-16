"""Lossless tool transport, checked against decimal text rather than a float."""
from decimal import Decimal
import unittest
import tally


class ExactTransport(unittest.TestCase):
    def test_original_transfer_and_control(self):
        for text in ['0.11111111111111111111', '0.123456789012345678901234567890', '0.25']:
            result = tally.eval_json(text)
            self.assertTrue(result['ok'])
            self.assertEqual(Decimal(result['exact_value']['decimal']), Decimal(text))
            self.assertIn('value', result)

    def test_session_nested_types_and_sources(self):
        session = tally.Session()
        result = session.handle({'op':'eval', 'code':'{n: 0.1234567890123456789, m: $12.34 from "S", s: "1.2", b: true}'})
        self.assertTrue(result['ok'])
        self.assertEqual(result['sources'], ['S'])
        exact = result['exact_value']
        self.assertEqual(exact['n'], {'type':'number','decimal':'0.1234567890123456789'})
        self.assertEqual(exact['m'], {'type':'money','cents':'1234'})
        self.assertEqual((exact['s'], exact['b']), ('1.2', True))

    def test_exec_expression(self):
        result = tally.Session().handle({'op':'exec','code':'0.1234567890123456789'})
        self.assertEqual(result['exact_value']['decimal'], '0.1234567890123456789')

    def test_batch_rejects_nonboolean_atomic_before_running_children(self):
        session = tally.Session()
        for flag in ('false', 0, None):
            with self.subTest(flag=flag):
                result = session.handle({'op': 'batch', 'atomic': flag, 'requests': [
                    {'op': 'exec', 'code': 'let amount = 4'}]})
                self.assertFalse(result['ok'])
                self.assertEqual(result['error']['code'], 'E_REQUEST')
                self.assertFalse(session.handle({'op': 'eval', 'code': 'amount'})['ok'])

    def test_atomic_false_keeps_successes_and_true_rolls_back(self):
        for flag in (True, False):
            session = tally.Session()
            result = session.handle({'op': 'batch', 'atomic': flag, 'requests': [
                {'op': 'exec', 'code': 'let amount = 4'},
                {'op': 'eval', 'code': 'missing_value'}]})
            self.assertFalse(result['ok'])
            self.assertEqual(result['rolled_back'], flag)
            self.assertEqual(session.handle({'op': 'eval', 'code': 'amount'})['ok'], not flag)

    def test_cent_allocation_compares_remainders_beyond_decimal_precision(self):
        weights = '[1, 1.' + '0' * 50 + '1] from "weights"'
        for amount, expected in [('$0.01', '1'), ('-$0.01', '-1')]:
            expr = f'allocate({amount} from "amount", {weights})'
            report = tally.eval_json(expr)
            self.assertTrue(report['ok'])
            self.assertEqual([v['cents'] for v in report['exact_value']], ['0', expected])
            self.assertEqual(report['sources'], ['amount', 'weights'])
        self.assertEqual(tally.eval_json('allocate($0.01, [1, 1])')['value'], ['$0.01', '$0.00'])

    def test_linear_solve_exact_unique_singular_and_inconsistent(self):
        from fractions import Fraction
        def solve(matrix, rhs):
            report = tally.eval_json(f'linear_solve({matrix}, {rhs})')
            self.assertTrue(report['ok'], report['error'])
            return report
        def vector(entries):
            return [Fraction(int(entry['numerator']), int(entry['denominator'])) for entry in entries]
        report = solve('[[0,2], [3 from "coefficient",1]]', '[1,1] from "constants"')
        self.assertEqual(report['sources'], ['coefficient','constants'])
        value = report['value']
        self.assertEqual((value['status'], value['rank']), ('unique', 2))
        self.assertEqual(vector(value['particular']), [Fraction(1,6), Fraction(1,2)])
        value = solve('[[2,4],[1,2]]', '[4,2]')['value']
        self.assertEqual((value['status'], value['rank']), ('parametric', 1))
        self.assertEqual(vector(value['particular']), [2,0])
        self.assertEqual(vector(value['nullspace'][0]), [-2,1])
        value = solve('[[2,4],[1,2]]', '[4,3]')['value']
        self.assertEqual((value['status'], value['particular']), ('inconsistent', None))
        for expr in ['linear_solve([[1],[1,2]], [1,2])', 'linear_solve([[true]], [1])',
                     'linear_solve([[1]], [])']:
            self.assertFalse(tally.eval_json(expr)['ok'])

    def test_least_squares_unique_and_nonidentifiable(self):
        from fractions import Fraction
        def q(value):
            return Fraction(value['numerator'], value['denominator'])
        result = tally.eval_json('least_squares([[1],[1],[1]], [1,2,4] from "readings")')
        self.assertEqual(result['sources'], ['readings'])
        value = result['value']
        self.assertEqual(q(value['particular'][0]), Fraction(7,3))
        self.assertEqual(list(map(q,value['residuals'])), [Fraction(4,3),Fraction(1,3),Fraction(-5,3)])
        self.assertEqual(q(value['squared_error']), Fraction(14,3))
        value = tally.eval_json('least_squares([[1,2],[1,2]], [0,2])')['value']
        self.assertEqual(value['status'], 'parametric')
        self.assertEqual(list(map(q,value['nullspace'][0])), [-2,1])
        self.assertEqual(q(value['squared_error']), 2)
        value = tally.eval_json('least_squares([[0],[0]],[1,2])')['value']
        self.assertEqual((value['rank'], q(value['squared_error'])), (0,5))
