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
