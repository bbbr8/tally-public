# Private - personal, financial, and mental-health data
import unittest
import tally


class MatrixTests(unittest.TestCase):
    def evaluate(self, expr):
        result = tally.eval_json(expr)
        self.assertTrue(result["ok"], result.get("error"))
        return result

    def test_real_complex_and_empty(self):
        for expr in ('matmul([[1,2],[3,4]],[[5],[6]]) == [[17],[39]]',
                     'matmul([[{real:0,imag:1}]],[[{real:0,imag:1}]])[0][0].real == -1',
                     'matmul([[0.1]],[[0.2]])[0][0] == 0.02',
                     'matmul([[],[]],[]) == [[],[]]'):
            with self.subTest(expr=expr):
                self.assertIs(self.evaluate(expr)["value"], True)

    def test_cancellation_exceeding_decimal_context(self):
        big = "1" + "0"*50
        result = self.evaluate(f"matmul([[{big},1,-{big}]],[[1],[1],[1]])[0][0] == 1")
        self.assertIs(result["value"], True)

    def test_cell_sources(self):
        result = self.evaluate('matmul([[2 from "A", 3 from "B"], [4 from "C", 1]],[[5],[6]])[0][0]')
        self.assertEqual(set(result["sources"]), {"A", "B"})

    def test_shape_and_types(self):
        for expr in ('matmul([[1]],[[2],[3]])', 'matmul([[1],[]],[[1]])', 'matmul([[true]],[[1]])'):
            self.assertFalse(tally.eval_json(expr)["ok"])
