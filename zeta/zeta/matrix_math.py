# Private - personal, financial, and mental-health data
"""Row-by-column multiplication, with scalar arithmetic supplied by the language."""
from operator import add, mul, sub

_OPERATIONS = {"+": add, "-": sub, "*": mul}


def _identity(value):
    return value


def _child(parent, value):
    return value


def _arithmetic(op, left, right):
    return _OPERATIONS[op](left, right)


def matmul(left, right, *, scalar, zero, unwrap=_identity, child=_child,
           arithmetic=_arithmetic, tick=None):
    """Multiply rectangular row lists. A complex entry selects complex output."""
    complex_output = False

    def prepare(matrix, side):
        nonlocal complex_output
        raw = unwrap(matrix)
        if not isinstance(raw, list):
            raise ValueError(f"{side} operand must be a list of rows")
        rows, width = [], 0
        for i, raw_row in enumerate(raw):
            row = child(matrix, raw_row)
            items = unwrap(row)
            if not isinstance(items, list):
                raise ValueError(f"{side} row {i} must be a list")
            if i and len(items) != width:
                raise ValueError(f"{side} row {i} has {len(items)} entries, expected {width}")
            width = len(items)
            converted = []
            for raw_value in items:
                value = child(row, raw_value)
                entry = unwrap(value)
                if tick:
                    tick()
                if isinstance(entry, dict):
                    if set(entry) != {"real", "imag"}:
                        raise ValueError("complex entries require real and imag fields")
                    converted.append((scalar(child(value, entry["real"])),
                                      scalar(child(value, entry["imag"]))))
                    complex_output = True
                else:
                    converted.append((scalar(value), zero))
            rows.append(converted)
        return rows, width

    a, n = prepare(left, "left")
    b, p = prepare(right, "right")
    if n != len(b):
        raise ValueError(f"incompatible shapes {len(a)}x{n} and {len(b)}x{p}")
    columns = list(zip(*b))
    result = []
    for row in a:
        output = []
        for column in columns:
            real, imag = zero, zero
            for (x, y), (u, v) in zip(row, column):
                if tick:
                    tick()
                term = arithmetic("*", x, u)
                if complex_output:
                    term = arithmetic("-", term, arithmetic("*", y, v))
                    cross = arithmetic("+", arithmetic("*", x, v), arithmetic("*", y, u))
                    imag = arithmetic("+", imag, cross)
                real = arithmetic("+", real, term)
            output.append({"real": real, "imag": imag} if complex_output else real)
        result.append(output)
    return result
