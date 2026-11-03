"""Bounded CPU simulation of pure quantum states, distinct from evidence probabilities.

Complex128-style Python complex amplitudes, most-significant qubit first (q0).
Unitary gates use standard matrices; measurement follows the Born rule. No
hardware execution or quantum speedup is claimed. Inputs/outputs are immutable.
"""
import bisect
import cmath
import math
import random
from decimal import Decimal

import tally as T

MAX_QUBITS = 16
MAX_GATES = 4096
MAX_SHOTS = 100000
PRECISION = Decimal('0.000000000001')
ROTATIONS = {'RX', 'RY', 'RZ', 'P'}
ARITY = {g: 1 for g in ('I', 'H', 'X', 'Y', 'Z', 'S', 'SDG', 'T', 'TDG', 'RX', 'RY', 'RZ', 'P')}
ARITY.update(CX=2, CZ=2, SWAP=2, CCX=3)
ADJOINT = {'S': 'SDG', 'SDG': 'S', 'T': 'TDG', 'TDG': 'T'}


def dec(value):
    return Decimal(str(value)).quantize(PRECISION).normalize()


def fail(it, node, message):
    raise it.err('quantum: ' + message, node)


def integer(it, node, value, name, low, high):
    value = T.strip(value)
    if isinstance(value, bool) or not isinstance(value, (Decimal, int)) or not Decimal(value).is_finite() \
            or value != int(value) or not low <= int(value) <= high:
        fail(it, node, f'{name} must be a whole number from {low} to {high}')
    return int(value)


def real(it, node, value, name):
    value = T.strip(value)
    if isinstance(value, bool) or not isinstance(value, (Decimal, int, float)):
        fail(it, node, f'{name} must be a finite number')
    value = float(value)
    if not math.isfinite(value):
        fail(it, node, f'{name} must be a finite number')
    return value


def targets(it, node, value, n):
    value = T.strip(value)
    value = value if isinstance(value, list) else [value]
    if not value:
        fail(it, node, 'targets must contain at least one qubit')
    result = [integer(it, node, x, 'qubit index', 0, n - 1) for x in value]
    if len(set(result)) != len(result):
        fail(it, node, 'target qubits must be distinct')
    return result


def spec(it, node, raw, n=MAX_QUBITS):
    raw = T.strip(raw)
    if not isinstance(raw, dict) or set(raw) - {'gate', 'targets', 'angle'} or not {'gate', 'targets'} <= set(raw):
        fail(it, node, 'a gate step is {gate: "H", targets: [0], angle: optional_radians}')
    gate = T.strip(raw['gate'])
    if not isinstance(gate, str):
        fail(it, node, 'gate name must be a string')
    gate = gate.upper()
    gate = 'CX' if gate == 'CNOT' else gate
    if gate not in ARITY:
        fail(it, node, f'unknown gate {gate}; supported: {", ".join(ARITY)}')
    ts = targets(it, node, raw['targets'], n)
    if len(ts) != ARITY[gate]:
        fail(it, node, f'{gate} takes {ARITY[gate]} distinct target qubit(s)')
    angle = raw.get('angle', Decimal(0))
    real(it, node, angle, 'angle in radians')
    if gate not in ROTATIONS and T.strip(angle) != 0:
        fail(it, node, f'{gate} has no rotation angle')
    return {'gate': gate, 'targets': ts, **({'angle': T.strip(angle)} if gate in ROTATIONS else {})}


def steps(it, node, raw, n=MAX_QUBITS):
    raw = T.strip(raw)
    if not isinstance(raw, list) or len(raw) > MAX_GATES:
        fail(it, node, f'circuit steps must be a list of at most {MAX_GATES} gates')
    result = []
    for entry in raw:
        it.tick(node)
        result.append(spec(it, node, entry, n))
    return result


class QuantumState:
    tally_type = 'quantum_state'

    def __init__(self, n, amplitudes, history=()):
        self.n = n
        self.amplitudes = tuple(amplitudes)
        self.history = tuple(history)

    def norm(self):
        return math.fsum(abs(a) ** 2 for a in self.amplitudes)

    def tally_show(self):
        return f'quantum_state({self.n} qubits, {len(self.history)} gates, norm={self.norm():.12g})'

    def tally_eq(self, other):
        # Amplitude equality, including global phase; use qfidelity for phase-invariant comparison.
        return isinstance(other, QuantumState) and self.n == other.n and all(
            abs(a - b) <= 1e-12 for a, b in zip(self.amplitudes, other.amplitudes))

    def tally_fields(self):
        preview = []
        for i, a in enumerate(self.amplitudes):
            if abs(a) > 1e-15:
                preview.append({'basis': format(i, f'0{self.n}b'), 're': dec(a.real), 'im': dec(a.imag),
                                'p': dec(abs(a) ** 2)})
                if len(preview) > 32:
                    break
        return {'schema': 'tally.quantum_state.v1', 'qubits': Decimal(self.n),
                'dimension': Decimal(len(self.amplitudes)), 'norm': dec(self.norm()),
                'gates': Decimal(len(self.history)), 'backend': 'cpu-statevector',
                'bit_order': 'q0 is the leftmost (most significant) bit',
                'preview': preview[:32], 'preview_truncated': len(preview) > 32,
                'precision': 'binary floating point; displayed numbers rounded to 12 decimal places'}


def as_state(it, node, value):
    value = T.strip(value)
    if not isinstance(value, QuantumState):
        fail(it, node, 'expected a quantum_state; create one with qstate(2)')
    return value


def matrix(gate, angle=0):
    c, s = math.cos(angle / 2), math.sin(angle / 2)
    r = math.sqrt(0.5)
    return {
        'I': (1, 0, 0, 1), 'H': (r, r, r, -r), 'X': (0, 1, 1, 0),
        'Y': (0, -1j, 1j, 0), 'Z': (1, 0, 0, -1),
        'S': (1, 0, 0, 1j), 'SDG': (1, 0, 0, -1j),
        'T': (1, 0, 0, cmath.exp(1j * math.pi / 4)),
        'TDG': (1, 0, 0, cmath.exp(-1j * math.pi / 4)),
        'RX': (c, -1j * s, -1j * s, c), 'RY': (c, -s, s, c),
        'RZ': (cmath.exp(-1j * angle / 2), 0, 0, cmath.exp(1j * angle / 2)),
        'P': (1, 0, 0, cmath.exp(1j * angle))}[gate]


def apply(it, node, state, operation):
    if len(state.history) >= MAX_GATES:
        fail(it, node, f'a state can retain at most {MAX_GATES} gate steps')
    gate, ts = operation['gate'], operation['targets']
    data = list(state.amplitudes)
    masks = [1 << (state.n - 1 - t) for t in ts]
    if gate == 'SWAP':
        a, b = masks
        for i in range(len(data)):
            it.tick(node)
            if not i & a and i & b:
                j = i ^ a ^ b
                data[i], data[j] = data[j], data[i]
    else:
        if gate in ('CX', 'CZ', 'CCX'):
            mask = masks[-1]
            control = sum(masks[:-1])
            m = matrix('Z' if gate == 'CZ' else 'X')
        else:
            mask, control = masks[0], 0
            m = matrix(gate, float(operation.get('angle', 0)))
        for i in range(len(data)):
            it.tick(node)
            if not i & mask and i & control == control:
                j = i | mask
                a, b = data[i], data[j]
                data[i], data[j] = m[0] * a + m[1] * b, m[2] * a + m[3] * b
    return QuantumState(state.n, data, state.history + (operation,))


def probabilities(it, node, state, ts):
    result = [0.0] * (1 << len(ts))
    masks = [1 << (state.n - 1 - t) for t in ts]
    for i, a in enumerate(state.amplitudes):
        it.tick(node)
        j = 0
        for mask in masks:
            j = (j << 1) | bool(i & mask)
        result[j] += abs(a) ** 2
    total = math.fsum(result)
    return [p / total for p in result]


def choose(ps, seed):
    rng = random.Random(seed)
    cdf, total = [], 0.0
    for p in ps:
        total += p
        cdf.append(total)
    # Put cumulative roundoff into the final possible outcome, never into a zero-probability tail.
    last = max(i for i, p in enumerate(ps) if p > 0)
    for i in range(last, len(cdf)):
        cdf[i] = 1.0
    return cdf, rng


def support(*values):
    return set().union(*(T.all_sources(v) for v in values))


def install(it):
    def bi(name, arity):
        def bind(fn):
            it.builtins.vars[name] = T.Builtin(name, fn, arity)
            return fn
        return bind

    @bi('qstate', (1, 2))
    def qstate(it_, node, count, basis=Decimal(0)):
        """Initialize 1..16 qubits in a computational basis state; q0 is the leftmost bit."""
        n = integer(it_, node, count, 'qubit count', 1, MAX_QUBITS)
        b = T.strip(basis)
        if isinstance(b, str):
            if len(b) != n or set(b) - {'0', '1'}:
                fail(it_, node, f'basis must be a {n}-bit string')
            b = int(b, 2)
        else:
            b = integer(it_, node, b, 'basis index', 0, (1 << n) - 1)
        data = []
        for i in range(1 << n):
            it_.tick(node)
            data.append(complex(i == b))
        return T.wrap(QuantumState(n, data), support(count, basis))

    @bi('qamplitudes', 1)
    def qamplitudes(it_, node, values):
        """A normalized power-of-two vector of real amplitudes or {re, im} complex amplitudes."""
        raw = T.strip(values)
        if not isinstance(raw, list) or not 2 <= len(raw) <= (1 << MAX_QUBITS) or len(raw) & (len(raw) - 1):
            fail(it_, node, 'amplitude count must be a power of two from 2 to 65536')
        data = []
        for a in raw:
            it_.tick(node)
            a = T.strip(a)
            if isinstance(a, dict):
                if set(a) - {'re', 'im'} or not a:
                    fail(it_, node, 'a complex amplitude is {re: number, im: number}')
                data.append(complex(real(it_, node, a.get('re', 0), 'real amplitude'),
                                    real(it_, node, a.get('im', 0), 'imaginary amplitude')))
            else:
                data.append(complex(real(it_, node, a, 'amplitude')))
        if any(abs(a) > 1 + 1e-9 for a in data):
            fail(it_, node, "normalized amplitudes cannot have magnitude greater than 1")
        norm = math.fsum(abs(a) ** 2 for a in data)
        if not math.isfinite(norm) or abs(norm - 1) > 1e-9:
            fail(it_, node, 'amplitudes must have sum(abs(amplitude)^2) = 1 within 1e-9')
        # Correct roundoff within the declared tolerance only.
        data = [a / math.sqrt(norm) for a in data]
        return T.wrap(QuantumState(len(data).bit_length() - 1, data), support(values))

    @bi('qgate', (3, 4))
    def qgate(it_, node, value, gate, qubits, angle=Decimal(0)):
        """Apply a validated unitary gate; angles are radians, controls precede targets."""
        state = as_state(it_, node, value)
        op = spec(it_, node, {'gate': gate, 'targets': qubits, 'angle': angle}, state.n)
        return T.wrap(apply(it_, node, state, op), support(value, gate, qubits, angle))

    @bi('qcircuit', 2)
    def qcircuit(it_, node, value, operations):
        """Validate a complete gate list, then execute it without mutating the input state."""
        state = as_state(it_, node, value)
        ops = steps(it_, node, operations, state.n)
        if len(state.history) + len(ops) > MAX_GATES:
            fail(it_, node, f'a state can retain at most {MAX_GATES} gate steps')
        for op in ops:
            state = apply(it_, node, state, op)
        return T.wrap(state, support(value, operations))

    @bi('qinverse', 1)
    def qinverse(it_, node, operations):
        """Reverse a gate list and replace every gate by its adjoint."""
        out = []
        for op in reversed(steps(it_, node, operations)):
            g = op['gate']
            out.append(dict(op, gate=ADJOINT.get(g, g),
                            **({'angle': -op['angle']} if g in ROTATIONS else {})))
        return T.wrap(out, support(operations))

    @bi('qoptimize', 1)
    def qoptimize(it_, node, operations):
        """Cancel adjacent inverse gates and merge adjacent rotations on identical targets."""
        ops = steps(it_, node, operations)
        out = []
        for op in ops:
            it_.tick(node)
            if op['gate'] == 'I':
                continue
            if out and out[-1]['targets'] == op['targets']:
                last = out[-1]
                if last['gate'] == op['gate'] and op['gate'] in ROTATIONS:
                    out.pop()
                    angle = last['angle'] + op['angle']
                    if angle != 0:
                        out.append(dict(op, angle=angle))
                    continue
                if op['gate'] not in ROTATIONS and ADJOINT.get(last['gate'], last['gate']) == op['gate']:
                    out.pop()
                    continue
            out.append(op)
        return T.wrap({'steps': out, 'before': Decimal(len(ops)), 'after': Decimal(len(out)),
                       'removed': Decimal(len(ops) - len(out))}, support(operations))

    @bi('qprobabilities', (1, 2))
    def qprobabilities(it_, node, value, qubits=None):
        """Born probabilities on all qubits or an ordered subset (first target is leftmost)."""
        state = as_state(it_, node, value)
        ts = list(range(state.n)) if T.strip(qubits) is None else targets(it_, node, qubits, state.n)
        ps = probabilities(it_, node, state, ts)
        return T.wrap({format(i, f'0{len(ts)}b'): dec(p) for i, p in enumerate(ps)}, support(value, qubits))

    @bi('qmeasure', (2, 3))
    def qmeasure(it_, node, value, qubits, options=None):
        """Partial computational-basis measurement; {seed: 7} or explicit {outcome: "01"} postselection."""
        state = as_state(it_, node, value)
        ts = targets(it_, node, qubits, state.n)
        opts = T.strip(options) if T.strip(options) is not None else {}
        if not isinstance(opts, dict) or set(opts) - {'seed', 'outcome'}:
            fail(it_, node, 'measurement options are {seed: integer} or {outcome: bitstring}')
        seed = integer(it_, node, opts.get('seed', 7), 'seed', 0, 2**63 - 1)
        ps = probabilities(it_, node, state, ts)
        postselected = 'outcome' in opts
        if postselected:
            outcome = T.strip(opts['outcome'])
            if not isinstance(outcome, str) or len(outcome) != len(ts) or set(outcome) - {'0', '1'}:
                fail(it_, node, f'outcome must be a {len(ts)}-bit string')
            chosen = int(outcome, 2)
        else:
            cdf, rng = choose(ps, seed)
            chosen = min(bisect.bisect_right(cdf, rng.random()), len(ps) - 1)
            outcome = format(chosen, f'0{len(ts)}b')
        p = ps[chosen]
        if p <= 0:
            fail(it_, node, 'measurement outcome has probability zero')
        data = []
        for i, a in enumerate(state.amplitudes):
            it_.tick(node)
            bits = ''.join('1' if i & (1 << (state.n - 1 - t)) else '0' for t in ts)
            data.append(a / math.sqrt(p) if bits == outcome else 0j)
        return T.wrap({'state': QuantumState(state.n, data, state.history), 'outcome': outcome,
                       'probability': dec(p), 'qubits': [Decimal(t) for t in ts],
                       'seed': None if postselected else Decimal(seed), 'postselected': postselected},
                      support(value, qubits, options))

    @bi('qsample', (1, 2, 3, 4))
    def qsample(it_, node, value, shots=Decimal(1024), seed=Decimal(7), qubits=None):
        """Seeded independent shots of the prepared state; this does not collapse the input."""
        state = as_state(it_, node, value)
        count = integer(it_, node, shots, 'shots', 1, MAX_SHOTS)
        seed_value = integer(it_, node, seed, 'seed', 0, 2**63 - 1)
        ts = list(range(state.n)) if T.strip(qubits) is None else targets(it_, node, qubits, state.n)
        ps = probabilities(it_, node, state, ts)
        cdf, rng = choose(ps, seed_value)
        counts = {}
        for _ in range(count):
            it_.tick(node)
            i = min(bisect.bisect_right(cdf, rng.random()), len(ps) - 1)
            label = format(i, f'0{len(ts)}b')
            counts[label] = counts.get(label, Decimal(0)) + 1
        return T.wrap({'schema': 'tally.quantum_samples.v1', 'counts': dict(sorted(counts.items())),
                       'shots': Decimal(count), 'seed': Decimal(seed_value), 'qubits': [Decimal(t) for t in ts],
                       'semantics': 'independent repetitions of the prepared state'}, support(value, shots, seed, qubits))

    @bi('qexpect', 2)
    def qexpect(it_, node, value, paulis):
        """Expectation of a Pauli string such as "ZZ" or "XI"; q0 is leftmost."""
        state = as_state(it_, node, value)
        word = T.strip(paulis)
        if not isinstance(word, str) or len(word) != state.n or set(word.upper()) - set('IXYZ'):
            fail(it_, node, f'Pauli word must contain {state.n} letters from IXYZ')
        result = 0j
        for i, a in enumerate(state.amplitudes):
            it_.tick(node)
            j, phase = i, 1
            for q, p in enumerate(word.upper()):
                mask = 1 << (state.n - 1 - q)
                bit = bool(i & mask)
                if p in 'XY':
                    j ^= mask
                if p == 'Y':
                    phase *= -1j if bit else 1j
                elif p == 'Z' and bit:
                    phase *= -1
            result += state.amplitudes[j].conjugate() * phase * a
        return T.wrap(dec(result.real), support(value, paulis))

    @bi('qbloch', (1, 2))
    def qbloch(it_, node, value, qubit=Decimal(0)):
        """Reduced one-qubit Bloch vector, purity and von Neumann entropy of a pure global state."""
        state = as_state(it_, node, value)
        q = integer(it_, node, qubit, 'qubit index', 0, state.n - 1)
        mask = 1 << (state.n - 1 - q)
        rho00, rho11, rho01 = 0.0, 0.0, 0j
        for i, a in enumerate(state.amplitudes):
            it_.tick(node)
            if not i & mask:
                b = state.amplitudes[i | mask]
                rho00 += abs(a) ** 2
                rho11 += abs(b) ** 2
                rho01 += a * b.conjugate()
        x, y, z = 2 * rho01.real, -2 * rho01.imag, rho00 - rho11
        radius = min(1.0, math.sqrt(x*x + y*y + z*z))
        eigen = [(1 + radius) / 2, (1 - radius) / 2]
        entropy = -sum(p * math.log2(p) for p in eigen if p > 0)
        purity = (1 + radius * radius) / 2
        return T.wrap({'qubit': Decimal(q), 'x': dec(x), 'y': dec(y), 'z': dec(z),
                       'purity': dec(purity), 'entropy': dec(entropy),
                       'entangled_with_rest': state.n > 1 and purity < 1 - 1e-10,
                       'semantics': 'reduced quantum state; global state is pure'}, support(value, qubit))

    @bi('qfidelity', 2)
    def qfidelity(it_, node, left, right):
        """Squared inner product of two pure states, invariant under global phase."""
        a, b = as_state(it_, node, left), as_state(it_, node, right)
        if a.n != b.n:
            fail(it_, node, 'fidelity requires states of the same qubit count')
        dot = 0j
        for x, y in zip(a.amplitudes, b.amplitudes):
            it_.tick(node)
            dot += x.conjugate() * y
        return T.wrap(dec(min(1.0, max(0.0, abs(dot) ** 2))), support(left, right))

    @bi('qasm', (2, 3))
    def qasm(it_, node, operations, count, measure_all=False):
        """Export gates as OpenQASM 3 with stdgates.inc; optional final measurement of all qubits."""
        n = integer(it_, node, count, 'qubit count', 1, MAX_QUBITS)
        measurement_arg = measure_all
        measure_all = T.strip(measure_all)
        if not isinstance(measure_all, bool):
            fail(it_, node, 'measure_all must be true or false')
        ops = steps(it_, node, operations, n)
        lines = ['OPENQASM 3.0;', 'include "stdgates.inc";', f'qubit[{n}] q;']
        for op in ops:
            g = op['gate']
            if g == 'I':
                continue
            name = g.lower()
            if g in ROTATIONS:
                name += '(' + str(op['angle']) + ')'
            lines.append(name + ' ' + ', '.join(f'q[{t}]' for t in op['targets']) + ';')
        if measure_all:
            lines += [f'bit[{n}] result;', 'result = measure q;']
        return T.wrap('\n'.join(lines) + '\n', support(operations, count, measurement_arg))

    @bi('qvector', 1)
    def qvector(it_, node, value):
        """Explicit full complex-amplitude export in basis order; default state JSON remains a bounded preview."""
        state = as_state(it_, node, value)
        out = []
        for i, a in enumerate(state.amplitudes):
            it_.tick(node)
            out.append({'basis': format(i, f'0{state.n}b'), 're': dec(a.real), 'im': dec(a.imag), 'p': dec(abs(a)**2)})
        return T.wrap(out, support(value))
