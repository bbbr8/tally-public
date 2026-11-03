"""Declared joint scenarios and amplitude amplification about the prepared state.

The weights describe a caller's model. Born probabilities and amplified search
weights describe that model, independently of any evidentiary or legal finding.
"""
import math
from decimal import Decimal, localcontext, MAX_EMAX, MIN_EMIN, DecimalException
import tally as T
import tally_quantum as Q


def encode(it, node, weights):
    raw = T.strip(weights)
    if not isinstance(raw, list) or not 2 <= len(raw) <= 1 << Q.MAX_QUBITS or len(raw) & (len(raw)-1):
        Q.fail(it, node, 'weights need a power-of-two length, 2..65536')
    ds = []
    for x in raw:
        it.tick(node); x = T.strip(x)
        if isinstance(x, bool) or not isinstance(x, (Decimal, int)):
            Q.fail(it, node, 'weights must be finite nonnegative numbers')
        x = Decimal(x)
        if not x.is_finite() or x < 0:
            Q.fail(it, node, 'weights must be finite nonnegative numbers')
        ds.append(x)
    scale = max(ds)
    if not scale:
        Q.fail(it, node, 'at least one scenario needs positive weight')
    # Scaling before conversion avoids overflow from large finite Decimal inputs.
    try:
        with localcontext() as ctx:
            ctx.prec=40;ctx.Emax=MAX_EMAX;ctx.Emin=MIN_EMIN
            scaled = [float(x / scale) for x in ds]
    except (DecimalException, OverflowError, ValueError):
        Q.fail(it, node, 'weight dynamic range exceeds this floating-point simulator')
    if any(x and y == 0 for x, y in zip(ds, scaled)):
        Q.fail(it, node, 'weight dynamic range exceeds this floating-point simulator')
    total = math.fsum(scaled)
    amps = [complex(math.sqrt(x / total)) for x in scaled]
    if any(x and a == 0 for x, a in zip(ds, amps)):
        Q.fail(it, node, 'normalized weight underflows this floating-point simulator')
    return Q.QuantumState((len(raw)-1).bit_length(), amps)


def marked_indices(it, node, raw, state):
    raw = T.strip(raw)
    if not isinstance(raw, list) or len(raw) > len(state.amplitudes):
        Q.fail(it, node, 'marked basis states must be a bounded list')
    out = set()
    for x in raw:
        it.tick(node); x = T.strip(x)
        if isinstance(x, str):
            if len(x) != state.n or set(x) - {'0', '1'}:
                Q.fail(it, node, 'marked strings must match the state qubit count')
            x = int(x, 2)
        else:
            x = Q.integer(it, node, x, 'marked basis index', 0, len(state.amplitudes)-1)
        if x in out:
            Q.fail(it, node, 'marked basis states must be unique')
        out.add(x)
    return out


def amplify(it, node, state, marked, rounds):
    initial = state.amplitudes
    data = list(initial)
    if len(state.history) + 2 * rounds > Q.MAX_GATES:
        Q.fail(it, node, 'amplification exceeds the state operation budget')
    for _ in range(rounds):
        for i in range(len(data)):
            it.tick(node)
            if i in marked:
                data[i] = -data[i]
        # Reflection about this exact prepared vector preserves zero support.
        z = sum(a.conjugate() * b for a, b in zip(initial, data))
        for i, a in enumerate(initial):
            it.tick(node); data[i] = 2 * a * z - data[i]
    history = state.history + tuple({'abstract': op, 'marked': tuple(sorted(marked))}
                                   for _ in range(rounds) for op in ('phase_oracle', 'prepared_reflection'))
    return Q.QuantumState(state.n, data, history)


def install(it):
    def bind(name, fn, arity):it.builtins.vars[name] = T.Builtin(name, fn, arity)
    def qencode(it_, node, weights):
        return T.wrap(encode(it_, node, weights), T.all_sources(weights))
    def qmark(it_, node, raw, marked):
        st = Q.as_state(it_, node, raw); indices = marked_indices(it_, node, marked, st)
        if len(st.history) >= Q.MAX_GATES:Q.fail(it_, node, 'state operation budget exceeded')
        amps = []
        for i, a in enumerate(st.amplitudes):
            it_.tick(node); amps.append(-a if i in indices else a)
        return T.wrap(Q.QuantumState(st.n, amps, st.history + ({'abstract':'phase_oracle','marked':tuple(sorted(indices))},)), Q.support(raw, marked))
    def qamplify(it_, node, raw, marked, rounds):
        st = Q.as_state(it_, node, raw); indices = marked_indices(it_, node, marked, st)
        n = Q.integer(it_, node, rounds, 'amplification rounds', 0, 256)
        return T.wrap(amplify(it_, node, st, indices, n), Q.support(raw, marked, rounds))
    bind('qencode', qencode, (1,1));bind('qmark', qmark, (2,2));bind('qamplify', qamplify, (3,3))
