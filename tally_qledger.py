"""Declared joint accounting scenarios, exact rational cents, and quantum filters.

All weights and exclusions are supplied modeling choices. Influence measures
changes within that model; document reading and legal assessments stay separate.
"""
from decimal import Decimal
from fractions import Fraction
import math
import tally as T
import tally_quantum as Q
import tally_qsearch as QS


def ledger(it,node,weights,outcomes,allowed):
    ws,vs=T.strip(weights),T.strip(outcomes)
    if not isinstance(ws,list) or not 2<=len(ws)<=65536 or len(ws)&(len(ws)-1) or not isinstance(vs,list) or len(vs)!=len(ws):
        Q.fail(it,node,'qledger needs equal power-of-two weight/outcome arrays, 2..65536')
    # Index validation reuses the simulator's q0-leftmost convention, without
    # constructing a state or changing exact money into floating point.
    class Shape:
        n=(len(ws)-1).bit_length()
        amplitudes=ws
    keep=QS.marked_indices(it,node,allowed,Shape())
    ww=[]; vv=[]
    for w,v in zip(ws,vs):
        it.tick(node);w=T.strip(w);v=T.strip(v)
        if isinstance(w,bool) or not isinstance(w,(int,Decimal)):Q.fail(it,node,'qledger weights must be nonnegative exact numbers')
        w=Decimal(w)
        if not w.is_finite() or w<0 or abs(w.as_tuple().exponent)>512 or len(w.as_tuple().digits)>128:Q.fail(it,node,'qledger weight exceeds exact rational bounds')
        if v is not None and not isinstance(v,T.Money):Q.fail(it,node,'qledger outcomes must be money or nil for unknown')
        if isinstance(v,T.Money) and len(str(abs(v.cents)))>128:Q.fail(it,node,'qledger money exceeds 128 digits')
        ww.append(Fraction(w));vv.append(v.cents if isinstance(v,T.Money) else None)
    total=sum(ww);retained=sum(w for i,w in enumerate(ww) if i in keep)
    if total<=0 or retained<=0:Q.fail(it,node,'qledger selected scenarios need positive declared weight')
    ids=[i for i in sorted(keep) if ww[i]>0];unknown=sum(ww[i] for i in ids if vv[i] is None)
    known=[i for i in ids if vv[i] is not None]
    def rat(f):return {'numerator':str(f.numerator),'denominator':str(f.denominator)}
    def mean(indices):
        if not indices or any(vv[i] is None for i in indices):return None
        return sum(ww[i]*vv[i] for i in indices)/sum(ww[i] for i in indices)
    m=mean(ids);axes=[]
    for q in range(Shape.n):
        it.tick(node);mask=1<<(Shape.n-1-q);one=[i for i in ids if i&mask];zero=[i for i in ids if not i&mask]
        a,b=mean(one),mean(zero)
        axes.append({'qubit':Decimal(q),'mean_if_one_cents':rat(a) if a is not None else None,
                     'mean_if_zero_cents':rat(b) if b is not None else None,
                     'difference_cents':rat(a-b) if a is not None and b is not None else None})
    return T.wrap_deep({'schema':'tally.qledger.v1','qubits':Decimal(Shape.n),'positive_scenarios':Decimal(len(ids)),
        'retained_weight':rat(retained/total),'unknown_weight':rat(unknown/retained),'complete':unknown==0,
        'mean_cents':rat(m) if m is not None else None,'known_min':T.Money(min(vv[i] for i in known)) if known else None,
        'known_max':T.Money(max(vv[i] for i in known)) if known else None,'axis_sensitivity':axes,
        'semantics':'caller-declared joint weights and scenario outcomes; rational cents remain unrounded; model sensitivity only'},
        T.all_sources(weights)|T.all_sources(outcomes)|T.all_sources(allowed))


def install(it):
    def qledger(it_,node,weights,outcomes,allowed):return ledger(it_,node,weights,outcomes,allowed)
    def qcondition(it_,node,raw,allowed):
        st=Q.as_state(it_,node,raw);ids=QS.marked_indices(it_,node,allowed,st)
        mass=math.fsum(abs(st.amplitudes[i])**2 for i in ids)
        if mass<=0:Q.fail(it_,node,'qcondition has zero supported mass')
        if len(st.history)>=Q.MAX_GATES:Q.fail(it_,node,'state operation budget exceeded')
        amps=[]
        for i,a in enumerate(st.amplitudes):
            it_.tick(node);amps.append(a/math.sqrt(mass) if i in ids else 0j)
        state=Q.QuantumState(st.n,amps,st.history+({'abstract':'scenario_postselection','allowed':tuple(sorted(ids))},))
        return T.wrap_deep({'state':state,'retained_mass':Decimal(str(mass)),
            'semantics':'explicit model postselection; discarded mass remains reported; no new evidence is created'},Q.support(raw,allowed))
    it.builtins.vars['qledger']=T.Builtin('qledger',qledger,(3,3))
    it.builtins.vars['qcondition']=T.Builtin('qcondition',qcondition,(2,2))
