"""Bounded, fingerprint-pinned exchange with Rico; imported evaluations stay derived."""
import hashlib
import json
import re
from datetime import date
from decimal import Decimal
from pathlib import Path
import tally as T
import tally_quantum as Q
import tally_qsearch as QS

LEVELS = {'SUPPORTED','SUPPORTED_IN_PART','OPEN','NOT_REACHED','CONTRADICTED'}
MAX_BYTES = 16 * 1024 * 1024


def no_duplicates(pairs):
    d = {}
    for k, v in pairs:
        if k in d:raise ValueError('duplicate JSON key: '+k)
        d[k] = v
    return d


def packet(it, node, value, purpose):
    count = [0]; active = set()
    def enc(v, depth=0):
        it.tick(node);count[0] += 1
        if depth > 32 or count[0] > 100000:raise ValueError('packet depth/node bound exceeded')
        sources = sorted(T.srcs(v));raw = T.strip(v)
        if len(sources)>4096 or any(not isinstance(s,str) or len(s)>16384 for s in sources):raise ValueError('invalid source list')
        out = {'sources': sources}
        if raw is None:out.update(type='nil',value=None)
        elif isinstance(raw,bool):out.update(type='bool',value=raw)
        elif isinstance(raw,str):
            if len(raw)>1024*1024:raise ValueError('packet string exceeds 1 MiB')
            out.update(type='string',value=raw)
        elif isinstance(raw,T.Money):
            v=str(raw.cents)
            if len(v)>128:raise ValueError('money exceeds 128 digits')
            out.update(type='money',cents=v)
        elif isinstance(raw,Decimal):
            v=str(raw)
            if not raw.is_finite() or len(v)>256:raise ValueError('invalid packet decimal')
            out.update(type='decimal',value=v)
        elif type(raw) is date:out.update(type='date',value=raw.isoformat())
        elif isinstance(raw,(list,dict)):
            ident=id(raw)
            if ident in active:raise ValueError('cyclic packet value')
            active.add(ident)
            try:
                if isinstance(raw,list):out.update(type='list',value=[enc(x,depth+1) for x in raw])
                else:
                    if any(not isinstance(k,str) or len(k)>16384 for k in raw):raise ValueError('packet map keys must be bounded strings')
                    out.update(type='map',value={k:enc(v,depth+1) for k,v in raw.items()})
            finally:active.remove(ident)
        else:raise ValueError('packet supports data values; got '+type(raw).__name__)
        return out
    purpose=T.strip(purpose)
    if not isinstance(purpose,str) or not purpose.strip() or len(purpose)>4096:raise ValueError('purpose must be a nonempty string, at most 4096 characters')
    result=json.dumps({'schema':'tally.case_packet.v1','analytical_tier':'derived','purpose':purpose,
                       'interpreter':T.interpreter_pin(),'value':enc(value)},ensure_ascii=False,allow_nan=False)
    if len(result.encode('utf-8'))>MAX_BYTES:raise ValueError('packet exceeds 16 MiB')
    return result


def read_report(it, node, path, expected, target):
    path=T.strip(path);expected=T.strip(expected);target=T.strip(target)
    if not isinstance(path,str) or not isinstance(expected,str) or not re.fullmatch('[0-9a-f]{64}',expected) or not isinstance(target,str):
        raise ValueError('read_rico needs path, lowercase sha256, target name')
    p=Path(T.resolve_path(it,path))
    with p.open('rb') as f:data=f.read(MAX_BYTES+1)
    if len(data)>MAX_BYTES or hashlib.sha256(data).hexdigest()!=expected:raise ValueError('Rico report size/hash mismatch')
    doc=json.loads(data,object_pairs_hook=no_duplicates,parse_float=Decimal,parse_int=Decimal,
                   parse_constant=lambda s:(_ for _ in ()).throw(ValueError('nonfinite JSON number')))
    if not isinstance(doc,dict) or not isinstance(doc.get('program'),str) or not isinstance(doc.get('sha256'),str) or not re.fullmatch('[0-9a-f]{64}',doc['sha256']) or not isinstance(doc.get('results'),list):
        raise ValueError('expected Rico elements --json envelope')
    hits=[r for r in doc['results'] if isinstance(r,dict) and r.get('name')==target]
    if len(hits)!=1:raise ValueError('Rico target must occur exactly once')
    r=hits[0];els=r.get('elements')
    if not isinstance(els,list) or len(els)>256 or not isinstance(r.get('state'),dict):raise ValueError('invalid Rico target')
    names=set();count=[0]
    source='derived:Rico-report:'+expected+' '+str(p.resolve())
    def annotate(v,depth=0):
        it.tick(node);count[0]+=1
        if depth>32 or count[0]>100000:raise ValueError('Rico report depth/node bound exceeded')
        if isinstance(v,dict):
            ss=v.get('sources',[]) if 'level' in v else []
            if not isinstance(ss,list) or any(not isinstance(x,str) or len(x)>16384 for x in ss) or len(ss)>4096:raise ValueError('invalid Rico source anchors')
            return T.wrap({k:annotate(x,depth+1) for k,x in v.items()},set(ss)|{source})
        if isinstance(v,list):return [annotate(x,depth+1) for x in v]
        return T.wrap(v,{source})
    if r['state'].get('level') not in LEVELS:raise ValueError('unknown Rico assessment level')
    for e in els:
        if not isinstance(e,dict) or not isinstance(e.get('name'),str) or not e['name'] or e['name'] in names or e.get('level') not in LEVELS:raise ValueError('invalid/duplicate Rico element or assessment')
        names.add(e['name'])
    result=annotate(r)
    return T.wrap({'schema':'tally.rico_report.v1','analytical_tier':'derived','result':result,
                   'report_sha256':expected,'program':doc['program'],'program_sha256':doc['sha256']},{source})


def install(it):
    def bind(name,fn,arity):it.builtins.vars[name]=T.Builtin(name,fn,arity)
    def case_packet(it_,node,value,purpose):
        try:return T.wrap(packet(it_,node,value,purpose),T.all_sources(value)|T.all_sources(purpose))
        except (ValueError,TypeError,OverflowError) as e:raise it_.err('exchange: '+str(e),node)
    def read_rico(it_,node,path,expected,target):
        try:return read_report(it_,node,path,expected,target)
        except (ValueError,TypeError,OSError,RecursionError) as e:raise it_.err('exchange: '+str(e),node)
    def rico_space(it_,node,report,weights):
        r=T.strip(report)
        if not isinstance(r,dict) or T.strip(r.get('schema'))!='tally.rico_report.v1':raise it_.err('rico_space expects a read_rico report',node)
        target=T.strip(r.get('result'));els=T.strip(target.get('elements')) if isinstance(target,dict) else None
        if not isinstance(els,list) or not 1<=len(els)<=Q.MAX_QUBITS:raise it_.err('rico_space supports 1..16 named elements',node)
        raw=T.strip(weights)
        if not isinstance(raw,list) or len(raw)!=1<<len(els):raise it_.err('rico_space needs explicit joint weights for every bit configuration',node)
        state=QS.encode(it_,node,weights);src=T.all_sources(report)|T.all_sources(weights)
        axes=[]
        for i,e in enumerate(els):
            e=T.strip(e)
            if not isinstance(e,dict) or not isinstance(T.strip(e.get('name')),str) or T.strip(e.get('level')) not in LEVELS:raise it_.err('invalid Rico element axis',node)
            axes.append({'qubit':Decimal(i),'element':e['name'],'assessment':e['level'],
                                     'sources':e.get('sources',[]),'tiers':e.get('tiers',[])})
        return T.wrap_deep({'state':state,'axes':axes,'target':target['name'],
            'semantics':'bit 1 assumes this premise holds within the declared scenario; Rico assessments remain separate',
            'weights':'caller-declared joint model; shared-source dependencies belong in joint weights',
            'analytical_tier':'hypothetical','report_sha256':r['report_sha256']},src)
    bind('case_packet',case_packet,(2,2));bind('read_rico',read_rico,(3,3));bind('rico_space',rico_space,(2,2))
