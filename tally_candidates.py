"""Execute candidate Tally programs against exact, source-aware finite tests.

For trusted local candidate programs. Language steps are bounded; this is not an
operating-system sandbox or a bound on every Python built-in's time or allocation.
File adapters are removed and imports are rejected in this evaluation profile.
"""
import argparse
import hashlib
import json
from pathlib import Path
import tally

PURE={'print','sources','len','sum','min','max','abs','round','round_money','type','str',
      'int','money','date','range','sorted','map','filter','reduce','any','all','contains','join','split'}


def canonical(value):return json.dumps(value,sort_keys=True,separators=(',',':'),allow_nan=False)
def digest(value):return hashlib.sha256(canonical(value).encode()).hexdigest()


def no_imports(source):
    def visit(value):
        if isinstance(value,tally.N):
            if value.k=='import':raise ValueError('Imports are unavailable in the candidate profile')
            visit(value.a)
        elif isinstance(value,(list,tuple)):
            for child in value:visit(child)
        elif isinstance(value,dict):
            for child in value.values():visit(child)
    visit(tally.parse(source,'<candidate>'))


def evaluate_candidates(packet):
    if not isinstance(packet,dict):raise ValueError('Candidate packet must be an object')
    candidates=packet.get('candidates');tests=packet.get('tests');steps=packet.get('max_steps',20000)
    if not isinstance(candidates,list) or not 1<=len(candidates)<=16:raise ValueError('Supply 1..16 candidate programs')
    if not isinstance(tests,list) or not 1<=len(tests)<=64:raise ValueError('Supply 1..64 exact tests')
    if type(steps) is not int or not 1<=steps<=100000:raise ValueError('max_steps must be 1..100000')
    seen=set()
    for test in tests:
        if not isinstance(test,dict) or set(test)-{'id','expression','expected','sources'} or not {'id','expression','expected'}<=set(test):raise ValueError('Tests need id, expression and exact expected value')
        if not isinstance(test['id'],str) or not test['id'] or test['id'] in seen:raise ValueError('Test IDs must be unique text')
        seen.add(test['id'])
        if not isinstance(test['expression'],str) or len(test['expression'])>16384:raise ValueError('Test expression too large')
        if 'sources' in test and (not isinstance(test['sources'],list) or any(not isinstance(x,str) for x in test['sources']) or len(test['sources'])!=len(set(test['sources']))):raise ValueError('Sources must be distinct source IDs')
        canonical(test)
    rows=[];seen=set();classes={}
    for candidate in candidates:
        if not isinstance(candidate,dict) or set(candidate)!={'id','source'} or not isinstance(candidate['id'],str) or not candidate['id'] or candidate['id'] in seen:raise ValueError('Candidate IDs must be unique text')
        seen.add(candidate['id']);source=candidate['source']
        if not isinstance(source,str) or len(source.encode())>65536:raise ValueError('Candidate source exceeds 64 KiB')
        row={'id':candidate['id'],'source_sha256':hashlib.sha256(source.encode()).hexdigest(),'passed':False,'checks':[]}
        try:no_imports(source)
        except (ValueError,tally.TallyError) as exc:
            row['diagnostic']=str(exc);rows.append(row);continue
        for test in tests:
            session=tally.Session(max_steps=steps)
            session.it.builtins.vars={k:v for k,v in session.it.builtins.vars.items() if k in PURE}
            # A batch shares one interpreter budget across setup and expression.
            batch=session.handle({'op':'batch','atomic':True,'requests':[
                {'op':'exec','code':source},{'op':'eval','code':test['expression']}]})
            value=batch['value'][-1]
            actual=value.get('exact_value');sources=value.get('sources',[])
            passed=value['ok'] and canonical(actual)==canonical(test['expected']) and ('sources' not in test or sorted(sources)==sorted(test['sources']))
            row['checks'].append({'id':test['id'],'passed':passed,'actual':actual,'sources':sources,
                                  'error':value.get('error'),'expected':test['expected'],
                                  'steps':session.it.budget.steps})
        row['passed']=all(c['passed'] for c in row['checks'])
        signature=digest([{'actual':c['actual'],'sources':c['sources'],'error':c['error']} for c in row['checks']])
        classes.setdefault(signature,[]).append(row['id']);rows.append(row)
    return {'schema':'tally.candidates.v1','runtime_version':tally.VERSION,'runtime_pin':tally.interpreter_pin(),
            'tests_sha256':digest(tests),'candidates':rows,'accepted':[r['id'] for r in rows if r['passed']],
            'outcome_classes':[{'class_id':key,'candidates':ids} for key,ids in sorted(classes.items())],
            'counterexamples':[{'candidate':r['id'],**c} for r in rows for c in r['checks'] if not c['passed']],
            'max_steps_per_request':steps,'budget_scope':'candidate setup plus expression per test',
            'scope':'declared exact test outcomes and source IDs; finite conformance only'}


def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('packet',type=Path);a=p.parse_args()
    try:result=evaluate_candidates(json.loads(a.packet.read_text()))
    except (ValueError,KeyError,TypeError,OSError) as exc:p.exit(2,str(exc)+'\n')
    print(json.dumps(result,indent=2));return 0 if result['accepted'] else 1


if __name__=='__main__':raise SystemExit(main())
