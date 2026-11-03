"""Exact, source-retaining budget bridges and applied receivable roll-forwards."""
from decimal import Decimal
from datetime import date
import tally as T

FIELDS=('scheduled','change','revised','completed','deposits','total','balance')


def install(it):
    def fail(node,msg):raise it.err('accounting: '+msg,node)
    def array(raw,node):
        raw=T.strip(raw)
        if not isinstance(raw,list) or len(raw)>2000:fail(node,'at most 2000 rows required')
        return raw
    def obj(raw,node):
        raw=T.strip(raw)
        if not isinstance(raw,dict):fail(node,'rows must be maps')
        return raw
    def amount(v,node):
        v=T.strip(v)
        if not isinstance(v,T.Money):fail(node,'amounts must be exact money')
        return v.cents
    def identity(v,node):
        v=T.strip(v)
        if isinstance(v,bool) or not isinstance(v,(str,Decimal)) or v=='':fail(node,'identity must be a nonempty string or number')
        return (type(v).__name__,v)
    def sources(*vs):return set().union(*(T.all_sources(v) for v in vs))
    def bind(name,fn,arity):it.builtins.vars[name]=T.Builtin(name,fn,arity)

    def bridge(it_,node,before,after):
        def index(raw):
            out={}
            for original in array(raw,node):
                it_.tick(node);r=obj(original,node)
                if any(k not in r for k in ('id','scope')+FIELDS):fail(node,'budget rows need id, scope and seven budget_audit money fields')
                key=(identity(r['scope'],node),identity(r['id'],node))
                if key in out:fail(node,'duplicate scope/item identity; comparison requires unique rows')
                for k in FIELDS:amount(r[k],node)
                out[key]=(r,original)
            return out
        a,b=index(before),index(after);changes=[];added=[];removed=[]
        for key in sorted(set(a)|set(b),key=str):
            it_.tick(node)
            if key not in a:added.append(b[key][1]);continue
            if key not in b:removed.append(a[key][1]);continue
            (x,rx),(y,ry)=a[key],b[key];d={k:amount(y[k],node)-amount(x[k],node) for k in FIELDS}
            residual=d['balance']-(d['revised']-d['completed']-d['deposits'])
            inputs=sources(rx,ry)
            def valid(r):
                m={k:amount(r[k],node) for k in FIELDS}
                return m['scheduled']+m['change']==m['revised'] and m['completed']+m['deposits']==m['total'] and m['revised']-m['total']==m['balance']
            changes.append(T.wrap_deep({'id':T.strip(x['id']),'scope':T.strip(x['scope']),
                'delta':{k:T.Money(v) for k,v in d.items()},'bridge_gap':T.Money(residual),'bridge_balanced':residual==0,
                'before_balanced':valid(x),'after_balanced':valid(y),
                'scope_driven_balance_change':valid(x) and valid(y) and d['balance']!=0 and d['balance']==d['revised'] and d['completed']==d['deposits']==d['total']==0,
                'changed':any(d.values()),'interpretation':'changes in supplied budget columns; funded, paid and credited stages require their own records'},inputs))
        clean=bool(changes) and not added and not removed and all(all(T.strip(r[k]) for k in ('bridge_balanced','before_balanced','after_balanced')) for r in changes)
        return {'rows':changes,'added':added,'removed':removed,'clean':T.wrap(clean,sources(before,after)),
                'complete_comparison':T.wrap(bool(a) and bool(b) and not added and not removed,sources(before,after)),
                'all_bridges_balanced':T.wrap(bool(changes) and all(T.strip(r['bridge_balanced']) for r in changes),sources(before,after))}

    def rollforward(it_,node,opening,events,closing,scope):
        o,c=amount(opening,node),amount(closing,node);sc=identity(scope,node)
        included=[];excluded=[];diagnostics=[];seen={};reversed_amounts={};net=0
        positive={'charge','payment_reversal','credit_reversal'}
        negative={'payment_applied','credit_applied','charge_reversal'}
        informational={'payment_sent','payment_received','receipt_reported','credit_promised','refund_expected','refund_sent','requested','approved'}
        parsed=[]
        for i,original in enumerate(array(events,node)):
            it_.tick(node);r=obj(original,node)
            if any(k not in r for k in ('id','scope','day','stage','amount')):fail(node,'events need id, scope, day, stage, amount')
            ident=identity(r['id'],node);event_scope=identity(r['scope'],node);day=T.strip(r['day']);stage=T.strip(r['stage']);v=amount(r['amount'],node)
            if not isinstance(day,date) or not isinstance(stage,str) or v<0:fail(node,'events need a known date, supported stage and nonnegative money')
            if stage not in positive|negative|informational:fail(node,'unsupported receivable stage '+stage)
            if ident in seen:fail(node,'duplicate event identity')
            seen[ident]=r;parsed.append((i,ident,event_scope,day,stage,v,r,original))
        # Group same-day claims on one original before processing. Earlier-day
        # accepted reversals consume capacity; an overfull same-day batch is held
        # in its entirety rather than selecting a winner by input order.
        batches={};original_sources={x[1]:x[7] for x in parsed}
        for item in parsed:
            i,ident,es,day,stage,v,r,original=item
            if es!=sc or not stage.endswith('_reversal'):continue
            link=T.strip(r.get('reverses'))
            key=(type(link).__name__,link) if isinstance(link,(str,Decimal)) and not isinstance(link,bool) else None
            orig=seen.get(key)
            expected={'charge_reversal':'charge','payment_reversal':'payment_applied','credit_reversal':'credit_applied'}[stage]
            if orig is not None and T.strip(orig['stage'])==expected and identity(orig['scope'],node)==sc and T.strip(orig['day'])<=day:
                batches.setdefault((day,key),[]).append(item)
        blocked=set();batch_sources={}
        for (day,key),group in sorted(batches.items(),key=lambda x:(x[0][0],str(x[0][1]))):
            prior=reversed_amounts.get(key,0);total=sum(x[5] for x in group)
            if prior+total>amount(seen[key]['amount'],node):
                combined=sources([x[7] for x in group],original_sources[key])
                for x in group:blocked.add(x[1]);batch_sources[x[1]]=combined
            else:reversed_amounts[key]=prior+total
        reversed_amounts={}
        # Same-day reversal is allowed only with an explicit original id.
        for i,ident,es,day,stage,v,r,original in sorted(parsed,key=lambda t:(t[3],t[0])):
            it_.tick(node);reason=None
            if es!=sc:reason='other_scope'
            elif stage in informational:reason='stage_does_not_establish_application'
            elif stage.endswith('_reversal'):
                link=T.strip(r.get('reverses'));orig=seen.get((type(link).__name__,link)) if isinstance(link,(str,Decimal)) and not isinstance(link,bool) else None
                original_stage={'charge_reversal':'charge','payment_reversal':'payment_applied','credit_reversal':'credit_applied'}[stage]
                if orig is None:reason='missing_reversal_link'
                elif T.strip(orig['stage'])!=original_stage or identity(orig['scope'],node)!=sc:reason='reversal_stage_or_scope_mismatch'
                elif T.strip(orig['day'])>day:reason='reversal_precedes_original'
                elif ident in blocked:reason='reversal_exceeds_original'
                else:
                    key=identity(orig['id'],node);used=reversed_amounts.get(key,0)
                    if used+v>amount(orig['amount'],node):reason='reversal_exceeds_original'
                    else:reversed_amounts[key]=used+v
            if reason:
                target=excluded if reason in ('other_scope','stage_does_not_establish_application') else diagnostics
                target.append(T.wrap_deep({'index':Decimal(i),'event':original,'reason':reason},batch_sources.get(ident,sources(original))))
                continue
            signed=v if stage in positive else -v;net+=signed
            included.append(T.wrap_deep({'index':Decimal(i),'event':original,'signed_effect':T.Money(signed)},sources(original)))
        src=sources(opening,events,closing,scope)
        return T.wrap_deep({'opening':T.Money(o),'net_applied_activity':T.Money(net),'calculated_closing':T.Money(o+net),
            'claimed_closing':T.Money(c),'gap':T.Money(o+net-c),'balanced':o+net==c,
            'clean':o+net==c and not diagnostics,'included':included,'excluded':excluded,'diagnostics':diagnostics,
            'scope':T.strip(scope),'coverage':'only supplied events; informational stages excluded explicitly'},src)

    def journal(it_,node,lines):
        groups={};accounts={};scopes=set();ids=set();diagnostics=[];raw=array(lines,node)
        for i,original in enumerate(raw):
            it_.tick(node);r=obj(original,node)
            if any(k not in r for k in ('id','entry','scope','account','debit','credit')):fail(node,'journal lines need id, entry, scope, account, debit, credit')
            ident=identity(r['id'],node);entry=identity(r['entry'],node);scope_key=identity(r['scope'],node);acct=identity(r['account'],node)
            d,cr=amount(r['debit'],node),amount(r['credit'],node)
            if d<0 or cr<0 or (d and cr):fail(node,'journal line has one nonnegative debit or credit')
            if ident in ids:diagnostics.append({'index':Decimal(i),'reason':'duplicate_line_id'})
            ids.add(ident);key=(scope_key,entry);groups.setdefault(key,[]).append((r,original))
            akey=(scope_key,acct);accounts[akey]=accounts.get(akey,0)+d-cr;scopes.add(scope_key)
        entries=[]
        for key,items in groups.items():
            rows=[r for r,_ in items]
            debit=sum(amount(r['debit'],node) for r in rows);credit=sum(amount(r['credit'],node) for r in rows)
            entries.append(T.wrap_deep({'scope':T.strip(rows[0]['scope']),'entry':T.strip(rows[0]['entry']),
                'debit':T.Money(debit),'credit':T.Money(credit),'gap':T.Money(debit-credit),
                'balanced':debit==credit and debit>0 and len(rows)>=2,'lines':Decimal(len(rows))},sources([original for _,original in items])))
        src=sources(lines)
        return {'entries':entries,'trial_balances':[T.wrap_deep({'scope':sk[1],'account':ak[1],'net_debit':T.Money(v)},src) for (sk,ak),v in accounts.items()],
                'diagnostics':diagnostics,'clean':T.wrap(bool(raw) and not diagnostics and all(T.strip(e['balanced']) for e in entries),src),
                'coverage':T.wrap('balanced supplied journal entries; counterpart accounts and posting authority require native support',src)}
    bind('budget_bridge',bridge,(2,2));bind('receivable_rollforward',rollforward,(4,4));bind('journal_audit',journal,(1,1))
