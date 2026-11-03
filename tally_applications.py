"""Reviewed invoice application capacities and cumulative billing bridges.

Native evidence supplies identity, account, stage and period. Exact arithmetic
never guesses a remittance link. Tests live in test_applications.py.
"""
from datetime import date
from decimal import Decimal
import tally as T


def install(it):
    def fail(n, m): raise it.err('applications: '+m, n)
    def obj(v,n):
        v=T.strip(v)
        if not isinstance(v,dict):fail(n,'map required')
        return v
    def rows(v,n):
        v=T.strip(v)
        if not isinstance(v,list) or len(v)>2000:fail(n,'at most 2000 rows required')
        return v
    def text(v,n):
        v=T.strip(v)
        if not isinstance(v,str) or not v.strip() or len(v)>4096:fail(n,'bounded nonempty text required')
        return v
    def cash(v,n):
        v=T.strip(v)
        if v is None:return None
        if not isinstance(v,T.Money) or v.cents<0 or len(str(v.cents))>128:fail(n,'nonnegative exact money or nil required')
        return v.cents
    def require(r,keys,n):
        if any(k not in r for k in keys):fail(n,'required fields: '+', '.join(keys))
    def src(*vs):return set().union(*(T.all_sources(v) for v in vs))
    def output(v,*vs):return T.wrap_deep(v,src(*vs))
    def maybe(v):return None if v is None else T.Money(v)

    def payment_application_audit(it_,n,invoices,payments,links):
        inv={};pay={}
        for target,records,amountkey,is_payment in [(inv,invoices,'opening_due',False),(pay,payments,'amount',True)]:
            for original in rows(records,n):
                it_.tick(n);r=obj(original,n);require(r,('id','payee','account',amountkey),n)
                ident=text(r['id'],n)
                if ident in target:fail(n,'duplicate invoice/payment id; canonical event IDs required')
                stage=text(r.get('stage'),n) if is_payment else None
                if is_payment and stage not in ('paid','received','requested','reported','advice','unknown'):fail(n,'explicit payment stage required')
                target[ident]={'id':ident,'payee':text(r['payee'],n),'account':text(r['account'],n),
                               'capacity':cash(r[amountkey],n),'stage':stage,'original':original}
        rr=[];seen=set();by_i={};by_p={}
        for original in rows(links,n):
            it_.tick(n);r=obj(original,n);require(r,('id','invoice','payment','amount','status','date'),n)
            ident=text(r['id'],n)
            if ident in seen:fail(n,'duplicate application event id')
            seen.add(ident);iid=text(r['invoice'],n);pid=text(r['payment'],n);amount=cash(r['amount'],n);status=text(r['status'],n);day=T.strip(r['date'])
            if status not in ('applied','reported','proposed','unknown'):fail(n,'explicit application status required')
            if day is not None and type(day) is not date:fail(n,'application date must be date or nil')
            reasons=[];i=inv.get(iid);p=pay.get(pid)
            if i is None:reasons.append('missing_invoice')
            if p is None:reasons.append('missing_payment')
            if amount is None:reasons.append('unknown_application_amount')
            if status!='applied':reasons.append('application_'+status)
            if p and p['stage'] not in ('paid','received'):reasons.append('payment_stage_'+p['stage'])
            if i and p:
                if i['payee']!=p['payee']:reasons.append('other_payee')
                if i['account']!=p['account']:reasons.append('other_account')
                if i['capacity'] is None:reasons.append('unknown_invoice_capacity')
                if p['capacity'] is None:reasons.append('unknown_payment_capacity')
            ss=src(original,i['original'] if i else None,p['original'] if p else None)
            row={'id':ident,'invoice':iid,'payment':pid,'amount':maybe(amount),'date':day,'reasons':reasons,'_src':ss}
            rr.append(row)
            if not reasons:
                by_i.setdefault(iid,[]).append(row);by_p.setdefault(pid,[]).append(row)
        # Test all candidate links simultaneously. Never choose the first row,
        # clamp a last row, or release a conflict merely by reordering inputs.
        for groups,capacities,reason in [(by_i,inv,'invoice_overallocated'),(by_p,pay,'payment_overallocated')]:
            for ident,group in groups.items():
                if sum(x['amount'].cents for x in group)>capacities[ident]['capacity']:
                    combined=set().union(*(x['_src'] for x in group))
                    for x in group:x['reasons'].append(reason);x['_src']|=combined
        accepted=[];held=[]
        for r in rr:
            ss=r.pop('_src');r['accepted']=not r['reasons'];w=T.wrap_deep(r,ss)
            (accepted if r['accepted'] else held).append(w)
        totals_i={k:0 for k in inv};totals_p={k:0 for k in pay}
        for wrapped in accepted:
            r=T.strip(wrapped);amount=T.strip(r['amount']).cents
            totals_i[T.strip(r['invoice'])]+=amount;totals_p[T.strip(r['payment'])]+=amount
        def summaries(table,totals,axis):
            result=[]
            for ident,r in table.items():
                related=[x for x in accepted+held if T.strip(T.strip(x)[axis])==ident]
                result.append(output({'id':ident,'capacity':maybe(r['capacity']),'accepted_applied':T.Money(totals[ident]),
                    'residual_after_accepted':maybe(None if r['capacity'] is None else r['capacity']-totals[ident]),
                    'has_held_links':any(T.strip(T.strip(x)['accepted']) is False for x in related)},r['original'],related))
            return result
        return {'accepted':accepted,'held':held,'invoices':summaries(inv,totals_i,'invoice'),'payments':summaries(pay,totals_p,'payment'),
                'accepted_total':output(T.Money(sum(totals_i.values())),accepted),
                'clean':output(bool(rr) and not held,invoices,payments,links),
                'complete_timing':output(bool(rr) and all(r['date'] is not None for r in rr),links),
                'meaning':'capacities are reviewed opening amounts; residuals reflect accepted links only, and held links remain unresolved; paid/received are supplied payee-stage annotations, not inferred bank settlement'}

    def progress_bridge(it_,n,previous,current):
        values=[]
        for original in (previous,current):
            r=obj(original,n);require(r,('account','scope','version','through','cumulative','retainage','settlements'),n)
            identity=tuple(text(r[k],n) for k in ('account','scope','version'));day=T.strip(r['through'])
            if day is not None and type(day) is not date:fail(n,'through must be date or nil')
            amounts=tuple(cash(r[k],n) for k in ('cumulative','retainage','settlements'));values.append((identity,day,amounts))
        a,b=values;reasons=[]
        for idx,key in enumerate(('account','scope','version')):
            if a[0][idx]!=b[0][idx]:reasons.append('other_'+key)
        if a[1] is None or b[1] is None:reasons.append('period_unknown')
        elif a[1]>=b[1]:reasons.append('period_not_forward')
        if any(x is None for x in a[2]+b[2]):reasons.append('amount_unknown')
        if reasons:return output({'clean':False,'new_charge':None,'reasons':reasons},previous,current)
        gross,retain,settle=(b[2][j]-a[2][j] for j in range(3));old_due=a[2][0]-a[2][1]-a[2][2];new_due=b[2][0]-b[2][1]-b[2][2]
        if gross<0:reasons.append('cumulative_reduction_or_revision')
        if settle<0:reasons.append('settlement_reversal_or_revision')
        if old_due<0 or new_due<0:reasons.append('negative_due_requires_credit_review')
        return output({'clean':not reasons,'new_charge':maybe(gross) if not reasons else None,'gross_change':T.Money(gross),
            'retainage_change':T.Money(retain),'settlement_change':T.Money(settle),'previous_due':T.Money(old_due),
            'current_due':T.Money(new_due),'due_change':T.Money(new_due-old_due),'reasons':reasons,
            'meaning':'same-account/scope/version cumulative snapshots with explicit baseline; gross increment, retainage and settlement changes stay distinct'},previous,current)

    def invoice_overlap(it_,n,lines):
        groups={};ids=set()
        for original in rows(lines,n):
            it_.tick(n);r=obj(original,n);require(r,('id','invoice','payee','account','item','quantity','rate','amount'),n)
            ident=text(r['id'],n)
            if ident in ids:fail(n,'duplicate reviewed line id')
            ids.add(ident);iid=text(r['invoice'],n);quantity=T.strip(r['quantity']);rate=cash(r['rate'],n);amount=cash(r['amount'],n)
            if not isinstance(quantity,Decimal) or not quantity.is_finite() or quantity<0 or len(quantity.as_tuple().digits)>128 or abs(quantity.as_tuple().exponent)>128:fail(n,'bounded nonnegative decimal quantity required')
            if rate is None or amount is None:fail(n,'known rate and amount required for exact overlap key')
            # Quantity is deliberately part of the key; item/unit/account are
            # reviewed strings. Equality supplies a lead, never de-duplication.
            key=tuple(text(r[k],n) for k in ('payee','account','item'))+(quantity,rate,amount)
            groups.setdefault(key,[]).append((iid,original))
        candidates=[]
        for key,group in groups.items():
            invoices=sorted(set(i for i,_ in group))
            if len(invoices)>1:candidates.append(output({'invoices':invoices,'amount_each':T.Money(key[-1]),
                'lines':[x for _,x in group],'status':'overlap_candidate','automatic_deduction':False},[x for _,x in group]))
        return {'candidates':candidates,'count':output(Decimal(len(candidates)),lines),
                'meaning':'exact reviewed line-key repeats across invoice IDs; delivery/performance records determine whether obligations overlap'}

    def allocation_support(it_,n,resources,claims):
        capacities={}
        for original in rows(resources,n):
            r=obj(original,n);require(r,('id','amount'),n);ident=text(r['id'],n)
            if ident in capacities:fail(n,'duplicate resource id')
            capacities[ident]=cash(r['amount'],n)
        if len(capacities)>64:fail(n,'at most 64 resources')
        cc=[];ids=set()
        for original in rows(claims,n):
            r=obj(original,n);require(r,('id','amount','uses'),n);ident=text(r['id'],n);amount=cash(r['amount'],n)
            if ident in ids:fail(n,'duplicate claim id')
            ids.add(ident);uses=[text(x,n) for x in rows(r['uses'],n)]
            if not uses or len(set(uses))!=len(uses) or any(k not in capacities for k in uses):fail(n,'claims need distinct, existing resource IDs')
            cc.append((ident,amount,uses))
        if not 1<=len(cc)<=16:fail(n,'1..16 claim qubits required')
        feasible=[];unresolved=[];rejected=0
        for state in range(1<<len(cc)):
            it_.tick(n);used={};unknown=False
            for j,(_,amount,uses) in enumerate(cc):
                if state & (1<<(len(cc)-1-j)):
                    for resource in uses:
                        if capacities[resource] is None or amount is None:unknown=True
                        if amount is not None:used[resource]=used.get(resource,0)+amount
            # A known capacity violation excludes a world even if another
            # active claim/resource is unresolved. Unknown is never free money.
            if any(capacities[k] is not None and used[k]>capacities[k] for k in used):rejected+=1
            elif unknown:unresolved.append(Decimal(state))
            else:feasible.append(Decimal(state))
        return output({'qubits':Decimal(len(cc)),'claim_order':[x[0] for x in cc],
            'feasible_states':feasible,'unresolved_states':unresolved,'rejected_count':Decimal(rejected),
            'meaning':'exact declared capacity constraints; q0 is the leftmost claim; feasible does not establish payment/application, and scenario weights are supplied separately'},resources,claims)

    for name,fn,arity in [('payment_application_audit',payment_application_audit,3),('progress_bridge',progress_bridge,2),('invoice_overlap',invoice_overlap,1),('allocation_support',allocation_support,2)]:
        it.builtins.vars[name]=T.Builtin(name,fn,(arity,arity))
