"""Signed document equations, dated milestone gates and joint logical support.

Inputs are reviewed annotations. Native interpretation and legal validity stay
with the source review. Public regressions live in test_terms.py.
"""
from datetime import date
from decimal import Decimal
import tally as T


def install(it):
    def fail(n,m):raise it.err('terms: '+m,n)
    def obj(v,n):
        v=T.strip(v)
        if not isinstance(v,dict):fail(n,'map required')
        return v
    def rows(v,n,limit=2000):
        v=T.strip(v)
        if not isinstance(v,list) or len(v)>limit:fail(n,'bounded list required')
        return v
    def text(v,n):
        v=T.strip(v)
        if not isinstance(v,str) or not v.strip() or len(v)>4096:fail(n,'bounded nonempty text required')
        return v
    def cash(v,n):
        v=T.strip(v)
        if v is None:return None
        if not isinstance(v,T.Money) or len(str(abs(v.cents)))>128:fail(n,'exact bounded money or nil required')
        return v.cents
    def boolean(v,n):
        v=T.strip(v)
        if v is not None and type(v) is not bool:fail(n,'bool or nil required')
        return v
    def day(v,n):
        v=T.strip(v)
        if v is not None and type(v) is not date:fail(n,'date or nil required')
        return v
    def require(r,keys,n):
        if any(k not in r for k in keys):fail(n,'required fields: '+', '.join(keys))
    def src(*vs):return set().union(*(T.all_sources(v) for v in vs))
    def output(v,*vs):return T.wrap_deep(v,src(*vs))
    def money(v):return T.Money(v) if v is not None else None

    def bill_equation(it_,n,document):
        r=obj(document,n);require(r,('kind','status','line_amounts','subtotal','discount','tax','total','adjustments','balance'),n)
        kind=text(r['kind'],n);status=text(r['status'],n)
        if kind not in ('invoice','credit_memo','sales_order','quote','contract'):fail(n,'explicit invoice/credit_memo/sales_order/quote/contract kind required')
        if status not in ('issued','requested','draft','unknown'):fail(n,'explicit document status required')
        subtotal,discount,tax,total,adjustments,balance=(cash(r[k],n) for k in ('subtotal','discount','tax','total','adjustments','balance'))
        if discount is not None and discount<0:fail(n,'discount is a nonnegative reduction or nil')
        lines=T.strip(r['line_amounts'])
        if lines is not None:lines=[cash(v,n) for v in rows(lines,n)]
        line_gap=None if lines is None or subtotal is None or None in lines else sum(lines)-subtotal
        tax_gap=None if None in (subtotal,discount,tax,total) else subtotal-discount+tax-total
        balance_gap=None if None in (total,adjustments,balance) else total+adjustments-balance
        reasons=[]
        if kind not in ('invoice','credit_memo'):reasons.append('unposted_document_role_'+kind)
        if status!='issued':reasons.append('status_'+status)
        if total is None:reasons.append('total_unknown')
        if total is not None and ((kind=='invoice' and total<0) or (kind=='credit_memo' and total>0)):reasons.append('document_sign_conflict')
        for name,gap in [('line',line_gap),('tax',tax_gap),('balance',balance_gap)]:
            if gap is None:reasons.append(name+'_equation_unknown')
            elif gap:reasons.append(name+'_equation_gap')
        candidate=kind in ('invoice','credit_memo') and status=='issued' and total is not None and 'document_sign_conflict' not in reasons and all(x in (0,None) for x in (line_gap,tax_gap,balance_gap))
        return output({'kind':kind,'status':status,'total':money(total),'displayed_adjustments':money(adjustments),
            'line_gap':money(line_gap),'tax_gap':money(tax_gap),'balance_gap':money(balance_gap),
            'fully_reconciled':all(x==0 for x in (line_gap,tax_gap,balance_gap)),
            'account_effect_candidate':money(total) if candidate else None,'reasons':reasons,
            'payment_component':None,'credit_component':None,
            'meaning':'signed reviewed equations; candidate is document-face account effect, with posting, invoice allocation and mixed payment/credit components requiring separate records'},document)

    def milestone_schedule(it_,n,contract,milestones,observations,asof):
        c=obj(contract,n);require(c,('project','version','scope','payer','payee','signed','effective_on'),n)
        identity=tuple(text(c[k],n) for k in ('project','version','scope','payer','payee'));signed=boolean(c['signed'],n);effective=day(c['effective_on'],n);cutoff=day(asof,n)
        if cutoff is None:fail(n,'known as-of date required')
        facts={}
        for original in rows(observations,n):
            r=obj(original,n);require(r,('id','project','version','value','as_of'),n);ident=text(r['id'],n)
            if ident in facts:fail(n,'duplicate condition observation ID')
            facts[ident]=(r,original,boolean(r['value'],n),day(r['as_of'],n),text(r['project'],n),text(r['version'],n))
        out=[];held=[];ids=set()
        for original in rows(milestones,n):
            it_.tick(n);r=obj(original,n);require(r,('id','project','version','scope','payer','payee','amount','requires'),n);ident=text(r['id'],n)
            if ident in ids:fail(n,'duplicate milestone ID')
            ids.add(ident);key=tuple(text(r[k],n) for k in ('project','version','scope','payer','payee'));amount=cash(r['amount'],n)
            if amount is not None and amount<0:fail(n,'milestone amount must be nonnegative')
            reasons=['other_'+k for j,k in enumerate(('project','version','scope','payer','payee')) if key[j]!=identity[j]]
            requirements=[text(v,n) for v in rows(r['requires'],n,64)]
            if len(set(requirements))!=len(requirements):fail(n,'duplicate milestone condition ID')
            if reasons:held.append(output({'id':ident,'reasons':reasons,'milestone':original},contract,original));continue
            states=[signed];reasons=[];related=[]
            if signed is None:reasons.append('signature_state_unknown')
            elif signed is False:reasons.append('not_signed')
            if effective is None:states.append(None);reasons.append('effective_date_unknown')
            elif effective>cutoff:states.append(False);reasons.append('not_effective_as_of')
            for name in requirements:
                fact=facts.get(name);state=None
                if fact is None:reasons.append('condition_missing:'+name)
                else:
                    rr,source,value,date_,project,version=fact;related.append(source)
                    if project!=identity[0] or version!=identity[1]:reasons.append('condition_other_project_or_version:'+name)
                    elif date_!=cutoff:reasons.append('condition_as_of_mismatch:'+name)
                    else:
                        state=value
                        if value is None:reasons.append('condition_unknown:'+name)
                        elif value is False:reasons.append('condition_false:'+name)
                states.append(state)
            eligible=False if False in states else (None if None in states else True)
            out.append(output({'id':ident,'payer':identity[3],'payee':identity[4],'amount':money(amount),'eligible':eligible,'requires':requirements,'reasons':reasons,
                'meaning':'eligibility under supplied literal milestone/signature/date model; cash payment and legal enforceability stay separate'},contract,original,related,asof))
        def total(rr):
            values=[T.strip(T.strip(r)['amount']) for r in rr]
            return None if any(x is None for x in values) else T.Money(sum(x.cents for x in values))
        eligible=[r for r in out if T.strip(T.strip(r)['eligible']) is True];unknown=[r for r in out if T.strip(T.strip(r)['eligible']) is None]
        return {'rows':out,'held':held,'scheduled_total':output(total(out),milestones),'eligible_total':output(total(eligible),eligible),
            'unresolved_total':output(total(unknown),unknown),'complete':output(bool(out) and not held and not unknown and all(T.strip(T.strip(r)['amount']) is not None for r in out),contract,milestones,observations,asof),
            'as_of':asof,'meaning':'observations are explicitly reviewed states at the requested date; states at other dates remain open, without inferred retroactive knowledge or continued truth'}

    def logic_support(it_,n,variables,facts,rules):
        names=[text(v,n) for v in rows(variables,n,16)]
        if not names or len(set(names))!=len(names):fail(n,'1..16 distinct variable IDs required')
        supplied=obj(facts,n)
        if any(k not in names for k in supplied):fail(n,'fact names an unknown variable')
        fixed={k:boolean(v,n) for k,v in supplied.items()};tests=[]
        for original in rows(rules,n,128):
            r=obj(original,n);require(r,('kind','members'),n);kind=text(r['kind'],n);members=[text(v,n) for v in rows(r['members'],n,16)]
            if kind not in ('requires','at_most_one','exactly_one'):fail(n,'rule kind requires/at_most_one/exactly_one required')
            if len(members)<2 or len(set(members))!=len(members) or any(v not in names for v in members):fail(n,'rules need distinct existing members')
            tests.append((kind,[names.index(v) for v in members]))
        allowed=[];rejected=0
        for state in range(1<<len(names)):
            it_.tick(n);bits=[bool(state&(1<<(len(names)-1-j))) for j in range(len(names))]
            valid=all(v is None or bits[names.index(k)]==v for k,v in fixed.items())
            for kind,indices in tests:
                selected=[bits[j] for j in indices]
                if kind=='requires':valid=valid and (not selected[0] or all(selected[1:]))
                elif kind=='at_most_one':valid=valid and sum(selected)<=1
                else:valid=valid and sum(selected)==1
            if valid:allowed.append(Decimal(state))
            else:rejected+=1
        return output({'qubits':Decimal(len(names)),'variable_order':names,'allowed_states':allowed,'rejected_count':Decimal(rejected),
            'satisfiable':bool(allowed),'unknown_variables':[name for name in names if fixed.get(name) is None],
            'meaning':'joint worlds under supplied observations and logical requirements; q0 is leftmost, nil facts remain free, and weights/legal elements are separate'},variables,facts,rules)

    for name,fn,arity in [('bill_equation',bill_equation,1),('milestone_schedule',milestone_schedule,4),('logic_support',logic_support,3)]:
        it.builtins.vars[name]=T.Builtin(name,fn,(arity,arity))
