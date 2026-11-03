"""Exact invoice snapshots, duplicate controls, and explicit contract scope bridges.

Inputs are reviewed annotations. Identity, role, scope and amount basis are
declared, never guessed from filenames or string similarity. Unknown stays nil.
"""
from decimal import Decimal
from datetime import date
import re
import tally as T


def install(it):
    def fail(node, msg): raise it.err('obligations: '+msg, node)
    def obj(v, node):
        v = T.strip(v)
        if not isinstance(v, dict): fail(node, 'map required')
        return v
    def rows(v, node):
        v = T.strip(v)
        if not isinstance(v, list) or len(v) > 2000: fail(node, 'at most 2000 rows required')
        return v
    def text(v, node):
        v = T.strip(v)
        if not isinstance(v, str) or not v.strip() or len(v)>4096: fail(node, 'nonempty bounded text required')
        return v
    def money(v, node, unknown=False):
        v = T.strip(v)
        if unknown and v is None: return None
        if not isinstance(v, T.Money): fail(node, 'exact money required; use nil for unknown')
        if len(str(abs(v.cents))) > 128: fail(node, 'money exceeds 128 digits')
        return v.cents
    def sources(*vs): return set().union(*(T.all_sources(v) for v in vs))
    def invoice_audit(it_, node, records):
        hashes = {}; identities = {}; result = []; conflicts = []
        for original in rows(records, node):
            it_.tick(node); r = obj(original,node)
            required = ('issuer','number','project','kind','basis','sha256','total','settlements','balance','line_amounts')
            if any(k not in r for k in required): fail(node, 'invoice needs '+', '.join(required))
            issuer,num,project,kind,basis,sha = (text(r[k],node) for k in required[:6])
            if not re.fullmatch('[0-9a-f]{64}',sha): fail(node, 'source SHA-256 required')
            if kind not in ('invoice','work_order','contract','quote'): fail(node,'explicit document kind required')
            if basis not in ('project_total','stage_request','incremental_charge','cumulative_charge','unknown'): fail(node,'explicit amount basis required')
            total,settle,bal = (money(r[k],node,True) for k in ('total','settlements','balance'))
            if any(x is not None and x<0 for x in (total,settle,bal)): fail(node,'displayed totals/settlements/balances must be nonnegative')
            lines = T.strip(r['line_amounts'])
            if lines is not None: lines = [money(x,node) for x in rows(lines,node)]
            project_total = money(r.get('project_total'),node,True)
            if project_total is not None and project_total<0:fail(node,'project_total must be nonnegative')
            line_basis=T.strip(r.get('line_basis','total'))
            if line_basis not in ('total','project_total'):fail(node,'line_basis must be total/project_total')
            line_target=project_total if line_basis=='project_total' else total
            signature = (issuer,num,project,kind,basis,total,settle,bal,tuple(lines) if lines is not None else None,project_total,line_basis)
            key = (issuer,num,project)
            duplicate = sha in hashes
            if duplicate and hashes[sha][0] != signature: fail(node,'same bytes have conflicting reviewed annotations')
            if not duplicate:
                hashes[sha] = (signature, len(result)); identities.setdefault(key,[]).append(len(result))
            line_gap = None if lines is None or line_target is None else sum(lines)-line_target
            balance_gap = None if any(x is None for x in (total,settle,bal)) else total-settle-bal
            reasons = []
            if kind != 'invoice': reasons.append('document_role_'+kind)
            if basis not in ('incremental_charge','stage_request'): reasons.append('charge_basis_'+basis)
            if total is None: reasons.append('unknown_total')
            if duplicate: reasons.append('duplicate_bytes')
            if line_gap is None: reasons.append('line_coverage_unknown')
            elif line_gap: reasons.append('line_footing_gap')
            if balance_gap is None: reasons.append('balance_equation_unknown')
            elif balance_gap: reasons.append('balance_equation_gap')
            result.append(T.wrap_deep({'issuer':issuer,'number':num,'project':project,'kind':kind,'basis':basis,'sha256':sha,
                'total':T.Money(total) if total is not None else None,'project_total':T.Money(project_total) if project_total is not None else None,'line_basis':line_basis,
                'duplicate':duplicate,'duplicate_of':Decimal(hashes[sha][1]) if duplicate else None,
                'line_gap':T.Money(line_gap) if line_gap is not None else None,'footed':line_gap==0 if line_gap is not None else None,
                'balance_gap':T.Money(balance_gap) if balance_gap is not None else None,'balance_balanced':balance_gap==0 if balance_gap is not None else None,
                'review_reasons':reasons,'version_conflict':False,
                'charge_candidate':kind=='invoice' and basis in ('incremental_charge','stage_request') and total is not None and not duplicate and line_gap in (0,None) and balance_gap in (0,None)},sources(original)))
        for key, idxs in identities.items():
            if len(idxs)>1:
                conflicts.append({'identity':list(key),'rows':[Decimal(i) for i in idxs]})
                # Every copy of any conflicting snapshot is held, regardless of input order.
                affected={T.strip(T.strip(result[i])['sha256']) for i in idxs}
                for row in result:
                    raw=T.strip(row)
                    if T.strip(raw['sha256']) in affected:
                        ss=sources(row);raw['version_conflict']=T.wrap(True,ss);raw['charge_candidate']=T.wrap(False,ss)
        summaries={}
        for row in result:
            r=T.strip(row)
            if T.strip(r['charge_candidate']):
                project=T.strip(r['project']);summaries.setdefault(project,[]).append(row)
        totals=[]
        for project,rr in summaries.items():
            totals.append(T.wrap_deep({'project':project,'candidate_total':T.Money(sum(T.strip(T.strip(r)['total']).cents for r in rr)),
                                     'count':Decimal(len(rr)),'meaning':'reviewed charge candidates; application, authorization and net liability remain separate'},sources(rr)))
        return {'rows':result,'version_conflicts':conflicts,'project_totals':totals,
                'unique_documents':T.wrap(Decimal(len(hashes)),sources(records)),
                'coverage':T.wrap('supplied reviewed annotations; byte copies deduplicated, different snapshots held for version review',sources(records))}

    def contract_bridge(it_,node,target,terms):
        r=obj(target,node)
        if any(k not in r for k in ('project','version','scope','amount')):fail(node,'target needs project, version, scope, amount')
        project,version,scope=(text(r[k],node) for k in ('project','version','scope'));expected=money(r['amount'],node)
        used=[];held=[];ids=set();net=0
        for original in rows(terms,node):
            it_.tick(node);x=obj(original,node)
            if any(k not in x for k in ('id','project','version','effect','amount','status')):fail(node,'terms need id, project, version, effect, amount, status')
            ident=text(x['id'],node)
            if ident in ids:fail(node,'duplicate component identity')
            ids.add(ident);pr=text(x['project'],node);ve=text(x['version'],node);effect=text(x['effect'],node);status=text(x['status'],node);amount=money(x['amount'],node,True)
            if effect not in ('add','subtract') or status not in ('documented','open','disputed'):fail(node,'term effect add/subtract and status documented/open/disputed required')
            if amount is not None and amount<0:fail(node,'term amount nonnegative; sign belongs in effect')
            reasons=[]
            if pr!=project:reasons.append('other_project')
            if ve!=version:reasons.append('other_version')
            # Older reviewed components without scope retain their explicitly
            # mapped target scope. An explicit scope may never be ignored.
            term_scope=text(x['scope'],node) if 'scope' in x else scope
            if term_scope!=scope:reasons.append('other_scope')
            if status!='documented':reasons.append('status_'+status)
            if amount is None:reasons.append('amount_unknown')
            if reasons:held.append(T.wrap_deep({'term':original,'reasons':reasons},sources(original)));continue
            signed=amount if effect=='add' else -amount;net+=signed
            used.append(T.wrap_deep({'term':original,'signed_effect':T.Money(signed),
                'scope':term_scope,'scope_basis':'explicit' if 'scope' in x else 'caller_mapped_target'},sources(original)))
        ss=sources(target,terms)
        return T.wrap_deep({'project':project,'version':version,'scope':scope,'represented_amount':T.Money(expected),
            'component_total':T.Money(net),'gap':T.Money(net-expected),'balanced':bool(used) and net==expected,
            'complete':bool(used) and not held,'clean':bool(used) and not held and net==expected,'included':used,'held':held,
            'meaning':'arithmetic of explicitly mapped same-project/version components; documented status is supplied, execution and authorization require separate record review'},ss)
    it.builtins.vars['invoice_audit']=T.Builtin('invoice_audit',invoice_audit,(1,1))
    it.builtins.vars['contract_bridge']=T.Builtin('contract_bridge',contract_bridge,(2,2))

    def change_order_audit(it_,node,contract,changes):
        c=obj(contract,node)
        if any(k not in c for k in ('project','version','requirement')):fail(node,'contract needs project/version/requirement')
        project,version,requirement=(text(c[k],node) for k in ('project','version','requirement'))
        if requirement!='advance_both':fail(node,'supported clause model: advance_both')
        out=[];seen=set()
        for original in rows(changes,node):
            it_.tick(node);r=obj(original,node)
            if any(k not in r for k in ('id','project','version','amount','written','buyer_signed','seller_signed','work_start')):fail(node,'change needs id/project/version/amount/written/buyer_signed/seller_signed/work_start')
            ident=text(r['id'],node)
            if ident in seen:fail(node,'duplicate change id')
            seen.add(ident);pr=text(r['project'],node);ve=text(r['version'],node);amount=money(r['amount'],node,True)
            written=T.strip(r['written']);dates=[T.strip(r[k]) for k in ('buyer_signed','seller_signed','work_start')]
            if written is not None and type(written) is not bool:fail(node,'written must be bool or nil')
            if any(d is not None and type(d) is not date for d in dates):fail(node,'signature/work dates must be known dates or nil')
            reasons=[];passed=None
            if pr!=project:reasons.append('other_project')
            if ve!=version:reasons.append('other_version')
            if not reasons:
                b,s,w=dates
                if written is False:passed=False;reasons.append('written_requirement_failed')
                elif w is not None and any(d is not None and d>w for d in (b,s)):
                    passed=False;reasons.append('signature_after_work_start')
                elif written is None or any(d is None for d in dates):reasons.append('missing_execution_or_start_bridge')
                elif b==w or s==w:reasons.append('same_day_order_unknown')
                else:passed=True
            out.append(T.wrap_deep({'id':ident,'amount':T.Money(amount) if amount is not None else None,
                'passes_clause':passed,'reasons':reasons,'meaning':'supplied clause and inspected timing annotations; amount/payment/application remain separate'},sources(contract,original)))
        return {'rows':out,'all_pass':T.wrap(bool(out) and all(T.strip(T.strip(x)['passes_clause']) is True for x in out),sources(contract,changes))}
    it.builtins.vars['change_order_audit']=T.Builtin('change_order_audit',change_order_audit,(2,2))
