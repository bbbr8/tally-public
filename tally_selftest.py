"""Portable synthetic selftest; never opens a native data store."""
def selftest():
    import tally
    cases = [('1 + 2',3), ('$1.25 + $2.75','$4.00'),
             ('$10.00 - $3.25','$6.75'), ('sum([1,2,3])',6),
             ('len([1,2,3])',3), ('stores()',[]),
             ('sources($1.00 from "DEMO-1")',['DEMO-1'])]
    passed=0
    for expr, expected in cases:
        result=tally.eval_json(expr)
        good=result['ok'] and result['value']==expected
        passed+=good
        if not good: print('FAIL',expr,result.get('error'),result.get('value'))
    result=tally.eval_json('$1.00 + 1')
    passed+=not result['ok']
    total=len(cases)+1
    print(f'portable selftest {passed}/{total}')
    return 0 if passed==total else 1
