"""Execute the distribution's synthetic built-in examples."""
import os
os.environ['TALLY_NO_EXPERIMENT_LOG'] = '1'
import tally
import tally_docs

def main():
    reference = tally.reference(verify=False)
    failures = []
    total = 0
    for entry in reference['builtins']:
        if entry['data']:
            continue
        total += 1
        result = tally.verify_example(tally_docs.PRELUDE, entry)
        if result is not True:
            failures.append((entry['name'], str(result)))
    for name, message in failures:
        print('FAIL', name, message)
    print(f'Reference checks: {total-len(failures)}/{total}')
    return 1 if failures else 0

if __name__ == '__main__':
    raise SystemExit(main())
