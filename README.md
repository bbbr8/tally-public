# Tally

Tally is a programming language for exact money, dates, source-linked values, rules, reconciliation and explicitly modeled scenarios. This portable distribution contains interpreter source and synthetic checks. It includes no personal records or preconfigured private data stores.

## Run on Windows or Mac

Install Python 3.12 or newer from python.org. Download and extract this repository, then run these commands from its folder:

```sh
python tally.py --selftest
python tally.py eval "1 + 2" --json
python tally.py describe --json
```

On Mac use `python3` if `python` is unavailable. Windows users can double-click `Start-Tally.cmd`; Mac users can run `bash Start-Tally.command`. The launchers verify Python and the portable checks before opening the interactive REPL.

Core execution needs only Python's standard library. Optional PDF reading uses PyMuPDF: install with `python -m pip install -r requirements-pdf.txt`. No hosted AI service or API key is required. Semantic or quantum outputs describe supplied models and assumptions; they are not measurements of external reality.

## Exact arithmetic and source tracking

```text
let price = $12.50 from "DEMO-PRICE"
let fee = $2.25 from "DEMO-FEE"
print(price + fee)
print(sources(price + fee))
```

Save as `example.tly`, then run `python tally.py run example.tly --json`. All examples here are synthetic.

## AI integration

Read `AI_GUIDE.md`. `tally.py serve` accepts JSON-lines requests. `describe --json` exposes the language reference. `tally_client.py` provides the Python client.

## Source configuration

Private-store discovery is disabled by default (`stores()` returns an empty list). Generic file import functions accept user-supplied paths. The optional `TALLY_BANK_DB` environment variable selects a compatible, user-owned bank database for the legacy bank adapter; it is not a general CSV importer. Review its expected schema in `tally_data.py` before use.

## Validation and scope

The Mac export passed eight portable self-checks and 221 executable reference examples. `VALIDATION.json` records those results. This portable check set replaces the original environment-specific selftest; it is not the complete upstream regression suite. Run `python verify_reference.py` to repeat reference checks. Windows/Mac launcher integration and optional PDF installation are separate from interpreter checks.

The export excludes private evaluation scripts, local datasets, experiment histories and the original Git history. Source examples and defaults were sanitized on the source machine before transfer. `SOURCE_MANIFEST.json` fingerprints the interpreter modules.
