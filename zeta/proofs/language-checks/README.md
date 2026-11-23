# Language stress checker

This Lean 4.36.0 project compares encoded runtime results with a reference calculation. CaseLog checks truth and proof provenance. Warrant checks assumptions and retraction. Spectra checks payment allocation and closing holdings. Concord checks proposition composition.

From this directory, build the checker and run all four synthetic cases.

```sh
lake build
lake exe oracle --check examples/agreement.txt
```

The expected output is `SUMMARY cases=4 disagreeing_cases=0`. Check mode exits with status 1 on a disagreement or an empty input. For report-only output, use `lake exe oracle examples/agreement.txt`. Input files use the generators’ space-separated record format, with one record per line.

To verify that the checker catches a wrong answer, run the supplied Concord control. It claims that a proposition at rank 3 has rank 1. The checker prints `K_COMPOSE` and exits with status 1.

```sh
lake exe oracle --check examples/disagreement.txt
```

The November 22 post-fix runs used seeds 0–1,999 and 300,000–309,999. Each language recorded zero disagreements across those 12,000 generated programs. The separate negative-control campaign flagged all 200 deliberately corrupted answers. These counts describe the archived fleet runs. The two commands above replay the small public examples.

## Issued Lean certificate

The full certificate covers four seed ranges. After the fixes, each language agreed with its Lean reference on 32,000 recorded programs. The 25 campaign tallies and the separate rejection of 200 corrupted answers use Lean’s compiled decision procedure (`native_decide`). The certificate also lists 15 laws of the Concord and CaseLog reference semantics. A companion module checks 52 arithmetic statements without axioms. [Issued PDF](certificate/Lean-Certificate.pdf) · [Theorem list, trust assumptions, and input hashes](certificate/Lean-Certificate.md)

To reproduce the full certificate from this directory, use Python 3.9 or newer and Lean 4.36.0. The first command expands the compressed synthetic records and verifies each SHA-256 digest against the issued document. The next two commands build and replay the theorem modules.

```sh
python certificate/restore_inputs.py
lake build LangStress.Certificate LangStress.Arithmetic
lake env leanchecker LangStress.Certificate LangStress.Arithmetic
```
