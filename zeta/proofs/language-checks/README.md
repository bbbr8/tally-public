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
