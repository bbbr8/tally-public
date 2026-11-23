# Zeta language family

Zeta, originally called Atone, is Bryce Jones’s programming language inspired by the teachings of Jesus Christ. It uses exact fractions and has language rules for independent witnesses, debts paid or borne, judgments by fruits, grace, parables, and restoring earlier values. This portfolio edition runs locally with Python 3.9 or newer and the standard library.

Original language design and handwritten work by Bryce Jones. AI assisted with preparing and testing this portable edition.

## Run the seven languages

Run these commands from the directory containing this README. On macOS, use `python3` if `python` is unavailable.

```sh
python zeta/zeta.py run zeta/examples/teachings.zeta
python zeta/zeta.py run zeta/examples/namesake.zeta --json
python euler/euler.py run euler/examples/namesake.euler --json
python gauss/gauss.py run gauss/examples/namesake.gauss --json
python riemann/riemann.py run riemann/examples/namesake.riemann --json
python mertens/mertens.py run mertens/examples/namesake.mertens --json
python hardy/hardy.py run hardy/examples/namesake.hardy --json
python siegel/siegel.py run siegel/examples/namesake.siegel --json
python -m unittest discover
```

| Current name | Former name | Namesake example |
| --- | --- | --- |
| Zeta | Atone | Real zeta values and exact Bernoulli numbers |
| Euler | Cana | Finite Euler products and primes |
| Gauss | Bethany | Prime counting and the logarithmic integral |
| Riemann | Emmaus | Approximate critical-line zero heights and the explicit formula |
| Mertens | Siloam | Möbius and Mertens functions |
| Hardy | Hebron | Hardy’s Z-function and theta function |
| Siegel | Tabor | Riemann–Siegel correction terms |

Each launcher supports `selftest` and `describe --json`. Exact results use fractions. Numerical results are approximations, and precision varies by function and input. The `expect` statements check specific known answers and tolerances.

All seven languages accept UTF-8 source files with or without a byte-order mark for `check` and `run`.

The examples use synthetic records or mathematical inputs. Each dialect’s `describe` output lists its historical parent languages and its runnable bridges to the parents included here. The original fleet edition provides additional integrations.

## Riemann answer key and Lean results

Bryce’s three-page answer key explains how known mathematical values exposed errors in numerical recipes. The archived scoreboard records 42 checks across the seven renamed languages, including the expected values, measured errors, and tolerances. [Riemann Answer Key](proofs/Riemann-Answer-Key.pdf) · [Namesake scoreboard](proofs/namesake_scoreboard.json)

Two new finite Lean proofs cover the count returned by trial division through 1,000 and the cross-multiplied identity for the four-prime Euler product, 1,225/768. Lean 4.36.0 reports a native-decision axiom for the prime-count check and no axioms for the product identity. Reproduce both with `lean proofs/RiemannKeys.lean`. The Riemann hypothesis is outside the scope of these finite checks. [Lean source](proofs/RiemannKeys.lean) · [Axiom output](proofs/RiemannKeys.results.txt)

The separate finite logic and arithmetic lab records its theorem statements, axiom dependencies, certified instances, tamper checks, and inconclusive results. The nine core theorems were replayed with Lean 4.36.0. The other entries are archived run results. [Core theorem source](proofs/PnpLab.lean) · [Original Lean lab results](proofs/Lean-lab-results.json)

## November 22 Riemann runs

Riemann brackets sign changes of a Riemann–Siegel approximation and refines each bracket by bisection. It rounds the resulting heights to 12 decimal places. The original tight check failed at the first zero with an absolute error of 0.000003134183. The follow-up checked the first three heights at a tolerance of 0.00001 and all three passed. At x = 1000.5, the explicit formula truncated to 200 zeros returned about 0.632369 less than the direct prime-power sum. [Original tight check](runs/2026-11-22/run.riemann) · [Follow-up run](runs/2026-11-22/run2.riemann)

The same collection includes Euler’s finite prime product, Gauss’s prime counts through ten million, Hardy’s three sign-change checks, and Mertens values through ten million. The November 22 audit matched all 13 archived reruns to their earlier outputs, including the known discrepancy in Loom’s original bisection. The scoreboards preserve those results alongside the explicit-formula and advanced comparisons. [Runnable programs](runs/2026-11-22) · [Scoreboards and audit](proofs/riemann-results)

## Lean project for the finite logic lab

The formal project contains the sources behind the 34 named theorem results in the lab archive, including the four-variable formula-size table, exact parity bounds, and sum-check soundness. The results identify which theorems rely on compiled finite checks. With Lean 4.36.0 installed, run `lake build` from the formal project directory. [Lean project](proofs/formal) · [Theorem and checker results](proofs/Lean-lab-results.json)

## Lean checks for four companion languages

The language stress checker compares generated answers from CaseLog, Warrant, Spectra, and Concord with Lean reference calculations. The archived post-fix runs recorded zero disagreements in 12,000 cases per language. The public sample contains one synthetic case from each language. [Checker, sample, and run instructions](proofs/language-checks)
