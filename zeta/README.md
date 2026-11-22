# Zeta

Zeta, originally called Atone, is Bryce Jones’s programming language inspired by the teachings of Jesus Christ. It uses exact fractions and has language rules for independent witnesses, debts paid or borne, judgments by fruits, grace, parables, and restoring earlier values. This portfolio edition runs locally with Python 3.9 or newer and the standard library.

Original language design and handwritten work by Bryce Jones. AI assisted with preparing and testing this portable edition.

## Run the renamed family

Run these commands from the repository root. On macOS, use `python3` if `python` is unavailable.

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
| Riemann | Emmaus | Tabulated zeta zeros and the explicit formula |
| Mertens | Siloam | Möbius and Mertens functions |
| Hardy | Hebron | Hardy’s Z-function and theta function |
| Siegel | Tabor | Riemann–Siegel correction terms |

Each launcher supports `selftest` and `describe --json`. Exact results use fractions. Numerical results are approximations, and precision varies by function and input. The `expect` statements check specific known answers and tolerances.

The examples use synthetic records or mathematical inputs. Each dialect’s `describe` output lists its historical parent languages and its runnable bridges to the parents included here. The original fleet edition provides additional integrations.

## Riemann answer key and Lean results

Bryce’s three-page answer key explains how known mathematical values exposed errors in numerical recipes. The archived scoreboard records 42 checks across the seven renamed languages, including the expected values, measured errors, and tolerances. [Riemann Answer Key](proofs/Riemann-Answer-Key.pdf) · [Namesake scoreboard](proofs/namesake_scoreboard.json)

Two new finite Lean proofs cover the count returned by trial division through 1,000 and the cross-multiplied identity for the four-prime Euler product, 1,225/768. Lean 4.36.0 reports a native-decision axiom for the prime-count check and no axioms for the product identity. Reproduce both with `lean proofs/RiemannKeys.lean`. The Riemann hypothesis is outside the scope of these finite checks. [Lean source](proofs/RiemannKeys.lean) · [Axiom output](proofs/RiemannKeys.results.txt)

The separate finite logic and arithmetic lab records its theorem statements, axiom dependencies, certified instances, tamper checks, and inconclusive results. The nine core theorems were replayed with Lean 4.36.0. The other entries are archived run results. [Core theorem source](proofs/PnpLab.lean) · [Original Lean lab results](proofs/Lean-lab-results.json)
