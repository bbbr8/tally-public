/-!
# Arithmetic certificate

Each theorem is one calculation stated in the report, checked by Lean's kernel with whole-number arithmetic.
Rates are pinned by their rounding: `(2R - 1) n ≤ 2 s k < (2R + 1) n` says k / n, scaled by s, rounds to R.
-/
set_option maxRecDepth 100000
set_option exponentiation.threshold 1000000
namespace LangStress.Arithmetic

/-- A01 programs per language, before (blocks A, B, C): 2,000 + 10,000 + 10,000 = 22,000 -/
theorem a01 : 2000 + 10000 + 10000 = 22000 := by decide +kernel
/-- A02 programs per language, after (blocks A, B, C, D): 2,000 + 10,000 + 10,000 + 10,000 = 32,000 -/
theorem a02 : 2000 + 10000 + 10000 + 10000 = 32000 := by decide +kernel
/-- A03 runs before: 3 languages with something to fix: 3 x 22,000 = 66,000 -/
theorem a03 : 3 * 22000 = 66000 := by decide +kernel
/-- A04 runs after: 4 languages: 4 x 32,000 = 128,000 -/
theorem a04 : 4 * 32000 = 128000 := by decide +kernel
/-- A05 all runs re-checked inside Lean: 66,000 + 128,000 = 194,000 -/
theorem a05 : 66000 + 128000 = 194000 := by decide +kernel
/-- A06 Warrant: blocks A + B + C: 495 + 2,338 + 2,291 = 5,124 -/
theorem a06 : 495 + 2338 + 2291 = 5124 := by decide +kernel
/-- A07 CaseLog: blocks A + B + C: 494 + 2,366 + 2,371 = 5,231 -/
theorem a07 : 494 + 2366 + 2371 = 5231 := by decide +kernel
/-- A08 Spectra: blocks A + B + C: 580 + 2,809 + 2,800 = 6,189 -/
theorem a08 : 580 + 2809 + 2800 = 6189 := by decide +kernel
/-- A09 all three languages: 5,124 + 5,231 + 6,189 = 16,544 -/
theorem a09 : 5124 + 5231 + 6189 = 16544 := by decide +kernel
/-- A10 Warrant rate: 5,124 / 22,000 = 23.29% -/
theorem a10 : (2 * 2329 - 1) * 22000 ≤ 20000 * 5124 ∧ 20000 * 5124 < (2 * 2329 + 1) * 22000 := by decide +kernel
/-- A11 CaseLog rate: 5,231 / 22,000 = 23.78% -/
theorem a11 : (2 * 2378 - 1) * 22000 ≤ 20000 * 5231 ∧ 20000 * 5231 < (2 * 2378 + 1) * 22000 := by decide +kernel
/-- A12 Spectra rate: 6,189 / 22,000 = 28.13% -/
theorem a12 : (2 * 2813 - 1) * 22000 ≤ 20000 * 6189 ∧ 20000 * 6189 < (2 * 2813 + 1) * 22000 := by decide +kernel
/-- A13 overall rate: 16,544 / 66,000 = 25.07% -/
theorem a13 : (2 * 2507 - 1) * 66000 ≤ 20000 * 16544 ∧ 20000 * 16544 < (2 * 2507 + 1) * 66000 := by decide +kernel
/-- A14 one program in how many: 66,000 / 16,544 = 3.99 -/
theorem a14 : (2 * 399 - 1) * 16544 ≤ 200 * 66000 ∧ 200 * 66000 < (2 * 399 + 1) * 16544 := by decide +kernel
/-- A15 Warrant block A: 495 / 2,000 = 24.75% -/
theorem a15 : (2 * 2475 - 1) * 2000 ≤ 20000 * 495 ∧ 20000 * 495 < (2 * 2475 + 1) * 2000 := by decide +kernel
/-- A16 Warrant block B: 2,338 / 10,000 = 23.38% -/
theorem a16 : (2 * 2338 - 1) * 10000 ≤ 20000 * 2338 ∧ 20000 * 2338 < (2 * 2338 + 1) * 10000 := by decide +kernel
/-- A17 Warrant block C: 2,291 / 10,000 = 22.91% -/
theorem a17 : (2 * 2291 - 1) * 10000 ≤ 20000 * 2291 ∧ 20000 * 2291 < (2 * 2291 + 1) * 10000 := by decide +kernel
/-- A18 CaseLog block A: 494 / 2,000 = 24.70% -/
theorem a18 : (2 * 2470 - 1) * 2000 ≤ 20000 * 494 ∧ 20000 * 494 < (2 * 2470 + 1) * 2000 := by decide +kernel
/-- A19 CaseLog block B: 2,366 / 10,000 = 23.66% -/
theorem a19 : (2 * 2366 - 1) * 10000 ≤ 20000 * 2366 ∧ 20000 * 2366 < (2 * 2366 + 1) * 10000 := by decide +kernel
/-- A20 CaseLog block C: 2,371 / 10,000 = 23.71% -/
theorem a20 : (2 * 2371 - 1) * 10000 ≤ 20000 * 2371 ∧ 20000 * 2371 < (2 * 2371 + 1) * 10000 := by decide +kernel
/-- A21 Spectra block A: 580 / 2,000 = 29.00% -/
theorem a21 : (2 * 2900 - 1) * 2000 ≤ 20000 * 580 ∧ 20000 * 580 < (2 * 2900 + 1) * 2000 := by decide +kernel
/-- A22 Spectra block B: 2,809 / 10,000 = 28.09% -/
theorem a22 : (2 * 2809 - 1) * 10000 ≤ 20000 * 2809 ∧ 20000 * 2809 < (2 * 2809 + 1) * 10000 := by decide +kernel
/-- A23 Spectra block C: 2,800 / 10,000 = 28.00% -/
theorem a23 : (2 * 2800 - 1) * 10000 ≤ 20000 * 2800 ∧ 20000 * 2800 < (2 * 2800 + 1) * 10000 := by decide +kernel
/-- A24 disagreements after, summed over every result file: 0 in each of 16 files = 0 -/
theorem a24 : 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 + 0 = 0 := by decide +kernel
/-- A25 exact 95% upper bound with 0 failures in 32,000: 1 - 0.025^(1/32,000) = 0.0115% -/
theorem a25 : (999884) ^ 32000 * 40 < (10 ^ 6) ^ 32000 ∧ (10 ^ 6) ^ 32000 < (999885) ^ 32000 * 40 := by decide +kernel
/-- A26 the same bound over all 128,000 runs after: 1 - 0.025^(1/128,000) = 0.00288% -/
theorem a26 : (9999711) ^ 128000 * 40 < (10 ^ 7) ^ 128000 ∧ (10 ^ 7) ^ 128000 < (9999712) ^ 128000 * 40 := by decide +kernel
/-- A28 size of that p-value: 2 x (1/2)^5,124 = (1/2)^5,123 = below 10^-1542 -/
theorem a28 : 10 ^ 1542 < 2 ^ 5123 ∧ 2 ^ 5123 < 10 ^ 1543 := by decide +kernel
/-- A29 Warrant: with a one-item nogood + without: 5,124 + 16,876 = 22,000 -/
theorem a29 : 5124 + 16876 = 22000 := by decide +kernel
/-- A30 Warrant: failures among programs with the trigger: 5,124 of 5,124 = 100% -/
theorem a30 : 5124 = 5124 ∧ 0 = 0 := by decide +kernel
/-- A31 Spectra: closes overdrawn + does not: 6,189 + 15,811 = 22,000 -/
theorem a31 : 6189 + 15811 = 22000 := by decide +kernel
/-- A32 Spectra: failures among overdrawn closes: 6,189 of 6,189 = 100% -/
theorem a32 : 6189 = 6189 ∧ 0 = 0 := by decide +kernel
/-- A33 CaseLog: programs with capitalised quoted names + without: 10,958 + 11,042 = 22,000 -/
theorem a33 : 10958 + 11042 = 22000 := by decide +kernel
/-- A34 CaseLog: wrong facts or answers, with such names: 2,652 / 10,958 = 24.2% -/
theorem a34 : (2 * 242 - 1) * 10958 ≤ 2000 * 2652 ∧ 2000 * 2652 < (2 * 242 + 1) * 10958 := by decide +kernel
/-- A35 CaseLog: wrong facts or answers, without such names: 0 of 11,042 = 0% -/
theorem a35 : 0 = 0 := by decide +kernel
/-- A36 wrong only + wrong and order-dependent + order-dependent only: 1,885 + 767 + 2,579 = 5,231 -/
theorem a36 : 1885 + 767 + 2579 = 5231 := by decide +kernel
/-- A37 programs with a wrong fact or answer: 1,885 + 767 = 2,652 -/
theorem a37 : 1885 + 767 = 2652 := by decide +kernel
/-- A38 programs whose report depended on statement order: 2,579 + 767 = 3,346 -/
theorem a38 : 2579 + 767 = 3346 := by decide +kernel
/-- A39 order-dependent share: 3,346 / 22,000 = 15.2% -/
theorem a39 : (2 * 152 - 1) * 22000 ≤ 2000 * 3346 ∧ 2000 * 3346 < (2 * 152 + 1) * 22000 := by decide +kernel
/-- A40 derived facts with a tier too weak: 1 tier + 2 tiers: 1,315 + 638 = 1,953 -/
theorem a40 : 1315 + 638 = 1953 := by decide +kernel
/-- A41 derived facts with a tier too strong: 1 tier + 2 tiers: 32 + 12 = 44 -/
theorem a41 : 32 + 12 = 44 := by decide +kernel
/-- A42 order-dependent, programs with 1 rule: 223 / 4,382 = 5.1% -/
theorem a42 : (2 * 51 - 1) * 4382 ≤ 2000 * 223 ∧ 2000 * 223 < (2 * 51 + 1) * 4382 := by decide +kernel
/-- A43 order-dependent, programs with 2 rules: 454 / 4,338 = 10.5% -/
theorem a43 : (2 * 105 - 1) * 4338 ≤ 2000 * 454 ∧ 2000 * 454 < (2 * 105 + 1) * 4338 := by decide +kernel
/-- A44 order-dependent, programs with 3 rules: 683 / 4,456 = 15.3% -/
theorem a44 : (2 * 153 - 1) * 4456 ≤ 2000 * 683 ∧ 2000 * 683 < (2 * 153 + 1) * 4456 := by decide +kernel
/-- A45 order-dependent, programs with 4 rules: 868 / 4,276 = 20.3% -/
theorem a45 : (2 * 203 - 1) * 4276 ≤ 2000 * 868 ∧ 2000 * 868 < (2 * 203 + 1) * 4276 := by decide +kernel
/-- A46 order-dependent, programs with 5 rules: 1,118 / 4,548 = 24.6% -/
theorem a46 : (2 * 246 - 1) * 4548 ≤ 2000 * 1118 ∧ 2000 * 1118 < (2 * 246 + 1) * 4548 := by decide +kernel
/-- A47 Spectra payment splits: payments x 6 tracing rules: 86,289 x 6 = 517,734 -/
theorem a47 : 86289 * 6 = 517734 := by decide +kernel
/-- A48 Warrant conclusions (nodes that are not premises): 255,327 - 143,833 = 111,494 -/
theorem a48 : 255327 - 143833 = 111494 := by decide +kernel
/-- A49 Warrant checks: labels, labels under retraction, critical sets: 2 x 255,327 + 111,494 = 622,148 -/
theorem a49 : 2 * 255327 + 111494 = 622148 := by decide +kernel
/-- A50 laws: Concord + CaseLog: 12 + 3 = 15 -/
theorem a50 : 12 + 3 = 15 := by decide +kernel
/-- A51 certificate theorems: laws + result tallies + negative control: 15 + 25 + 1 = 41 -/
theorem a51 : 15 + 25 + 1 = 41 := by decide +kernel
/-- A52 language suites: first pass: 55 - 6 = 49 -/
theorem a52 : 55 - 6 = 49 := by decide +kernel
/-- A53 language suites: final: 55 of 55 = all pass -/
theorem a53 : 55 = 55 := by decide +kernel

end LangStress.Arithmetic
