# Lean certificate: stress test of four case languages

Issued 2026-11-22 · Lean (version 4.36.0, arm64-apple-darwin24.6.0, commit 611c117bfaf7b7ae1cfcf246ce6fba31e8f509e9, Release)

## What this certifies

1. **15 laws hold for every possible input.** They were proved by Lean's kernel, not sampled.
2. **25 tallies are exact.** Each says: this result file holds *n* programs, and on exactly *d* of them the answer the
   runtime gave differs from the Lean reference semantics. Lean re-runs its own reference check over the whole file when the
   project is built; a single wrong count fails the build.
3. **The checker rejects wrong answers.** 200 answers that agreed were each corrupted in one place; Lean rejects all 200.

Build: completed, 0 errors. Independent kernel replay (leanchecker): passed. No external libraries.

## The tallies

`before` = the runtimes as they stood before the fixes. `after` = the fixed runtimes. Blocks A to D are separate seed ranges.

| Theorem | Language | State | Block | Programs | Disagreements |
|---|---|---|---|---:|---:|
| `warrant_before_A_tally` | Warrant | before | A (seeds from 0) | 2,000 | 495 |
| `warrant_after_A_tally` | Warrant | after | A (seeds from 0) | 2,000 | 0 |
| `caselog_before_A_tally` | CaseLog | before | A (seeds from 0) | 2,000 | 494 |
| `caselog_after_A_tally` | CaseLog | after | A (seeds from 0) | 2,000 | 0 |
| `spectra_before_A_tally` | Spectra | before | A (seeds from 0) | 2,000 | 580 |
| `spectra_after_A_tally` | Spectra | after | A (seeds from 0) | 2,000 | 0 |
| `concord_after_A_tally` | Concord | after | A (seeds from 0) | 2,000 | 0 |
| `warrant_before_B_tally` | Warrant | before | B (seeds from 100,000) | 10,000 | 2,338 |
| `warrant_after_B_tally` | Warrant | after | B (seeds from 100,000) | 10,000 | 0 |
| `caselog_before_B_tally` | CaseLog | before | B (seeds from 100,000) | 10,000 | 2,366 |
| `caselog_after_B_tally` | CaseLog | after | B (seeds from 100,000) | 10,000 | 0 |
| `spectra_before_B_tally` | Spectra | before | B (seeds from 100,000) | 10,000 | 2,809 |
| `spectra_after_B_tally` | Spectra | after | B (seeds from 100,000) | 10,000 | 0 |
| `concord_after_B_tally` | Concord | after | B (seeds from 100,000) | 10,000 | 0 |
| `warrant_before_C_tally` | Warrant | before | C (seeds from 200,000) | 10,000 | 2,291 |
| `warrant_after_C_tally` | Warrant | after | C (seeds from 200,000) | 10,000 | 0 |
| `caselog_before_C_tally` | CaseLog | before | C (seeds from 200,000) | 10,000 | 2,371 |
| `caselog_after_C_tally` | CaseLog | after | C (seeds from 200,000) | 10,000 | 0 |
| `spectra_before_C_tally` | Spectra | before | C (seeds from 200,000) | 10,000 | 2,800 |
| `spectra_after_C_tally` | Spectra | after | C (seeds from 200,000) | 10,000 | 0 |
| `concord_after_C_tally` | Concord | after | C (seeds from 200,000) | 10,000 | 0 |
| `warrant_after_D_tally` | Warrant | after | D (seeds from 300,000) | 10,000 | 0 |
| `caselog_after_D_tally` | CaseLog | after | D (seeds from 300,000) | 10,000 | 0 |
| `spectra_after_D_tally` | Spectra | after | D (seeds from 300,000) | 10,000 | 0 |
| `concord_after_D_tally` | Concord | after | D (seeds from 300,000) | 10,000 | 0 |
| `negative_controls_all_rejected` | all four | corrupted | drawn from block D | 200 | 200 |

Totals: before 66,000 programs, 16,544 disagreements · after 128,000 programs, 0 disagreements.

## The laws

| Theorem | Statement in plain words | Axioms used |
|---|---|---|
| `Concord.allOf_comm` | all_of gives the same result whatever the order of its inputs | propext |
| `Concord.anyOf_comm` | any_of gives the same result whatever the order of its inputs | propext |
| `Concord.allOf_assoc` | nesting all_of inside all_of changes nothing | propext |
| `Concord.anyOf_assoc` | nesting any_of inside any_of changes nothing | propext |
| `Concord.allOf_idem` | repeating an input of all_of changes nothing | propext |
| `Concord.anyOf_idem` | repeating an input of any_of changes nothing | propext |
| `Concord.conflict_poisons_all` | an all_of holding a CONFLICT is CONFLICT | propext |
| `Concord.conflict_poisons_any` | an any_of holding a CONFLICT is CONFLICT | propext |
| `Concord.all_le_any` | all_of never ranks above any_of of the same inputs | propext |
| `Concord.allOf_mono` | raising one input never lowers an all_of | propext |
| `Concord.anyOf_mono` | raising one input never lowers an any_of | propext |
| `Concord.allOf_stands` | all_of reaches STANDS exactly when every input stands | propext |
| `CaseLog.truth_knowledge_mono` | adding support moves an answer only from NEITHER toward BOTH, never back | none |
| `CaseLog.truth_both_iff` | the answer is BOTH exactly when the fact and its denial are both held | none |
| `CaseLog.truth_neither_iff` | the answer is NEITHER exactly when neither is held | none |

## The arithmetic

52 calculations stated in the report are theorems in `Arithmetic.lean`, proved by Lean's kernel with whole-number arithmetic. 52 of them use no axiom. A deliberately wrong sum is rejected; kernel replay: passed.

| No. | Calculation | Result |
|---|---|---:|
| A01 | programs per language, before (blocks A, B, C): 2,000 + 10,000 + 10,000 | 22,000 |
| A02 | programs per language, after (blocks A, B, C, D): 2,000 + 10,000 + 10,000 + 10,000 | 32,000 |
| A03 | runs before: 3 languages with something to fix: 3 x 22,000 | 66,000 |
| A04 | runs after: 4 languages: 4 x 32,000 | 128,000 |
| A05 | all runs re-checked inside Lean: 66,000 + 128,000 | 194,000 |
| A06 | Warrant: blocks A + B + C: 495 + 2,338 + 2,291 | 5,124 |
| A07 | CaseLog: blocks A + B + C: 494 + 2,366 + 2,371 | 5,231 |
| A08 | Spectra: blocks A + B + C: 580 + 2,809 + 2,800 | 6,189 |
| A09 | all three languages: 5,124 + 5,231 + 6,189 | 16,544 |
| A10 | Warrant rate: 5,124 / 22,000 | 23.29% |
| A11 | CaseLog rate: 5,231 / 22,000 | 23.78% |
| A12 | Spectra rate: 6,189 / 22,000 | 28.13% |
| A13 | overall rate: 16,544 / 66,000 | 25.07% |
| A14 | one program in how many: 66,000 / 16,544 | 3.99 |
| A15 | Warrant block A: 495 / 2,000 | 24.75% |
| A16 | Warrant block B: 2,338 / 10,000 | 23.38% |
| A17 | Warrant block C: 2,291 / 10,000 | 22.91% |
| A18 | CaseLog block A: 494 / 2,000 | 24.70% |
| A19 | CaseLog block B: 2,366 / 10,000 | 23.66% |
| A20 | CaseLog block C: 2,371 / 10,000 | 23.71% |
| A21 | Spectra block A: 580 / 2,000 | 29.00% |
| A22 | Spectra block B: 2,809 / 10,000 | 28.09% |
| A23 | Spectra block C: 2,800 / 10,000 | 28.00% |
| A24 | disagreements after, summed over every result file: 0 in each of 16 files | 0 |
| A25 | exact 95% upper bound with 0 failures in 32,000: 1 - 0.025^(1/32,000) | 0.0115% |
| A26 | the same bound over all 128,000 runs after: 1 - 0.025^(1/128,000) | 0.00288% |
| A28 | size of that p-value: 2 x (1/2)^5,124 = (1/2)^5,123 | below 10^-1542 |
| A29 | Warrant: with a one-item nogood + without: 5,124 + 16,876 | 22,000 |
| A30 | Warrant: failures among programs with the trigger: 5,124 of 5,124 | 100% |
| A31 | Spectra: closes overdrawn + does not: 6,189 + 15,811 | 22,000 |
| A32 | Spectra: failures among overdrawn closes: 6,189 of 6,189 | 100% |
| A33 | CaseLog: programs with capitalised quoted names + without: 10,958 + 11,042 | 22,000 |
| A34 | CaseLog: wrong facts or answers, with such names: 2,652 / 10,958 | 24.2% |
| A35 | CaseLog: wrong facts or answers, without such names: 0 of 11,042 | 0% |
| A36 | wrong only + wrong and order-dependent + order-dependent only: 1,885 + 767 + 2,579 | 5,231 |
| A37 | programs with a wrong fact or answer: 1,885 + 767 | 2,652 |
| A38 | programs whose report depended on statement order: 2,579 + 767 | 3,346 |
| A39 | order-dependent share: 3,346 / 22,000 | 15.2% |
| A40 | derived facts with a tier too weak: 1 tier + 2 tiers: 1,315 + 638 | 1,953 |
| A41 | derived facts with a tier too strong: 1 tier + 2 tiers: 32 + 12 | 44 |
| A42 | order-dependent, programs with 1 rule: 223 / 4,382 | 5.1% |
| A43 | order-dependent, programs with 2 rules: 454 / 4,338 | 10.5% |
| A44 | order-dependent, programs with 3 rules: 683 / 4,456 | 15.3% |
| A45 | order-dependent, programs with 4 rules: 868 / 4,276 | 20.3% |
| A46 | order-dependent, programs with 5 rules: 1,118 / 4,548 | 24.6% |
| A47 | Spectra payment splits: payments x 6 tracing rules: 86,289 x 6 | 517,734 |
| A48 | Warrant conclusions (nodes that are not premises): 255,327 - 143,833 | 111,494 |
| A49 | Warrant checks: labels, labels under retraction, critical sets: 2 x 255,327 + 111,494 | 622,148 |
| A50 | laws: Concord + CaseLog: 12 + 3 | 15 |
| A51 | certificate theorems: laws + result tallies + negative control: 15 + 25 + 1 | 41 |
| A52 | language suites: first pass: 55 - 6 | 49 |
| A53 | language suites: final: 55 of 55 | all pass |

## What each kind of theorem rests on

| Kind | Count | Checked by | Rests on |
|---|---:|---|---|
| Laws | 15 | Lean's kernel, by exhausting every case | no axiom, or only `propext` |
| Tallies and negative control | 26 | Lean's compiled evaluator running the reference check | `propext`, `Classical.choice`, `Quot.sound`, and one evaluation axiom per theorem (`native_decide`) |
| Arithmetic | 52 | Lean's kernel, whole numbers | no axiom |

The reference semantics is written from each language's definitions (minimal consistent environments for Warrant; least fixpoint,
four-valued answers, best tier and proof certificates for CaseLog; lattice composition for Concord; the tracing doctrines in exact
fractions for Spectra, with lowest-intermediate-balance checked against owner-last). The result files were recorded by generator
scripts that call the real runtimes; their fingerprints follow, so a later build can be tied to exactly these files.

## Fingerprints (SHA-256)

### Result files embedded in the proofs

| File | Programs | SHA-256 |
|---|---:|---|
| warrant_before_A.txt | 2,000 | `c6205706f0c9010c043bba866bb8509e11fe28f44de3764aaa3a3a05aeda6ef2` |
| warrant_after_A.txt | 2,000 | `23d4e877a51cf05256492fa894aca13c48dbf06aa78d1dc9c28698c44b4b0ca4` |
| caselog_before_A.txt | 2,000 | `71937d3d8510d44e48f598b218775bb72218b6ee3cc6078cd929e8431f9eb150` |
| caselog_after_A.txt | 2,000 | `0167d7573a2f32a1baa6ccfd3957f6a8fbf2d263749a8786da74b4fef71612b5` |
| spectra_before_A.txt | 2,000 | `5e6d7a574630bd2cb2048074f6cde4a7841f867bf58fb6372dc1245014c94014` |
| spectra_after_A.txt | 2,000 | `856603bed22ce0aea2f06f3ff0d8b35a93e1257c8e5012e4e66f8d860746b8de` |
| concord_after_A.txt | 2,000 | `d7fbcee1da0c5b2f2a809c6f99c6bb84e1c45beaa3521bee83a5c9d744386edb` |
| warrant_before_B.txt | 10,000 | `20e5cc9cc98cedd61c8b5e8261ebad604ca2930adf70681eb44d7a723bff5c4b` |
| warrant_after_B.txt | 10,000 | `dc5025296fd988562b389fae58fc6f781742cce760c0ac183131d9ca7b605f55` |
| caselog_before_B.txt | 10,000 | `70dfa35951d6a7bb9b6f75ba31b9134062eab1755e64f983141a19147b7ecd86` |
| caselog_after_B.txt | 10,000 | `0352ad6365b67744e5097bc744e3dc0d1f7919d955d96a2313455b72253e7031` |
| spectra_before_B.txt | 10,000 | `dae9caf2aba8e2ed75519004197df64c0c69c06ac6d4a21456eb05cb15df3fec` |
| spectra_after_B.txt | 10,000 | `b8e90bd79583446a5642829ba88754cb5a608d4b8504f200b5588f76c6741e1c` |
| concord_after_B.txt | 10,000 | `ef1e7c589fdc440800f86f609cf7c113c935fed7f66e1ac163d855128cdd790a` |
| warrant_before_C.txt | 10,000 | `ab2f9e584d1355a7ecebe75da8e9ca44cc5a5bd30b96f7cc62da6377d00b3942` |
| warrant_after_C.txt | 10,000 | `bb9bef35558a4be8c90ccd99bcbe8739ad3d538a15f5294bf1324d1fe42afb8e` |
| caselog_before_C.txt | 10,000 | `7277532d9cd807a91b4bb5e37e8ec888312e094c7f475e9a29d8e7716b5a37a3` |
| caselog_after_C.txt | 10,000 | `ece43a624921549ccb5b951815c1c7e3a5147c72afabd0d5f616a9d6b8b95f91` |
| spectra_before_C.txt | 10,000 | `0c93c63e36f1e6374cd90a912683b15bcc502649a84a71be0d2e7181003f35c3` |
| spectra_after_C.txt | 10,000 | `08f9725c6ce2b95791d6b05860057a5bd047de6babb010a270ab706a2df26a78` |
| concord_after_C.txt | 10,000 | `ca718d5225756915d14758efeffd862c1f4c9c0c9b5393270691ec93ea734f47` |
| warrant_after_D.txt | 10,000 | `eba1e0e02b69be2121829d3c17417bed3ee356755e4eaaf02cc7d06bee77694f` |
| caselog_after_D.txt | 10,000 | `576e025ccf1ce6b8785cdde8b308e838a806238d5dbd299233e931080580b495` |
| spectra_after_D.txt | 10,000 | `75beacf898e2e79646259cdbfb371286e7573560d44ffa951070f9c8b73c2f47` |
| concord_after_D.txt | 10,000 | `da0d3ea513975e1d0c7c4918c9f1f924779005202e4abc1c012aa93806d2714a` |
| negative_controls.txt | 200 | `643c758735a24bb970362aa7e756c45a0a5a381417f4d8df18fb3b759f1e4768` |

### Lean sources

| File | SHA-256 |
|---|---|
| Arithmetic.lean | `8e9f6b12a11fef03b4650d9f86ddbec29c2750a97d4df1781f355f12ac8a69ca` |
| CaseLog.lean | `84540d05576b08013ed37de0558fe0e8d9247f4b85de255457084ce20aa3e0c2` |
| CertData.lean | `f4ef62af7d11248edea05e51f50ad45b2bdb7cf4191c1af0b75515d81b4e4398` |
| Certificate.lean | `bceeb9e8fa0e4012c1c8577404dd17c5224bc8f64786ffc0c8983a08f24886f3` |
| Concord.lean | `b5603a7317c3c458a47b97f5248fa02950e82a3d0929eaa8b80e80c11a1d6edb` |
| Spectra.lean | `3a1c3c65ea63e5efac7256e2e810db38891b725dd7d90f7dfc9737094ebe027c` |
| Tokens.lean | `e2f10ed11230631168db7fc5a9589f8c0b1d578a4cc2d38b7ceb047e73a1d3da` |
| Warrant.lean | `6d955f80428405ba10ed8a97514f9ff2e1dc6780038adc906a20f049720f4329` |

### Runtimes after the fixes

| Runtime | SHA-256 |
|---|---|
| CaseLog | `c7ee3f989d09e7b3485f63a950f976a366dcf1281824907e151b8e4dc7c2bb6a` |
| Warrant | `a6e7413632a24a2e288a1909273e82e970f40ce64c39662ed79f93be599a7401` |
| Spectra | `9e8ac5b58cf84ab4d090919acab09561f131a05764ab439e42c81a8c22bf9d84` |

## Re-checking

In the Lean project folder run `lake build`. It ends with `Build completed successfully` only if every theorem above still holds
for the embedded files. `lake env leanchecker LangStress.Certificate` replays the proofs in the independent kernel checker.
