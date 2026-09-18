# TTT2 Artifacts (KO7 Full Step)

This folder stores the archived external validation trail for the KO7 full-step TRS
and the free two-rule recursor.

## Input
- `KO7_full_step.trs`: input TRS (8 rules, 7 constructors)
- `free_recursor.trs`: free two-rule recursor (2 rules), exported by
  `OperatorKO7/Meta/TPDB_Export.lean` from `freeRecursorTRS`

## TTT2 Proof Outputs

### Certified (YES → CeTA CERTIFIED)
- `KO7_FAST.cpf`: FAST strategy (DP + SCC + subterm criterion)
- `KO7_LPO.cpf`: LPO strategy (lexicographic path order, rule removal)
- `KO7_COMP.cpf`: COMP strategy (DP + TDG + SCC + subterm + matrix + LPO)

### Rejected (MAYBE → CeTA REJECTED)
- `KO7_KBO.cpf`: KBO strategy (Knuth-Bendix order)
- `KO7_POLY.cpf`: POLY strategy (polynomial interpretation, `-ib 5 -ob 6`)
- `KO7_MAT2.cpf`: MAT(2) strategy (matrix interpretation, dim 2)
- `KO7_MAT3.cpf`: MAT(3) strategy (matrix interpretation, dim 3)

### Not Certifiable
- FBI strategy: returned MAYBE (0.17s) but produced no CPF certificate. No `.cpf` file is included for this strategy.

## Prior Text Outputs
- `KO7_full_step_TTT2_results_FAST.txt`: FAST strategy human-readable output
- `KO7_full_step_TTT2_results_POLY.txt`: POLY strategy human-readable output

Note: Human-readable text outputs are preserved only for FAST and POLY. Timings for other strategies are from TTT2 runs and can be reproduced using the generation commands below. CPF files (which encode the complete proof certificates) are included for all strategies that produced them (FBI returned MAYBE with no CPF output).

## Certification Log
- `KO7_CeTA_certification.txt`: full CeTA 2.36 verification results for all strategies

## Generation

From a local TTT2 1.20 checkout, point `<TRS>` to `Artifacts/ttt2/KO7_full_step.trs`
or to an equivalent local copy of that file:

```bash
./ttt2 -cpf <TRS>                                  # FAST (default)
./ttt2 -cpf -s lpo <TRS>                           # LPO
./ttt2 -cpf -s 'dp;...' <TRS>                      # COMP (full strategy string in certification log)
./ttt2 -cpf -s kbo <TRS>                           # KBO
./ttt2 -cpf -s 'poly -direct -ib 5 -ob 6' <TRS>   # POLY
./ttt2 -cpf -s 'matrix -dim 2 -ib 2 -ob 2' <TRS>  # MAT(2)
./ttt2 -cpf -s 'matrix -dim 3 -ib 2 -ob 2' <TRS>  # MAT(3)
```

Post-processing: raw TTT2 output has a `YES`/`MAYBE` line before XML; the CPF files
archived here have that line stripped.

## CeTA Certification (2026-03-04)

CeTA 2.36 via web interface at http://138.232.18.220/tool/ceta.

| Strategy | TTT2 | CeTA |
|----------|------|------|
| FAST | YES | **CERTIFIED** |
| LPO | YES | **CERTIFIED** |
| COMP | YES | **CERTIFIED** |
| KBO | MAYBE | REJECTED |
| POLY | MAYBE | REJECTED |
| MAT(2) | MAYBE | REJECTED |
| MAT(3) | MAYBE | REJECTED |
| FBI | MAYBE | N/A |

The configured modular/structural runs (FAST, LPO, COMP) produced certified proofs. The
configured global/compositional runs (KBO, POLY, MAT(2), MAT(3), FBI) returned MAYBE and did
not produce a certified termination proof. MAYBE records non-success of that bounded search
under the stated strategies and parameters, not a proof that no such method can succeed.

## Free Recursor Certification (2026-09-16)

Hosted TTT2/CeTA interface at `http://138.232.18.220/tool/ttt2` with CeTA enabled.

| Strategy | TTT2 | CeTA |
|----------|------|------|
| FAST | YES (0.023s) | **CERTIFIED** |

- `free_recursor_FAST.cpf`: FAST certificate (DP + subterm criterion, argument
  filter collapsing `recur#` to its third argument, then empty DP problem)
- `free_recursor_TTT2_results_FAST.txt`: human-readable output
- `free_recursor_CeTA_certification.txt`: certification log

The certificate's projection to the recursion counter matches the Lean-side
termination proof `freeRecursorTRS_terminating`
(`OperatorKO7/Meta/Methods/OrientationClosure/DependencyPairSoundness.lean`).

## Lean-side relation to this folder

The repository also includes `Meta/TTT2_CertificateReplay.lean`, but that file is not
a CPF parser. It is a narrow Lean-side replay of the mathematical core of the FAST
certificate: the single recursive SCC, the projected argument, and the resulting
well-founded DP-pair proof.
