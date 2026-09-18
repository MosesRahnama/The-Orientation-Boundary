# Artifact Reproducibility

This note is the public reproducibility summary for The Orientation Boundary
companion artifact.

## Exact Pins

- Lean toolchain: `leanprover/lean4:v4.22.0-rc4`
  Source: `lean-toolchain`
- Pinned `mathlib4` commit: `632465e4b02cb70a5dfa4cfe15468e8a62c2bd85`
  Sources: `lakefile.lean`, `lake-manifest.json`
- Full dependency lockfile:
  `lake-manifest.json`

The development uses Mathlib automation, so replay against another toolchain or
`mathlib` revision can change proof-checking behavior.

## Minimal Replay

From the repository root:

```bash
lake exe cache get
lake build
lake exe verifyTpdbExport
```

What this covers:

- `lake build` kernel-checks the public Lean library rooted at `OperatorKO7.lean`,
  which imports every module of the release.
- `lake exe verifyTpdbExport` re-checks the generated TPDB exports against
  `Artifacts/ttt2/KO7_full_step.trs` and `Artifacts/ttt2/free_recursor.trs`.

The verification receipt for the current release is in the repository `README.md`.

## External Validation Trail

The archived external tool trail lives in `Artifacts/ttt2/` and includes:

- `KO7_full_step.trs` and `free_recursor.trs`
- TTT2 text outputs
- CPF certificates
- CeTA certification logs
- `Artifacts/ttt2/README.md`

This trail is archived for public inspection. It is not claimed as a Lean theorem
layer; it is an external validation layer attached to the main formal artifact.

## Micro-Benchmarks

Replay-cost notes for the active artifact state are recorded in:

- `Artifacts/MICRO_BENCHMARKS.md`

That file reports local Lean replay timings together with the archived TTT2 run times
already stored in `Artifacts/ttt2/`.
