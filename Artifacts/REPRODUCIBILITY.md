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

These values should be treated as part of the artifact narrative. The project uses
Mathlib automation heavily enough that replay against a different toolchain or
`mathlib` revision may change proof-checking behavior.

## Minimal Replay

From the repository root:

```bash
lake exe cache get
lake build OperatorKO7
```

What this covers:

- `lake build OperatorKO7`
  checks the public Lean library rooted at `OperatorKO7.lean`.

## External Validation Trail

The archived external tool trail lives in `Artifacts/ttt2/` and includes:

- `KO7_full_step.trs`
- TTT2 text outputs
- CPF certificates
- CeTA certification log
- `Artifacts/ttt2/README.md`

This trail is archived for public inspection. It is not claimed as a Lean theorem
layer; it is an external validation layer attached to the main formal artifact.

## Micro-Benchmarks

Replay-cost notes for the active artifact state are recorded in:

- `Artifacts/MICRO_BENCHMARKS.md`

That file reports local Lean replay timings together with the archived TTT2 run times
already stored in `Artifacts/ttt2/`.
