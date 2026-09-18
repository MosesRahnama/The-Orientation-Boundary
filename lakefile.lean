import Lake
open Lake DSL

/-!
Lake configuration for the `OperatorKO7` Lean package.

Why this file exists:
- Declares the package/library name (`OperatorKO7`) and its root module directory.
- Declares the `mathlib` dependency.

Notes for readers:
- This is configuration, not part of the KO7 mathematics.
- See `README.md` for the public artifact summary and file map.
- See `OperatorKO7/Kernel.lean` for the kernel (`Trace`, `Step`).
- See `OperatorKO7/Meta/` for the certified safe fragment (`SafeStep`) and proofs.
-/

package OperatorKO7 where
  moreLeanArgs := #["-Dpp.notation=true", "-Dtrace.profiler.threshold=5"]

@[default_target]
lean_lib OperatorKO7 where
  roots := #[`OperatorKO7]

/-- Runnable artifact verifier cited by the manuscript reproducibility note:
`lake exe verifyTpdbExport` re-checks the generated TPDB text against both the
embedded checked literal and the on-disk `Artifacts/ttt2/KO7_full_step.trs`. -/
lean_exe verifyTpdbExport where
  root := `VerifyTpdbExport

require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ "632465e4b02cb70a5dfa4cfe15468e8a62c2bd85"
