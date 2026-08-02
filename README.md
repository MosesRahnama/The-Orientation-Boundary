# OperatorKO7 Public Manuscript Companion

This repository is the **public companion artifact** for the following manuscripts:

- Rahnama, M. *The Orientation Boundary for Step-Duplicating Recursors: Mechanized Impossibility, Escape, and Certification.*
- Rahnama, M. *Operational Inexpressibility at the Primitive-Recursion Orientation Boundary.*
- Rahnama, M. *The Confluence-Preservation Boundary for Diagonal Identity Queries: Non-Left-Linearity, Signature Inexpressibility, and External Guarding.*

It contains the public Lean 4 source package, selected external proof artifacts, and reproducibility metadata for inspection of the formal claims made in those manuscripts.

---

## Disclosure Scope

The current release contains 738 Lean files under `OperatorKO7/`. The 2026-08-02 Tier-17B closure mirrors all 50 modified or new private Lean files exactly, including the generated theorem-naming snapshot, and kernel-checks the three API roots plus the complete reviewer-gate stack. The exact paths, SHA-256 values, and validation status are recorded in `TIER17B-PUBLIC-MIRROR-RECEIPT-2026-08-02.{md,csv}`; the 2026-08-01 receipt remains the historical static-only seed record.

No NDA, reviewer qualification, or separate access grant applies to retained public-release copies. Product-facing Supervisory Engine modules and other listed private material outside the three manuscript stacks are excluded by scope and covered by the NDA inventory at the end of `Lean_Module_Disclosure_Details.md`.

The proof-foundation audit now leaves 50 historical NDA-inventory paths excluded and provides public overlap copies for the other 13. No module in the current public root and reviewer-gate static closure imports an excluded path.

For the current disclosure policy and the full module-to-manuscript map, see [Lean_Module_Disclosure_Details.md](./Lean_Module_Disclosure_Details.md).

---

## What Is Included

```
OperatorKO7.lean                   public library root
OperatorKO7/
  Kernel.lean                     KO7 kernel
  CrossPaperAPI.lean              cross-manuscript bridge surface
  OrientationBoundaryAPI.lean     Paper A reviewer surface
  InformationalIncompletenessAPI.lean  information-theoretic support surface
  PrimitiveSchemaAPI.lean         primitive-schema surface
  SchemaAPI.lean                  schema-barrier surface
  SchemaExtendedAPI.lean          extended-schema surface
  Meta/                           public theorem modules
  Test/                           reachability and axiom-audit gates

Artifacts/
  ttt2/                           external proof artifacts
  REPRODUCIBILITY.md              reproducibility notes
  MICRO_BENCHMARKS.md             timing micro-benchmarks

CITATION.cff                       citation metadata
LICENSE                            source-available license
Lean_Module_Disclosure_Details.md  module-to-manuscript disclosure map
README.md                          this file
lakefile.lean                      Lake build manifest
lake-manifest.json                 Mathlib commit pin
lean-toolchain                     Lean version pin
```

---

## What Is Not Included

The separate product-facing `SupervisoryEngine\` module tree and all Lean modules unrelated to the three named manuscripts are intentionally excluded. `OperatorKO7\Meta\GenericSupervisoryEngine.lean` remains because it is imported by the manuscript-facing `CrossPaperAPI` proof surface.

---

## Building

This repository targets the Lean 4 toolchain pinned in `lean-toolchain`:

```
leanprover/lean4:v4.22.0-rc4
```

The Mathlib commit pinned in `lake-manifest.json` is:

```
632465e4b02cb70a5dfa4cfe15468e8a62c2bd85
```

From the repository root, fetch dependencies and check the public Lean package with:

```bash
lake exe cache get
lake build OperatorKO7
```

The public package is source-closed for the seven API roots imported by `OperatorKO7.lean`. The Tier-17B reviewer surface has been targeted-kernel-verified on Lean 4.22.0-rc4: `Tier17BClaimReach` passes 190 checks, `Tier17BAxiomAudit` passes 149 declaration audits within `{propext, Classical.choice, Quot.sound}`, and all preservation gates exit 0. No bare whole-package build was used.

---

## License

This artifact is governed by a strict source-available license with three tiers:

| Tier | Who | Cost |
|---|---|---|
| **Academic Research** | individual scholar (student, postdoc, faculty, independent researcher) using the artifact for personal study, proof verification, reproduction of paper results, or citation in their own publications | **free** |
| **Departmental Academic Use** | any use by, on behalf of, or with resources from an academic department, lab, research group, research center, or institute (course material, funded projects, supervised student work, institutional infrastructure, joint or collaborative research) | **paid license required** |
| **Commercial Use** | any use connected to a commercial product, service, for-profit business operation, government-contractor work, paid consulting, or training / evaluating / benchmarking a commercial machine-learning system | **paid license required** |

See [LICENSE](./LICENSE) for the full terms, including the explicit definitions of each tier, the attribution requirement, the restrictions that apply across all tiers, and the legal remedies reserved for unauthorized commercial use.

For paid licensing or any licensing inquiry, contact:

**info@minaanalytics.com**

---

## Access

No NDA is required for the retained copies in this three-manuscript public release. The separate excluded/private NDA inventory is recorded at the end of `Lean_Module_Disclosure_Details.md`. Licensing questions can be directed to:

**info@minaanalytics.com**

---

## Citation

If you use this artifact in a publication or other public disclosure, please cite the originating papers and this repository:

```bibtex
@misc{rahnama_orientation_boundary,
  author       = {Rahnama, Moses},
  title        = {The Orientation Boundary for Step-Duplicating Recursors:
                  Mechanized Impossibility, Escape, and Certification},
  year         = {2026},
  howpublished = {preprint},
  note         = {\url{https://github.com/MosesRahnama/The-Orientation-Boundary}}
}

@misc{rahnama_operational_inexpressibility,
  author       = {Rahnama, Moses},
  title        = {Operational Inexpressibility at the Primitive-Recursion
                  Orientation Boundary},
  year         = {2026},
  howpublished = {preprint},
  note         = {\url{https://github.com/MosesRahnama/The-Orientation-Boundary}}
}

@misc{rahnama_distinction_boundary,
  author       = {Rahnama, Moses},
  title        = {The Confluence-Preservation Boundary for Diagonal Identity
                  Queries: Non-Left-Linearity, Signature Inexpressibility,
                  and External Guarding},
  year         = {2026},
  howpublished = {preprint},
  note         = {\url{https://github.com/MosesRahnama/The-Orientation-Boundary}}
}
```

See `CITATION.cff` for machine-readable citation metadata.

---

## Contact

Moses Rahnama, Mina Analytics

**info@minaanalytics.com**
