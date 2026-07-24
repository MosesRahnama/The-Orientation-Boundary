# The Orientation Boundary

This repository is the **public companion artifact** for the following manuscripts:

- Rahnama, M. *The Orientation Boundary for Step-Duplicating Recursors: Mechanized Impossibility, Escape, and Certification.*
- Rahnama, M. *Operational Inexpressibility at the Primitive-Recursion Orientation Boundary.*
- Rahnama, M. *The Confluence-Preservation Boundary for Diagonal Identity Queries: Non-Left-Linearity, Signature Inexpressibility, and External Guarding.*

It contains the public Lean 4 source package for the exposed theorem surface, manuscript source snapshots, selected external proof artifacts, and reproducibility metadata for inspection of the formal claims made in those manuscripts.

---

## Disclosure Scope

For the Orientation Boundary paper, the release target is its complete 380-file Lean closure: 270 direct manuscript references plus 110 transitive imports. The current staging state is 201 source-identical public files, 80 public files requiring synchronization, and 99 files pending transfer.

No Orientation Boundary closure file is subject to NDA. NDA access may still apply to other manuscripts or product-facing material outside that paper closure.

For the current disclosure policy and the full module-to-manuscript map, see [Lean_Module_Disclosure_Details.md](./Lean_Module_Disclosure_Details.md).

---

## What Is Included

```
OperatorKO7.lean                   public library root
OperatorKO7/
  Kernel.lean                     KO7 kernel
  CrossPaperAPI.lean              cross-manuscript bridge surface
  PrimitiveSchemaAPI.lean         primitive-schema surface
  SchemaAPI.lean                  schema-barrier surface
  SchemaExtendedAPI.lean          extended-schema surface
  Meta/                           public theorem modules
  Test/                           reachability and axiom-audit gates

Manuscripts/
  Orientation_Boundary/           Paper A TeX source and bibliography
  Operational_Inexpressibility/   Paper B TeX source and bibliography
  Distinction_Boundary/           Paper C TeX source

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

The Orientation Boundary files marked `pending transfer` or `synchronization required` in the disclosure ledger are not yet release-ready, but all are designated public and require no NDA. Other manuscripts may retain separate access policies.

For the Orientation Boundary paper, the complete direct-plus-import inventory is the 380-row closure table in `Lean_Module_Disclosure_Details.md`; the manuscript module map is a theorem-facing summary rather than an exhaustive import manifest.

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

The public package is source-closed for the API roots imported by `OperatorKO7.lean`.

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

## Reviewer NDA Access

No NDA is required for any file in the Orientation Boundary Lean closure. For material outside that closure, academic and editorial reviewers may request access under the applicable policy. Contact:

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
