# The Orientation Boundary Research Program Public Repository 

Lean 4 companion artifact for three manuscripts on the orientation boundary for step-duplicating recursors. It contains the Lean source package, external proof artifacts, and reproducibility metadata for inspecting the formal claims those papers make.

## Publications

- Rahnama, M. *The Orientation Boundary for Step-Duplicating Recursors: Direct Measures, Polynomial Decision, and Dependency-Pair Escape.* [arXiv:2512.00081](https://arxiv.org/abs/2512.00081)
- Rahnama, M. *Observer Determinacy of Termination Certificates: Sufficient Statistics, Blackwell Comparison, and Simple Projections for Step-Duplicating Recursion.* [arXiv:2604.22844](https://arxiv.org/abs/2604.22844)
- Rahnama, M. *Unique Normal Forms: Proof-Graph Counterexamples, Infinite-Carrier Certificates, and Confluence Repair.* [SSRN 7037939](https://papers.ssrn.com/sol3/papers.cfm?abstract_id=7037939)

---

## Contents

The repository holds 1,621 Lean modules under `OperatorKO7/`, the library root `OperatorKO7.lean`, and `VerifyTpdbExport.lean`. Each module is named in one of the three manuscripts or required to compile a module that is. The Orientation Boundary correspondence is [1.ORIENTATION_BOUNDARY_CLAIM_INDEX.md](./1.ORIENTATION_BOUNDARY_CLAIM_INDEX.md), the Observer Determinacy correspondence is [2.OPERATIONAL_INEXPRESSIBILITY_CLAIM_INDEX.md](./2.OPERATIONAL_INEXPRESSIBILITY_CLAIM_INDEX.md) and the Unique Normal Forms correspondence is [3.UNIQUE_NORMAL_FORMS_CLAIM_INDEX.md](./3.UNIQUE_NORMAL_FORMS_CLAIM_INDEX.md).

```
OperatorKO7.lean                   library root; imports every module
OperatorKO7/
  Kernel.lean                      KO7 kernel
  PrimitiveSchemaAPI.lean          conservative primitive/schema-parametric core
  SchemaAPI.lean                   schema-barrier surface
  SchemaExtendedAPI.lean           extended barrier, tooling, and SCC layer
  OrientationBoundaryAPI.lean      order-type and boundary surface
  ResidualMethodAPI.lean           residual frontier surface
  Meta/                            theorem modules
  Test/                            reachability and axiom-audit gates

Artifacts/
  ttt2/                            external proof artifacts (TTT2, CeTA), including free_recursor.trs
  REPRODUCIBILITY.md               reproducibility notes
  MICRO_BENCHMARKS.md              timing micro-benchmarks

CITATION.cff                       citation metadata
LICENSE                            source-available license
1.ORIENTATION_BOUNDARY_CLAIM_INDEX.md  full claim-to-code index for the Orientation Boundary paper
2.OPERATIONAL_INEXPRESSIBILITY_CLAIM_INDEX.md  full claim-to-code index for the Observer Determinacy paper
3.UNIQUE_NORMAL_FORMS_CLAIM_INDEX.md  full claim-to-code index for the Unique Normal Forms paper
lakefile.lean                      Lake build configuration
lake-manifest.json                 Mathlib commit pin
lean-toolchain                     Lean version pin
```

The Unique Normal Forms manuscript keeps a headline claim-to-code table in its own appendix and
publishes the exhaustive surface here, in
[3.UNIQUE_NORMAL_FORMS_CLAIM_INDEX.md](./3.UNIQUE_NORMAL_FORMS_CLAIM_INDEX.md): 454 claim anchors and
298 modules, including 84 `Meta/UniqueNormalization` modules (constructor compatibility lives in
`ConstructorCompatibility.lean`; the 14 history/occurrence/stable-boundary modules stay out of this
tree). One hundred and twenty-two `Test/*Reach` gates import modules of that index, and
`Test/UNFClaimIndexAnchorCheck.lean` pins the paper-facing declarations. Each row carries the paper's theorem number and its stable label, so a claim traces in
either direction.

---

## Building

The pinned toolchain is `leanprover/lean4:v4.22.0-rc4` and the pinned Mathlib commit is `632465e4b02cb70a5dfa4cfe15468e8a62c2bd85`.

From the repository root:

```bash
lake exe cache get
lake build
```

`OperatorKO7.lean` imports every module, so `lake build` kernel-checks the entire package. Individual modules can be checked on their own:

```bash
lake build OperatorKO7.Meta.SafeStep
```

The reproducibility executable cited in the manuscripts re-checks the generated TPDB export against both the embedded literal and `Artifacts/ttt2/KO7_full_step.trs`, and the free recursor export against `Artifacts/ttt2/free_recursor.trs`:

```bash
lake exe verifyTpdbExport
```

## Verification status

Full-package verification on 2026-09-17: `lake build` from the repository root completed 8,677 jobs over 1,621 modules and exited 0, with zero errors and zero uses of `sorry`. Every reach gate named in the three claim indexes built in that run. `lake build OperatorKO7.Test.UNFClaimIndexAnchorCheck` prints one axiom report for each of its 469 pinned declarations, 110 of them axiom-free and the rest within {propext, Classical.choice, Quot.sound}, with no use of `sorryAx`. `lake exe verifyTpdbExport` matched `Artifacts/ttt2/KO7_full_step.trs` and `Artifacts/ttt2/free_recursor.trs`.

Orientation Boundary additions of 2026-09-17: `Meta/YamadaTupleAffineBarrier_Schema.lean` (named by the paper and the index) restored to the tree, and `Meta/Methods/OrientationClosure/OrientationBoundaryObject.lean` with `Test/OrientationBoundaryObjectReach.lean` added; both are imported from the root, and the named builds `lake build OperatorKO7.Meta.Methods.OrientationClosure.OrientationBoundaryObject` and `lake build OperatorKO7.Test.OrientationBoundaryObjectReach` exit 0 with every axiom set within {propext, Classical.choice, Quot.sound}.

The modules under `OperatorKO7/Test/` are reachability and axiom-audit gates: they pin declaration
types and print axiom inventories, and carry no mathematical content of their own. A gate passing is
evidence that a declaration exists with the stated type; that a theorem is the intended one is
separate evidence, which the manuscripts supply.

---

## License

This artifact is governed by a source-available license with three tiers:

| Tier | Who | Cost |
|---|---|---|
| **Individual Research** | any individual, with or without an academic affiliation: a student, postdoc, faculty member, independent researcher, or hobbyist, using the artifact for personal study, proof verification, reproduction of paper results, or citation in their own publications | **free** |
| **Departmental Academic Use** | any use by, on behalf of, or with resources from an academic department, lab, research group, research center, or institute (course material, funded projects, supervised student work, institutional infrastructure, joint or collaborative research) | **paid license required** |
| **Commercial Use** | any use connected to a commercial product, service, for-profit business operation, government-contractor work, paid consulting, or training / evaluating / benchmarking a commercial machine-learning system | **paid license required** |

See [LICENSE](./LICENSE) for the full terms, including the definitions of each tier, the attribution requirement, the restrictions that apply across all tiers, and the legal remedies reserved for unauthorized commercial use.

For licensing inquiries, contact **info@minaanalytics.com**.

---

## Citation

If you use this artifact in a publication or other public disclosure, please cite the originating papers and this repository:

```bibtex
@misc{rahnama_orientation_boundary,
  author       = {Rahnama, Moses},
  title        = {The Orientation Boundary for Step-Duplicating Recursors:
                  Direct Measures, Polynomial Decision, and Dependency-Pair Escape},
  year         = {2026},
  eprint       = {2512.00081},
  archivePrefix= {arXiv},
  note         = {\url{https://arxiv.org/abs/2512.00081}}
}

@misc{rahnama_operational_inexpressibility,
  author       = {Rahnama, Moses},
  title        = {Observer Determinacy of Termination Certificates:
                  Sufficient Statistics, Blackwell Comparison, and Simple Projections
                  for Step-Duplicating Recursion},
  year         = {2026},
  eprint       = {2604.22844},
  archivePrefix= {arXiv},
  note         = {\url{https://arxiv.org/abs/2604.22844}}
}

@misc{rahnama_unique_normal_forms,
  author       = {Rahnama, Moses},
  title        = {Unique Normal Forms: Proof-Graph Counterexamples,
                  Infinite-Carrier Certificates, and Confluence Repair},
  year         = {2026},
  howpublished = {SSRN preprint 7037939},
  note         = {\url{https://papers.ssrn.com/sol3/papers.cfm?abstract_id=7037939}}
}
```

See `CITATION.cff` for machine-readable citation metadata.

---

## Contact

Moses Rahnama, Mina Analytics

**info@minaanalytics.com**
