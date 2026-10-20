# The Orientation Boundary

Research papers by Moses Rahnama, with Lean 4 proofs and benchmark sessions, data and code.

## Papers

1. **The Orientation Boundary for Step-Duplicating Recursors: A Machine-Checked Structural Theory of Termination Proofs.**

   [Paper](https://arxiv.org/abs/2512.00081) · [Claims and Lean proofs](1.ORIENTATION_BOUNDARY_CLAIM_INDEX.md) · [DOI: 10.48550/arXiv.2512.00081](https://doi.org/10.48550/arXiv.2512.00081)

2. **Observer Determinacy of Termination Certificates: Sufficient Statistics, Blackwell Comparison, and Simple Projections for Step-Duplicating Recursion.**

   [Paper](https://arxiv.org/abs/2604.22844) · [Claims and Lean proofs](2.OPERATIONAL_INEXPRESSIBILITY_CLAIM_INDEX.md) · [DOI: 10.48550/arXiv.2604.22844](https://doi.org/10.48550/arXiv.2604.22844)

3. **Unique Normal Forms: Proof-Graph Counterexamples, Infinite-Carrier Certificates, and Confluence Repair.**

   [Paper](https://papers.ssrn.com/sol3/papers.cfm?abstract_id=7037939) · [Claims and Lean proofs](3.UNIQUE_NORMAL_FORMS_CLAIM_INDEX.md) · [DOI: 10.2139/ssrn.7037939](https://doi.org/10.2139/ssrn.7037939)

4. **Merged States of an Observer: Discrimination, Reading Cost and Zero-Error Recovery.**

   [Paper](https://papers.ssrn.com/sol3/papers.cfm?abstract_id=7640059) · [Claims and Lean proofs](4.MERGED_STATES_OF_AN_OBSERVER_CLAIM_INDEX.md) · [DOI: 10.2139/ssrn.7640059](https://doi.org/10.2139/ssrn.7640059)

5. **The Primitive Recursor Test: Construction-Recognition Gap and Representation-Shift Failure in Formal Reasoning.**

   [Paper: SSRN 7647678](https://papers.ssrn.com/sol3/papers.cfm?abstract_id=7647678) · [Sessions, data and code](https://github.com/MosesRahnama/The-Primitive-Recursor-Test)

The four claim indexes give the theory papers' result numbers, Lean declarations, source files, and conditions.

## Build

The project uses [Lean 4.22.0-rc4](lean-toolchain) and the dependencies in [lake-manifest.json](lake-manifest.json). The following commands run from the repository root:

```sh
lake exe cache get
lake build
```

The root library imports the public Lean modules. The recorded build on 20 October 2026 completed 8,867 jobs across 1,811 modules, with zero errors or uses of `sorry`.

The TPDB export check uses:

```sh
lake exe verifyTpdbExport
```

[Reproducibility](Artifacts/REPRODUCIBILITY.md) gives the build details and external validation records.

## Citation and license

[CITATION.cff](CITATION.cff) contains citation metadata. The [LICENSE](LICENSE) sets the terms for individual research, academic, and commercial use.

**Contact:** Moses Rahnama, Mina Analytics · [info@minaanalytics.com](mailto:info@minaanalytics.com)
