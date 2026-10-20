# The Orientation Boundary

Research papers by Moses Rahnama, with Lean 4 proofs and benchmark sessions, data and code.

## Papers

1. **The Orientation Boundary for Step-Duplicating Recursors: A Machine-Checked Structural Theory of Termination Proofs.**

   [Paper](https://arxiv.org/abs/2512.00081) · [Claims and Lean proofs](1.ORIENTATION_BOUNDARY_CLAIM_INDEX.md) · [DOI: 10.48550/arXiv.2512.00081](https://doi.org/10.48550/arXiv.2512.00081)

2. **Observer Determinacy of Termination Certificates: Sufficient Statistics, Blackwell Comparison, and Simple Projections for Step-Duplicating Recursion.**

   [Paper](https://arxiv.org/abs/2604.22844) · [Claims and Lean proofs](2.OPERATIONAL_INEXPRESSIBILITY_CLAIM_INDEX.md) · [DOI: 10.48550/arXiv.2604.22844](https://doi.org/10.48550/arXiv.2604.22844)

3. **Confluence on the Normalizing Core: Normal Forms Without Termination or Global Normalization.**

   [Paper](https://papers.ssrn.com/sol3/papers.cfm?abstract_id=7037939) · [Claims and Lean proofs](3.CONFLUENCE_ON_THE_NORMALIZING_CORE_CLAIM_INDEX.md) · [DOI: 10.2139/ssrn.7037939](https://doi.org/10.2139/ssrn.7037939)

4. **Entangled Merged Pairs: The Observation-Boundary Principle.**

   [Paper](https://papers.ssrn.com/sol3/papers.cfm?abstract_id=7640059) · [Claims and Lean proofs](4.BOUNDARY_OBSERVATION_PRINCIPLE_CLAIM_INDEX.md) · [DOI: 10.2139/ssrn.7640059](https://doi.org/10.2139/ssrn.7640059)

5. **A Counterexample to Lemma 64 of the Kahrs and Smith Proof for RTA-79.**

   [Paper: SSRN 7659838](https://papers.ssrn.com/sol3/papers.cfm?abstract_id=7659838) · [Paper summary and Lean results](5.LEMMA_64_COUNTEREXAMPLE.md) · [Standalone Lean package and proof graph](Lemma64-Counterexample/README.md) · [Claim ledger](Lemma64-Counterexample/CLAIMS.csv) · [Standalone repository](https://github.com/MosesRahnama/RTA-79-Proof-Counterexample)

6. **The Primitive Recursor Test: Construction-Recognition Gap and Representation-Shift Failure in Formal Reasoning.**

   [Paper: SSRN 7647678](https://papers.ssrn.com/sol3/papers.cfm?abstract_id=7647678) · [Sessions, data and code](https://github.com/MosesRahnama/The-Primitive-Recursor-Test)

## Claim-to-code indexes

Each index maps one manuscript's results to the Lean declarations that prove them. A reader starts from a result in the paper, finds the matching entry under Claims, and follows the entry's source link into the Lean file.

| File | Manuscript | Contents |
| --- | --- | --- |
| [1.ORIENTATION_BOUNDARY_CLAIM_INDEX.md](1.ORIENTATION_BOUNDARY_CLAIM_INDEX.md) | Paper 1 (arXiv 2512.00081) | 165 entries; Claims, Modules, Source files, Additional results |
| [2.OPERATIONAL_INEXPRESSIBILITY_CLAIM_INDEX.md](2.OPERATIONAL_INEXPRESSIBILITY_CLAIM_INDEX.md) | Paper 2 (arXiv 2604.22844) | 230 entries; Claims, Modules, Check files |
| [3.CONFLUENCE_ON_THE_NORMALIZING_CORE_CLAIM_INDEX.md](3.CONFLUENCE_ON_THE_NORMALIZING_CORE_CLAIM_INDEX.md) | Paper 3 (SSRN 7037939) | 108 entries; Claims, Modules |
| [4.BOUNDARY_OBSERVATION_PRINCIPLE_CLAIM_INDEX.md](4.BOUNDARY_OBSERVATION_PRINCIPLE_CLAIM_INDEX.md) | Paper 4 (SSRN 7640059) | 366 entries; Claims, Modules, Check files |
| [5.LEMMA_64_COUNTEREXAMPLE.md](5.LEMMA_64_COUNTEREXAMPLE.md) | Paper 5 (SSRN 7659838) | Prose summary of the result and the formalization |

- An entry in indexes 1, 2, and 4 carries the paper's result number as its heading, the manuscript label, a status, a statement summary, the Lean result, the conditions, a source link, and a folded list of Lean declarations.
- A status of `PROVEN` marks a result with a Lean proof; `DEFINITION` marks a definition. Index 1 also uses `PROVEN / EXTERNAL` for results with external tool evidence, and index 2 uses `NO-LEAN` for a claim with no attached Lean declaration.
- Declaration names under a stated Lean namespace take that namespace as their prefix. The Modules, Source files, and Check files sections resolve the numbered source links, state each module's namespace and role, and list the check files that hold the declaration and axiom checks.
- Papers 1 and 2 name the Concrete Witness System `KO7` in Lean.
- Index 3 keys entries by the manuscript's stable LaTeX labels in place of theorem numbers. Each entry gives the label, a plain-language title, the source file, the full namespace, the declaration names, and the foundation entry imports. The Verification scope section records the declaration and axiom audit behind the index.
- Index 4 headings use the paper's current result numbers; 21 of them also give the result's number in the first SSRN version.
- Paper 5 keeps its claim-to-code map in [CLAIMS.csv](Lemma64-Counterexample/CLAIMS.csv), with one row per claim node and columns for the statement, status, manuscript source, module, and test. The [package README](Lemma64-Counterexample/README.md) documents the single-file package, its main theorems `Lemma64.lemma64_counterexample` and `Lemma64.lemma64_fails`, and the build command.
- Paper 6 has no claim index in this repository. Its sessions, data, and code sit in [The-Primitive-Recursor-Test](https://github.com/MosesRahnama/The-Primitive-Recursor-Test).

## Build

The project uses [Lean 4.22.0-rc4](lean-toolchain) and the dependencies in [lake-manifest.json](lake-manifest.json). The following commands run from the repository root:

```sh
lake exe cache get
lake build
```

The root library imports the public Lean modules. The recorded build on 28 October 2026 completed 8,968 jobs across 1,913 modules, with zero errors or uses of `sorry`.

The TPDB export check uses:

```sh
lake exe verifyTpdbExport
```

[Reproducibility](Artifacts/REPRODUCIBILITY.md) gives the build details and external validation records.

## Citation and license

[CITATION.cff](CITATION.cff) contains citation metadata. The [LICENSE](LICENSE) sets the terms for individual research, academic, and commercial use.

**Contact:** Moses Rahnama, Mina Analytics · [info@minaanalytics.com](mailto:info@minaanalytics.com)
