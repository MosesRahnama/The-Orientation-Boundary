# The Orientation Boundary Public Disclosure Statement

**Date:** 2026-05-05  
**Status:** Public-facing disclosure statement for the current public package.

This repository is the public companion artifact for two manuscripts:

- *The Orientation Boundary for Step-Duplicating Recursors: Mechanized Impossibility, Escape, and Certification.*
- *Operational Inexpressibility at the Primitive-Recursion Orientation Boundary.*

It provides a source-available Lean 4 artifact, selected external validation artifacts, and reproducibility metadata for public inspection of the formal claims made in those manuscripts.

## Disclosure Boundary

```
manuscript claims -> public companion artifact -> reviewer access when needed
```

The public repository discloses the Lean files, build metadata, and external artifacts needed for a reader to inspect the public theorem surface associated with the manuscripts.

Some additional development files may be withheld from the public repository. Qualified academic or editorial reviewers may request access to additional supporting material under a non-disclosure agreement when that material is needed for review of a manuscript claim.

The current public package is source-closed for the API roots imported by `OperatorKO7.lean`.

## Publicly Included Material

The public package includes:

- Lean 4 source files selected for public disclosure.
- Public API entry points for the exposed theorem surfaces.
- Lake and Lean toolchain metadata needed to identify the intended build environment.
- External TTT2 and CeTA validation artifacts for the KO7 rewrite-system trail.
- Reproducibility notes, citation metadata, license terms, and repository documentation.

## Reviewer Access

Additional non-public material may be made available to qualified reviewers under NDA when needed to evaluate a manuscript claim, reproduce a stated theorem dependency, or inspect a supporting proof layer not included in the public repository.

Requests should be directed to the contact address listed in the repository README and citation metadata.

## Release Checks

Before publication, the repository should satisfy the following checks:

```
[public file set]
      |
      v
[source-closure audit]
      |
      v
[license and citation check]
      |
      v
[public release]
```

| Check | Public-facing requirement |
|---|---|
| Source scope | Public files match the final disclosure decision. |
| Build claims | README build instructions match what the public package can actually replay. |
| Citation | `CITATION.cff` names the current manuscripts and current license accurately. |
| License | Public documentation agrees with the repository license. |
| Artifacts | External validation files are present only when they are intended for public release. |
| Local caches | Build caches, generated scratch files, and machine-local state are absent. |

## Non-Public Material

Material not included in the public repository is not described here by file name, internal role, or implementation detail. The public statement records only the access policy: some supporting material may be available to qualified reviewers under NDA, and anything not included in the public package remains outside the public disclosure.

## Current Position

The public repository is a source-available companion artifact for the two named manuscripts. Its build and replay statements are limited to the files disclosed in this public package.
