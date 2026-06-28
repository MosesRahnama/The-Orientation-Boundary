-- Top-level public API roots
import OperatorKO7.Kernel
import OperatorKO7.PrimitiveSchemaAPI
import OperatorKO7.SchemaAPI
import OperatorKO7.SchemaExtendedAPI
import OperatorKO7.CrossPaperAPI

/-!
# OperatorKO7: Public Companion Library

This file is the Lake library root for the public companion artifact. It
imports only the seven top-level public API roots; transitively, it loads
every Lean module shipped on this repository.

The full active Lean stack is described in the manuscript module-map appendices
of *The Orientation Boundary for Step-Duplicating Recursors: Mechanized
Impossibility, Escape, and Certification* and *Operational Inexpressibility at
the Primitive-Recursion Orientation Boundary*. Files cited only in those
appendices and not invoked in the body of either manuscript are covered by the
disclosure policy in `Disclosure_List.md`.
See `README.md` and contact `info@minaanalytics.com`.
-/
