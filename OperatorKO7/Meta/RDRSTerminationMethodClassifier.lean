import OperatorKO7.Meta.RDRSMethodCertificateClassifier
import OperatorKO7.Meta.RDRSTerminationMethodAtlas

/-!
# RDRS Termination-Method Classifier (T9 shim)

Roadmap row: `Expansion/RDRS_Termination_Methods_Roadmap.md` milestone T9,
"Supervisor Classifier And Decidability Surface" -- the decidability table
from the atlas, the syntactic classifier over method rows, the separation
between row classification and true method-search decidability, and the
engine-facing status vocabulary.

This module exists as a stable import path for the historical T9 file name.
The decidability surface for the atlas (decidable equality, status enum,
row identity) landed inside `OperatorKO7.RDRSTerminationMethodAtlas`. The
priority-classifier surface over the normalized-certificate syntax landed
inside `OperatorKO7.RDRSMethodCertificateClassifier`. Both modules are
imported here so downstream code that wrote
`import OperatorKO7.Meta.RDRSTerminationMethodClassifier` resolves.

Supersession map:

  decidability table over the atlas rows
                                        -> OperatorKO7.RDRSTerminationMethodAtlas
  syntactic classifier (priority order over normalized certificates)
                                        -> OperatorKO7.RDRSMethodCertificateClassifier
  engine-facing status vocabulary
                                        -> OperatorKO7.RDRSTerminationMethodUniverse
                                           (re-exported transitively via the
                                            atlas import)

No `sorry`, `axiom`, `native_decide`, `@[csimp]`, `unsafe`, `partial`, or
`opaque` is introduced.
-/

set_option autoImplicit false

namespace OperatorKO7.RDRSTerminationMethodClassifier

def supersededBy : List String :=
  ["OperatorKO7.RDRSMethodCertificateClassifier",
   "OperatorKO7.RDRSTerminationMethodAtlas"]

theorem rdrs_termination_method_classifier_shim_marker :
    supersededBy.length = 2 ∧ supersededBy.Nodup := by
  refine ⟨rfl, ?_⟩
  simp [supersededBy, List.Nodup]

end OperatorKO7.RDRSTerminationMethodClassifier
