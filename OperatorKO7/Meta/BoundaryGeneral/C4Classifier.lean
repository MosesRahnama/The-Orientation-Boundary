/-!
# Theory VII: C4 layer classifier for undecidability claims

Boundary-general cross-paper packet, Theory VII. Failures at a proof interface must be classified by
layer, not all lumped as "undecidability." The five layers are object-level undecidability, interface
inexpressibility, licensed-inert payload, resource halt, and external-metatheorem use. The
classifier is a total computable function on evidence; the duplicating recursor under a direct
whole-term language classifies as **interface inexpressibility, not object undecidability** (the
verdict depends on the step argument, a dimension the observation language cannot name).

This prevents a benchmark or reviewer from calling every failure "undecidability" when the precise
failure is interface loss, license absence, or resource abstention. `classify` is `decide`-checkable,
so the recursor and external-metatheorem classifications are closed computations.

No `sorry`, `axiom`, or `native_decide`.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.BoundaryGeneral.C4Classifier

/-- The five boundary layers. -/
inductive BoundaryLayer
  | objUndec
  | interfaceInexpr
  | licensedInert
  | resourceHalt
  | externalMeta
  deriving DecidableEq, Repr

/-- Classifier evidence for a claim: the booleans the classification rules read. -/
structure Evidence where
  objectUndecidable : Bool      -- no algorithm in the object theory decides the verdict
  dimensionChangesVerdict : Bool -- a dimension `D` can change the admissible verdict
  languageNamesDimension : Bool  -- the observation language can name `D`
  licenseRequired : Bool         -- payload present but a license is required for verdict export
  resourceStopping : Bool        -- the decisive event is a budget / abstention / stopping rule
  externalMetaUsed : Bool        -- the result uses a metatheorem not internalized

/-- The total computable C4 classifier (Definition 7.3), in priority order. -/
def classify (e : Evidence) : BoundaryLayer :=
  if e.objectUndecidable then .objUndec
  else if e.dimensionChangesVerdict && !e.languageNamesDimension then .interfaceInexpr
  else if e.licenseRequired then .licensedInert
  else if e.resourceStopping then .resourceHalt
  else if e.externalMetaUsed then .externalMeta
  else .interfaceInexpr

/-- The duplicating recursor's evidence: the verdict depends on the step argument (a dimension the
direct whole-term language cannot name), while the object predicate is decidable. -/
def recursorEvidence : Evidence where
  objectUndecidable := false
  dimensionChangesVerdict := true
  languageNamesDimension := false
  licenseRequired := false
  resourceStopping := false
  externalMetaUsed := false

/-- **Theorem 7.4.** Under a direct whole-term observation language the duplicating recursor is
interface inexpressibility, not object undecidability. -/
theorem recursor_is_interfaceInexpr :
    classify recursorEvidence = BoundaryLayer.interfaceInexpr := by decide

theorem recursor_not_objUndec :
    classify recursorEvidence ≠ BoundaryLayer.objUndec := by decide

/-- Evidence that invokes an external metatheorem not internalized in the object language. -/
def externalMetaEvidence : Evidence where
  objectUndecidable := false
  dimensionChangesVerdict := false
  languageNamesDimension := true
  licenseRequired := false
  resourceStopping := false
  externalMetaUsed := true

/-- **Theorem 7.5.** External-metatheorem use (with no internal proof object) classifies as the
external-meta layer, not as object undecidability. -/
theorem externalMeta_classified :
    classify externalMetaEvidence = BoundaryLayer.externalMeta := by decide

#print axioms recursor_is_interfaceInexpr
#print axioms externalMeta_classified

end OperatorKO7.Meta.BoundaryGeneral.C4Classifier
