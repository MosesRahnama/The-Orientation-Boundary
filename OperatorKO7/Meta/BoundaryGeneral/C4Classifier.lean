/-!
# Priority classifier for five boundary-layer labels

`Evidence` stores six Boolean flags, and `classify` selects a `BoundaryLayer` by a fixed priority
order. The final branch returns `interfaceInexpr`, so an all-false evidence record receives that
label by default. `recursorEvidence` and `externalMetaEvidence` are explicit fixtures; their
classification theorems are closed computations over those records. The formal scope is the
priority classifier over supplied flags; semantic adapters belong in separate modules.
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

/-- Select a layer by priority, with `interfaceInexpr` as the all-false default. -/
def classify (e : Evidence) : BoundaryLayer :=
  if e.objectUndecidable then .objUndec
  else if e.dimensionChangesVerdict && !e.languageNamesDimension then .interfaceInexpr
  else if e.licenseRequired then .licensedInert
  else if e.resourceStopping then .resourceHalt
  else if e.externalMetaUsed then .externalMeta
  else .interfaceInexpr

/-- Explicit fixture assigning the dimension-change and language-omission flags. -/
def recursorEvidence : Evidence where
  objectUndecidable := false
  dimensionChangesVerdict := true
  languageNamesDimension := false
  licenseRequired := false
  resourceStopping := false
  externalMetaUsed := false

/-- Computation of `classify` on `recursorEvidence`. -/
theorem recursor_is_interfaceInexpr :
    classify recursorEvidence = BoundaryLayer.interfaceInexpr := by decide

theorem recursor_not_objUndec :
    classify recursorEvidence ≠ BoundaryLayer.objUndec := by decide

/-- Explicit fixture assigning only the external-metatheorem flag. -/
def externalMetaEvidence : Evidence where
  objectUndecidable := false
  dimensionChangesVerdict := false
  languageNamesDimension := true
  licenseRequired := false
  resourceStopping := false
  externalMetaUsed := true

/-- Computation of `classify` on `externalMetaEvidence`. -/
theorem externalMeta_classified :
    classify externalMetaEvidence = BoundaryLayer.externalMeta := by decide

#print axioms recursor_is_interfaceInexpr
#print axioms externalMeta_classified

end OperatorKO7.Meta.BoundaryGeneral.C4Classifier
