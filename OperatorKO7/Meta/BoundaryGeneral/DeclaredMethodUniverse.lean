import OperatorKO7.Meta.BoundaryGeneral.CheckedNonOrientationCertificate
import OperatorKO7.Meta.RDRSTerminationMethodUniverse

/-!
# Declared method universe with an explicit outside case

This classifier has proof-bearing inputs for the six direct families in `DeclaredDirectFamily`. Construction and projection escapes carry their data separately. RDRS method families remain in `outsideDeclaredUniverse` unless supplied as proof-bearing declared-family data; the classifier does not claim that the six direct families exhaust termination methods.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.BoundaryGeneral

open OperatorKO7.StepDuplicating
open OperatorKO7.StepDuplicating.StepDuplicatingSchema
open OperatorKO7.RDRSTerminationMethodUniverse

/-- Methods intentionally outside the proof-bearing direct-family syntax. -/
inductive OutsideMethod where
  | atlasFamily (family : RDRSMethodFamily)
  | unlisted (description : String)
  deriving DecidableEq, Repr

/-- A construction escape carries a concrete evaluator and a proof that its
constructed order orients the exact duplicating rule. This record does not
assert that the construction belongs to a direct family. -/
structure ConstructionWitness (S : StepDuplicatingSchema) where
  description : String
  Codomain : Type
  order : Codomain → Codomain → Prop
  eval : S.T → Codomain
  orientsDupStep :
    ∀ b s n,
      order (eval (S.wrap s (S.recur b s n)))
        (eval (S.recur b s (S.succ n)))

/-- A projection escape carries a theorem-backed projection rank. -/
structure ProjectionWitness (S : StepDuplicatingSchema) where
  description : String
  rank : ProjectionRank S

/-- Every `ProjectionWitness` orients the duplicating rule by following only its recursive counter. -/
theorem ProjectionWitness.orients_dup_step
    {S : StepDuplicatingSchema} (data : ProjectionWitness S)
    (b s n : S.T) :
    data.rank.rank (S.wrap s (S.recur b s n)) <
      data.rank.rank (S.recur b s (S.succ n)) :=
  projection_orients_dup_step data.rank b s n

/-- Result of classifying one member of the explicitly declared syntax. -/
inductive ClassificationResult (S : StepDuplicatingSchema) where
  | blocked (cert : CheckedNonOrientationCertificate S)
  | constructionEscape (data : ConstructionWitness S)
  | projectionEscape (data : ProjectionWitness S)
  | outsideDeclaredUniverse (description : OutsideMethod)

/-! ## Family-indexed proof-bearing inputs -/

/-- Input type required by each theorem-backed direct family. The transparent
compositional branch stores its transparency equation, and the matrix branch
stores its dimension together with the projected-affine-pump structure. -/
def DeclaredDirectFamilyInput (S : StepDuplicatingSchema) :
    DeclaredDirectFamily → Type
  | .additive => AdditiveMeasure S
  | .transparentCompositional =>
      { M : CompositionalMeasure S // M.c_succ M.c_base = M.c_base }
  | .affineWithPump => AffineMeasureWithPump S
  | .restrictedQuadraticWithPump => QuadraticCounterMeasureWithPump S
  | .maxPlusWithPump => MaxMeasureWithPump S
  | .matrixFunctionalWithProjectedAffinePump =>
      Σ d : Nat, MatrixFunctionalMeasureWithProjectedAffinePump S d

/-- Every direct-family constructor has a theorem-backed certificate adapter. -/
def checkedCertificateFor {S : StepDuplicatingSchema} :
    (family : DeclaredDirectFamily) →
      DeclaredDirectFamilyInput S family →
        CheckedNonOrientationCertificate S
  | .additive, M => additive_checkedCertificate M
  | .transparentCompositional, M =>
      transparentCompositional_checkedCertificate M.1 M.2
  | .affineWithPump, M => affineWithPump_checkedCertificate M
  | .restrictedQuadraticWithPump, M =>
      restrictedQuadraticWithPump_checkedCertificate M
  | .maxPlusWithPump, M => maxPlusWithPump_checkedCertificate M
  | .matrixFunctionalWithProjectedAffinePump, M =>
      matrixFunctionalWithProjectedAffinePump_checkedCertificate M.2

/-- A member of the declared direct universe: a family tag and the input required by its extractor. -/
structure DeclaredDirectMethod (S : StepDuplicatingSchema) where
  family : DeclaredDirectFamily
  input : DeclaredDirectFamilyInput S family

/-- Extract the checked counterexample carried by a declared direct method. -/
def DeclaredDirectMethod.certificate {S : StepDuplicatingSchema}
    (method : DeclaredDirectMethod S) :
    CheckedNonOrientationCertificate S :=
  checkedCertificateFor method.family method.input

/-- The certificate produced for a method retains the same family tag. -/
theorem DeclaredDirectMethod.certificate_family
    {S : StepDuplicatingSchema} (method : DeclaredDirectMethod S) :
    method.certificate.family = method.family := by
  rcases method with ⟨family, input⟩
  cases family <;> rfl

/-- Inductive syntax for the whole declared classifier surface. -/
inductive DeclaredMethod (S : StepDuplicatingSchema) where
  | direct (method : DeclaredDirectMethod S)
  | constructionEscape (data : ConstructionWitness S)
  | projectionEscape (data : ProjectionWitness S)
  | outsideDeclaredUniverse (description : OutsideMethod)

/-- Classifies each constructor of `DeclaredMethod` by its corresponding result. -/
def classifyDeclaredMethod {S : StepDuplicatingSchema} :
    DeclaredMethod S → ClassificationResult S
  | .direct method => .blocked method.certificate
  | .constructionEscape data => .constructionEscape data
  | .projectionEscape data => .projectionEscape data
  | .outsideDeclaredUniverse description =>
      .outsideDeclaredUniverse description

/-- Every declared direct method is classified as blocked by its extracted
checked certificate. -/
theorem classifyDeclaredMethod_direct
    {S : StepDuplicatingSchema} (method : DeclaredDirectMethod S) :
    classifyDeclaredMethod (.direct method) =
      ClassificationResult.blocked method.certificate :=
  rfl

/-- Soundness of every proof-bearing member of the declared direct universe. -/
theorem declaredDirectMethod_not_orients
    {S : StepDuplicatingSchema} (method : DeclaredDirectMethod S) :
    ¬ OrientsDupStepRelation method.certificate.eval
      method.certificate.order :=
  method.certificate.not_global_orients

/-- Fixed-system form: a declared direct method over the schema of a fixed system cannot globally orient that system. -/
theorem declaredDirectMethod_not_system_global_orients
    {Sys : StepDuplicatingSystem}
    (method : DeclaredDirectMethod Sys.toStepDuplicatingSchema) :
    ¬ GlobalOrients Sys method.certificate.eval
      method.certificate.order :=
  method.certificate.not_system_global_orients

/-- Exhaustiveness theorem for the declared syntax only. The theorem quantifies
over the inductive `DeclaredMethod`; it makes no claim about all termination
methods. -/
theorem declaredMethod_classification_exhaustive
    {S : StepDuplicatingSchema} (method : DeclaredMethod S) :
    (∃ cert, classifyDeclaredMethod method =
      ClassificationResult.blocked cert) ∨
    (∃ data, classifyDeclaredMethod method =
      ClassificationResult.constructionEscape data) ∨
    (∃ data, classifyDeclaredMethod method =
      ClassificationResult.projectionEscape data) ∨
    (∃ description, classifyDeclaredMethod method =
      ClassificationResult.outsideDeclaredUniverse description) := by
  cases method with
  | direct directMethod =>
      exact Or.inl ⟨directMethod.certificate, rfl⟩
  | constructionEscape data =>
      exact Or.inr (Or.inl ⟨data, rfl⟩)
  | projectionEscape data =>
      exact Or.inr (Or.inr (Or.inl ⟨data, rfl⟩))
  | outsideDeclaredUniverse description =>
      exact Or.inr (Or.inr (Or.inr ⟨description, rfl⟩))

/-! ## Outside cases for the RDRS method families -/

/-- An RDRS family is outside the six-family direct syntax unless supplied as proof-bearing declared-family input. -/
theorem atlasFamily_classifies_outside
    (S : StepDuplicatingSchema) (family : RDRSMethodFamily) :
    classifyDeclaredMethod
      (S := S) (.outsideDeclaredUniverse (.atlasFamily family)) =
      ClassificationResult.outsideDeclaredUniverse (.atlasFamily family) :=
  rfl

/-- Tuple interpretations are explicitly outside the six-family direct syntax. -/
theorem tupleInterpretation_classifies_outside
    (S : StepDuplicatingSchema) :
    classifyDeclaredMethod
      (S := S)
      (.outsideDeclaredUniverse
        (.atlasFamily .tupleInterpretationStrictS)) =
      ClassificationResult.outsideDeclaredUniverse
        (.atlasFamily .tupleInterpretationStrictS) :=
  rfl

/-- Semantic labeling is explicitly outside the six-family direct syntax. -/
theorem semanticLabeling_classifies_outside
    (S : StepDuplicatingSchema) :
    classifyDeclaredMethod
      (S := S)
      (.outsideDeclaredUniverse (.atlasFamily .semanticLabeling)) =
      ClassificationResult.outsideDeclaredUniverse
        (.atlasFamily .semanticLabeling) :=
  rfl

end OperatorKO7.Meta.BoundaryGeneral
