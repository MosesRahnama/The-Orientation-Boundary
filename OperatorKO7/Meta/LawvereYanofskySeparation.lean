import OperatorKO7.Meta.ConfessionMethod_DP

/-!
# Lawvere-Yanofsky Separation for the DP Confession

This module isolates the semantic ingredients that a genuine
Lawvere--Yanofsky diagonal route would need and compares them with the
concrete dependency-pair confession on the primitive duplicator.

The conclusion is deliberately artifact-honest: we do not formalize a full
historical impossibility theorem, but we do prove that the mechanized DP object
in this repository is a singleton extracted-pair certificate with an external
Arts--Giesl license and no packaged internal code / evaluation /
fixed-point-free schema.
-/

namespace OperatorKO7.LawvereYanofskySeparation

open OperatorKO7
open OperatorKO7.Trace
open OperatorKO7.ConfessionMethodFamily
open OperatorKO7.MetaDependencyPairs

/-- Bare internal coding interface for a Lawvere--Yanofsky style setup. -/
structure LawvereCodeObject where
  Code : Type
  quote : Trace → Code

/-- Self-application / representability interface for a Lawvere--Yanofsky style
setup. -/
structure LawvereEvaluationMap where
  Code : Type
  Value : Type
  represent : Code → Value
  evaluate : Code → Code → Value
  selfApplicationCode : Code → Code
  selfApplicationCorrect : ∀ c, represent (selfApplicationCode c) = evaluate c c

/-- Fixed-point-free endomap required to run the Lawvere--Yanofsky diagonal
contradiction. -/
structure FixedPointFreeEndomap where
  Value : Type
  endomap : Value → Value
  isFixedPointFree : ∀ v, endomap v ≠ v

/-- Bundled semantic Lawvere--Yanofsky schema. -/
structure LawvereYanofskySchema where
  codeObject : LawvereCodeObject
  evaluationMap : LawvereEvaluationMap
  fixedPointFreeEndomap : FixedPointFreeEndomap
  codeTypesAgree : evaluationMap.Code = codeObject.Code
  valueTypesAgree : fixedPointFreeEndomap.Value = evaluationMap.Value

/-- Finite extracted-pair carrier used by a dependency-pair certificate. -/
structure FinitePairGraphCertificate where
  Node : Type
  finiteNodes : Fintype Node
  pairSemantics : Node → DPPairProblemEvidence

attribute [instance] FinitePairGraphCertificate.finiteNodes

/-- Structured summary of what the mechanized DP confession actually supplies.
Optional Lawvere--Yanofsky slots are left explicit so the separation theorem
can state that they are absent on the primitive duplicator object. -/
structure DpConfessionStructure where
  routeEvidence : DPRouteEvidence
  pairCertificate : FinitePairGraphCertificate
  externalLicense : SoundnessLicense
  internalCodeObject? : Option LawvereCodeObject := none
  evaluationMap? : Option LawvereEvaluationMap := none
  fixedPointFreeEndomap? : Option FixedPointFreeEndomap := none

/-- The DP confession has an internal code object exactly when such a datum is
present in its structured summary. -/
def DpConfessionStructure.HasInternalCodeObject
    (D : DpConfessionStructure) : Prop :=
  ∃ C, D.internalCodeObject? = some C

/-- The DP confession has an internal self-evaluation / representability layer
exactly when such a datum is present in its structured summary. -/
def DpConfessionStructure.HasEvaluationMap
    (D : DpConfessionStructure) : Prop :=
  ∃ E, D.evaluationMap? = some E

/-- The DP confession has a contradiction-driving fixed-point-free endomap
exactly when such a datum is present in its structured summary. -/
def DpConfessionStructure.HasFixedPointFreeEndomap
    (D : DpConfessionStructure) : Prop :=
  ∃ F, D.fixedPointFreeEndomap? = some F

/-- Bundled Lawvere--Yanofsky instantiability from the DP-side summary. -/
def DpConfessionStructure.FurnishesLawvereYanofskySchema
    (D : DpConfessionStructure) : Prop :=
  ∃ S : LawvereYanofskySchema,
    D.internalCodeObject? = some S.codeObject
      ∧ D.evaluationMap? = some S.evaluationMap
      ∧ D.fixedPointFreeEndomap? = some S.fixedPointFreeEndomap

/-- Summary predicate for the repository's intended semantic separation claim:
finite graph certification is present, but the internal code / evaluation /
fixed-point-free package required by the Lawvere--Yanofsky route is absent. -/
def DpConfessionStructure.SemanticallySeparatedFromLawvereYanofsky
    (D : DpConfessionStructure) : Prop :=
  Nonempty D.pairCertificate.Node
    ∧ ¬ D.HasInternalCodeObject
    ∧ ¬ D.HasEvaluationMap
    ∧ ¬ D.HasFixedPointFreeEndomap
    ∧ ¬ D.FurnishesLawvereYanofskySchema

/-- The primitive duplicator has exactly one extracted dependency-pair node. -/
inductive PrimitiveDuplicatorPairNode
  | recSucc
  deriving DecidableEq, Repr, Fintype

/-- The singleton extracted-pair certificate carried by the primitive
duplicator's DP proof. -/
def primitiveDuplicatorFinitePairGraphCertificate :
    FinitePairGraphCertificate where
  Node := PrimitiveDuplicatorPairNode
  finiteNodes := inferInstance
  pairSemantics
    | .recSucc => schemaDPPairProblemEvidence Trace.void Trace.void Trace.void

/-- The concrete DP confession structure on the primitive duplicator. The three
Lawvere--Yanofsky slots are intentionally absent: the object records a finite
pair certificate and an external soundness license instead. -/
def primitiveDuplicatorDpConfessionStructure : DpConfessionStructure where
  routeEvidence := schemaDPRouteEvidence
  pairCertificate := primitiveDuplicatorFinitePairGraphCertificate
  externalLicense := dpConfession.license

@[simp] theorem primitive_duplicator_pair_node_card :
    Fintype.card PrimitiveDuplicatorPairNode = 1 := by
  decide

theorem primitive_duplicator_dp_confession_has_singleton_pair_graph :
    Fintype.card primitiveDuplicatorDpConfessionStructure.pairCertificate.Node = 1 := by
  simp [primitiveDuplicatorDpConfessionStructure, primitiveDuplicatorFinitePairGraphCertificate]

theorem primitive_duplicator_dp_confession_pair_problem_is_well_founded :
    WellFounded MetaDependencyPairs.DPPairRev :=
  primitiveDuplicatorDpConfessionStructure.routeEvidence.pairProblemWellFounded

theorem primitive_duplicator_dp_confession_lacks_internal_code_object :
    ¬ primitiveDuplicatorDpConfessionStructure.HasInternalCodeObject := by
  simp [DpConfessionStructure.HasInternalCodeObject, primitiveDuplicatorDpConfessionStructure]

theorem primitive_duplicator_dp_confession_lacks_evaluation_map :
    ¬ primitiveDuplicatorDpConfessionStructure.HasEvaluationMap := by
  simp [DpConfessionStructure.HasEvaluationMap, primitiveDuplicatorDpConfessionStructure]

theorem primitive_duplicator_dp_confession_lacks_fixed_point_free_endomap :
    ¬ primitiveDuplicatorDpConfessionStructure.HasFixedPointFreeEndomap := by
  simp [DpConfessionStructure.HasFixedPointFreeEndomap, primitiveDuplicatorDpConfessionStructure]

theorem primitive_duplicator_dp_confession_not_lawvere_yanofsky_schema :
    ¬ primitiveDuplicatorDpConfessionStructure.FurnishesLawvereYanofskySchema := by
  simp [DpConfessionStructure.FurnishesLawvereYanofskySchema, primitiveDuplicatorDpConfessionStructure]

theorem primitive_duplicator_dp_confession_semantically_separated_from_lawvere_yanofsky :
    primitiveDuplicatorDpConfessionStructure.SemanticallySeparatedFromLawvereYanofsky := by
  refine ⟨⟨PrimitiveDuplicatorPairNode.recSucc⟩, ?_, ?_, ?_, ?_⟩
  · exact primitive_duplicator_dp_confession_lacks_internal_code_object
  · exact primitive_duplicator_dp_confession_lacks_evaluation_map
  · exact primitive_duplicator_dp_confession_lacks_fixed_point_free_endomap
  · exact primitive_duplicator_dp_confession_not_lawvere_yanofsky_schema

theorem primitive_duplicator_dp_confession_semantic_profile :
    Fintype.card primitiveDuplicatorDpConfessionStructure.pairCertificate.Node = 1
      ∧ WellFounded MetaDependencyPairs.DPPairRev
      ∧ primitiveDuplicatorDpConfessionStructure.externalLicense = SoundnessLicense.artsGiesl2000
      ∧ primitiveDuplicatorDpConfessionStructure.SemanticallySeparatedFromLawvereYanofsky := by
  refine ⟨primitive_duplicator_dp_confession_has_singleton_pair_graph, ?_, rfl, ?_⟩
  · exact primitive_duplicator_dp_confession_pair_problem_is_well_founded
  · exact primitive_duplicator_dp_confession_semantically_separated_from_lawvere_yanofsky

end OperatorKO7.LawvereYanofskySeparation
