import OperatorKO7.Meta.InformationTheoreticConfession
import OperatorKO7.Meta.ConfessionMethod_RouteEvidence

/-!
# Confession Method Universal Instances

This module packages four confession methods as generic confession moves. Each
wrapper is constructed from an explicit equality between the method's rank and
the canonical dependency-pair rank.
-/

namespace OperatorKO7.Meta.ConfessionMethodUniversalInstances

open OperatorKO7
open OperatorKO7.Trace
open OperatorKO7.StepDuplicating
open OperatorKO7.StepDuplicating.StepDuplicatingSchema
open OperatorKO7.CompositionalImpossibility
open OperatorKO7.ConfessionMethodFamily
open OperatorKO7.Meta.GenericConfessionMove
open OperatorKO7.Meta.InformationTheoreticConfession

abbrev KO7Carrier := OperatorKO7.CompositionalImpossibility.ko7Schema.T

abbrev UniversalMove (X : Type _) (P : X → Prop) (License : Type _) :=
  OperatorKO7.Meta.GenericConfessionMove.GenericConfessionMove X P License

abbrev UniversalInfo {X : Type _} {P : X → Prop} {License : Type _}
    (M : UniversalMove X P License) :=
  OperatorKO7.Meta.InformationTheoreticConfession.InformationTheoreticConfession M

abbrev UniversalRouteLicense := PUnit

/-- The shared KO7 verdict used by the universal confession wrappers. -/
abbrev ko7ConfessionVerdict : KO7Carrier → Prop :=
  OperatorKO7.Meta.InformationTheoreticConfession.ko7ConfessionVerdict

/-- Package a KO7 rank function as a generic confession move, assuming equality
with the canonical dependency-pair rank. -/
def rankToGenericConfessionMove
    {License : Type _}
    (licenseWitness : License)
    (rank : KO7Carrier → Nat)
    (coreEq : rank = dpConfession.rank) :
    UniversalMove KO7Carrier ko7ConfessionVerdict License where
  licenseWitness := licenseWitness
  sourceBarrier := fun t => rank t = 0
  Quotient := Nat
  projection := rank
  residualObstruction := fun n => n = 0
  Certificate := Nat
  certificateOf := id
  verifier := fun n => n = 0
  verifier_sound := by
    intro q h
    exact h
  barrier_covers_residual := by
    intro x h
    simpa using h
  soundness := by
    intro x h
    simpa [ko7ConfessionVerdict, coreEq] using h
  verdictSufficient := by
    intro x x' hproj
    constructor <;> intro hx
    · have hx' : rank x = 0 := by
        simpa [ko7ConfessionVerdict, coreEq] using hx
      have hx'' : rank x' = 0 := by
        simpa [hproj] using hx'
      simpa [ko7ConfessionVerdict, coreEq] using hx''
    · have hx' : rank x' = 0 := by
        simpa [ko7ConfessionVerdict, coreEq] using hx
      have hx'' : rank x = 0 := by
        simpa [hproj] using hx'
      simpa [ko7ConfessionVerdict, coreEq] using hx''

/-- Package a confession method whose rank equals the canonical dependency-pair rank. -/
def methodToGenericConfessionMove
    (method : ConfessionMethod ko7Schema)
    (coreEq : method.rank = dpConfession.rank) :
  UniversalMove KO7Carrier ko7ConfessionVerdict SoundnessLicense :=
  rankToGenericConfessionMove method.license method.rank coreEq

/-- Package route-evidence rank data, assuming equality with the canonical
dependency-pair rank. -/
def routeEvidenceToGenericConfessionMove
    (routeEvidence : RouteEvidence ko7Schema)
    (coreEq : routeEvidence.rank = dpConfession.rank) :
    UniversalMove KO7Carrier ko7ConfessionVerdict UniversalRouteLicense :=
  rankToGenericConfessionMove PUnit.unit routeEvidence.rank coreEq

/-- The chosen canonical confession move is the dependency-pair wrapper. -/
def canonicalConfessionMove : UniversalMove KO7Carrier ko7ConfessionVerdict SoundnessLicense :=
  methodToGenericConfessionMove dpConfession rfl

/-- Abstract information profile for a wrapped KO7 confession move. The
discarded-information carrier and bit function are both the quotient-valued
rank, while the designated canonical bit count is zero. -/
def methodToInformationTheoreticConfession
    (method : ConfessionMethod ko7Schema)
    (coreEq : method.rank = dpConfession.rank) :
    UniversalInfo (methodToGenericConfessionMove method coreEq) where
  PreConfessionInformation := KO7Carrier
  PostVerdictInformation := Nat
  DiscardedInformation := Nat
  preEncode := id
  postEncode := id
  discardEncode := fun t => (methodToGenericConfessionMove method coreEq).projection t
  discardedBits := id
  canonicalDiscardedBits := 0

/-- Information profile attached to the canonical dependency-pair wrapper. -/
def canonicalInformationTheoreticConfession :
    UniversalInfo canonicalConfessionMove :=
  methodToInformationTheoreticConfession dpConfession rfl

/-- Abstract information profile for a route-evidence wrapper with canonical rank. -/
def routeEvidenceToInformationTheoreticConfession
    (routeEvidence : RouteEvidence ko7Schema)
    (coreEq : routeEvidence.rank = dpConfession.rank) :
    OperatorKO7.Meta.InformationTheoreticConfession.InformationTheoreticConfession
      (routeEvidenceToGenericConfessionMove routeEvidence coreEq) :=
  { PreConfessionInformation := KO7Carrier
    PostVerdictInformation := Nat
    DiscardedInformation := Nat
    preEncode := id
    postEncode := id
    discardEncode := routeEvidence.rank
    discardedBits := id
    canonicalDiscardedBits := 0 }

theorem dpRouteEvidence_rank_eq_dpConfession :
    schemaDPGenericRouteEvidence.rank = dpConfession.rank := rfl

theorem counterProjectionRouteEvidence_rank_eq_counterProjectionConfession :
    schemaDirectCounterProjectionGenericRouteEvidence.rank = counterProjectionConfession.rank := rfl

theorem sctRouteEvidence_rank_eq_sctConfession :
    schemaSCTGenericRouteEvidence.rank = sctConfession.rank := rfl

theorem argumentFilteringRouteEvidence_rank_eq_argumentFilteringConfession :
    schemaArgumentFilteringGenericRouteEvidence.rank = argumentFilteringConfession.rank := rfl

/-- A wrapped method with canonical rank refines the canonical move by the identity map. -/
theorem methodToGenericConfessionMove_refines_canonical
    (method : ConfessionMethod ko7Schema)
    (coreEq : method.rank = dpConfession.rank) :
    GenericConfessionMove.Refines
      (methodToGenericConfessionMove method coreEq)
      canonicalConfessionMove := by
  exact ⟨{
    factor := id
    commutes := by
      intro x
      exact congrFun coreEq x
  }⟩

/-- The canonical move refines a wrapped method with the same rank by the identity map. -/
theorem canonical_refines_methodToGenericConfessionMove
    (method : ConfessionMethod ko7Schema)
    (coreEq : method.rank = dpConfession.rank) :
    GenericConfessionMove.Refines
      canonicalConfessionMove
      (methodToGenericConfessionMove method coreEq) := by
  exact ⟨{
    factor := id
    commutes := by
      intro x
      exact (congrFun coreEq x).symm
  }⟩

/-- A wrapped method with canonical rank is H-equivalent to the canonical move. -/
theorem methodToGenericConfessionMove_HEquivalent_canonical
    (method : ConfessionMethod ko7Schema)
    (coreEq : method.rank = dpConfession.rank) :
    GenericConfessionMove.HEquivalent
      (methodToGenericConfessionMove method coreEq)
      canonicalConfessionMove := by
  exact ⟨{
    forward := Classical.choice (methodToGenericConfessionMove_refines_canonical method coreEq)
    backward := Classical.choice (canonical_refines_methodToGenericConfessionMove method coreEq)
  }⟩

/-- A route-evidence wrapper with canonical rank refines the canonical move. -/
theorem routeEvidenceToGenericConfessionMove_refines_canonical
    (routeEvidence : RouteEvidence ko7Schema)
    (coreEq : routeEvidence.rank = dpConfession.rank) :
    GenericConfessionMove.Refines
      (routeEvidenceToGenericConfessionMove routeEvidence coreEq)
      canonicalConfessionMove := by
  exact ⟨{
    factor := id
    commutes := by
      intro x
      exact congrFun coreEq x
  }⟩

/-- The canonical move refines a route-evidence wrapper with the same rank. -/
theorem canonical_refines_routeEvidenceToGenericConfessionMove
    (routeEvidence : RouteEvidence ko7Schema)
    (coreEq : routeEvidence.rank = dpConfession.rank) :
    GenericConfessionMove.Refines
      canonicalConfessionMove
      (routeEvidenceToGenericConfessionMove routeEvidence coreEq) := by
  exact ⟨{
    factor := id
    commutes := by
      intro x
      exact (congrFun coreEq x).symm
  }⟩

/-- A route-evidence wrapper with canonical rank is H-equivalent to the canonical move. -/
theorem routeEvidenceToGenericConfessionMove_HEquivalent_canonical
    (routeEvidence : RouteEvidence ko7Schema)
    (coreEq : routeEvidence.rank = dpConfession.rank) :
    GenericConfessionMove.HEquivalent
      (routeEvidenceToGenericConfessionMove routeEvidence coreEq)
      canonicalConfessionMove := by
  exact ⟨{
    forward := Classical.choice (routeEvidenceToGenericConfessionMove_refines_canonical routeEvidence coreEq)
    backward := Classical.choice
      (canonical_refines_routeEvidenceToGenericConfessionMove routeEvidence coreEq)
  }⟩

/-- Canonical-rank equality supplies the required refinement record. -/
def methodUniversalCharacterizationData
    (method : ConfessionMethod ko7Schema)
    (coreEq : method.rank = dpConfession.rank) :
    UniversalConfessionCharacterizationData
      canonicalConfessionMove
      (methodToGenericConfessionMove method coreEq) where
  factorization := methodToGenericConfessionMove_refines_canonical method coreEq

/-- Canonical-rank equality supplies the factorization and reverse projection
required by `OptimalityData`. -/
def methodOptimalityData
    (method : ConfessionMethod ko7Schema)
    (coreEq : method.rank = dpConfession.rank) :
    OptimalityData
      canonicalConfessionMove
      (methodToGenericConfessionMove method coreEq) where
  factorization := methodUniversalCharacterizationData method coreEq
  uniqueness := by
    intro _
    refine ⟨id, ?_⟩
    intro x
    exact (congrFun coreEq x).symm

/-- The two zero-valued canonical-bit fields satisfy the abstract minimality record. -/
def methodDiscardedInformationMinimalityData
    (method : ConfessionMethod ko7Schema)
    (coreEq : method.rank = dpConfession.rank) :
    DiscardedInformationMinimalityData
      canonicalInformationTheoreticConfession
      (methodToInformationTheoreticConfession method coreEq) where
  canonical_le_candidate := by
    simp [canonicalInformationTheoreticConfession, methodToInformationTheoreticConfession]

/-- Record storing a confession method, route evidence, its generic wrapper,
and the wrapper's abstract information profile. Compatibility between the
method and route evidence is supplied separately where required. -/
structure ConfessionMethodUniversalInstance where
  name : String
  method : ConfessionMethod ko7Schema
  routeEvidence : RouteEvidence ko7Schema
  move : UniversalMove KO7Carrier ko7ConfessionVerdict SoundnessLicense
  informationProfile : UniversalInfo move

/-- Construct a universal instance from a method, route evidence, and an
explicit equality between the method rank and canonical rank. -/
def futureConfessionMethodUniversalInstance
    (name : String)
    (method : ConfessionMethod ko7Schema)
    (routeEvidence : RouteEvidence ko7Schema)
    (coreEq : method.rank = dpConfession.rank) :
    ConfessionMethodUniversalInstance where
  name := name
  method := method
  routeEvidence := routeEvidence
  move := methodToGenericConfessionMove method coreEq
  informationProfile := methodToInformationTheoreticConfession method coreEq

def dpUniversalInstance : ConfessionMethodUniversalInstance where
  name := "DP"
  method := dpConfession
  routeEvidence := schemaDPGenericRouteEvidence
  move := canonicalConfessionMove
  informationProfile := canonicalInformationTheoreticConfession

def counterProjectionUniversalInstance : ConfessionMethodUniversalInstance where
  name := "CounterProjection"
  method := counterProjectionConfession
  routeEvidence := schemaDirectCounterProjectionGenericRouteEvidence
  move := methodToGenericConfessionMove counterProjectionConfession counterProjection_eq_dp_rank
  informationProfile := methodToInformationTheoreticConfession counterProjectionConfession counterProjection_eq_dp_rank

def sctUniversalInstance : ConfessionMethodUniversalInstance where
  name := "SCT"
  method := sctConfession
  routeEvidence := schemaSCTGenericRouteEvidence
  move := methodToGenericConfessionMove sctConfession sct_eq_dp_rank
  informationProfile := methodToInformationTheoreticConfession sctConfession sct_eq_dp_rank

def argumentFilteringUniversalInstance : ConfessionMethodUniversalInstance where
  name := "ArgumentFiltering"
  method := argumentFilteringConfession
  routeEvidence := schemaArgumentFilteringGenericRouteEvidence
  move := methodToGenericConfessionMove argumentFilteringConfession argumentFiltering_eq_dp_rank
  informationProfile := methodToInformationTheoreticConfession argumentFilteringConfession argumentFiltering_eq_dp_rank

/-- Names of the four universal instances defined in this module. -/
def universalInstanceNames : List String :=
  [dpUniversalInstance.name,
    counterProjectionUniversalInstance.name,
    sctUniversalInstance.name,
    argumentFilteringUniversalInstance.name]

theorem universalInstanceNames_length : universalInstanceNames.length = 4 := by
  rfl

/-- The four declared method wrappers are H-equivalent to the canonical move
through their proved rank equalities. -/
theorem all_existing_confession_routes_are_HEquivalent_to_canonical :
    GenericConfessionMove.HEquivalent dpUniversalInstance.move canonicalConfessionMove
      ∧ GenericConfessionMove.HEquivalent counterProjectionUniversalInstance.move canonicalConfessionMove
      ∧ GenericConfessionMove.HEquivalent sctUniversalInstance.move canonicalConfessionMove
      ∧ GenericConfessionMove.HEquivalent argumentFilteringUniversalInstance.move canonicalConfessionMove := by
  exact ⟨methodToGenericConfessionMove_HEquivalent_canonical dpConfession rfl,
    methodToGenericConfessionMove_HEquivalent_canonical counterProjectionConfession counterProjection_eq_dp_rank,
    methodToGenericConfessionMove_HEquivalent_canonical sctConfession sct_eq_dp_rank,
    methodToGenericConfessionMove_HEquivalent_canonical argumentFilteringConfession argumentFiltering_eq_dp_rank⟩

/-- A method with canonical rank and matching route-evidence rank yields a
route-evidence refinement and a method-wrapper H-equivalence. -/
theorem future_confessionMethod_with_rank_eq_and_routeEvidence_rank_eq_method_projects_to_universal_surface
    (name : String)
    (method : ConfessionMethod ko7Schema)
    (routeEvidence : RouteEvidence ko7Schema)
    (methodRankEq : method.rank = dpConfession.rank)
    (routeRankEq : routeEvidence.rank = method.rank) :
    GenericConfessionMove.Refines
        (routeEvidenceToGenericConfessionMove routeEvidence (routeRankEq.trans methodRankEq))
        canonicalConfessionMove
      ∧ GenericConfessionMove.HEquivalent
        (futureConfessionMethodUniversalInstance name method routeEvidence methodRankEq).move
        canonicalConfessionMove := by
  exact ⟨routeEvidenceToGenericConfessionMove_refines_canonical
      routeEvidence (routeRankEq.trans methodRankEq),
    methodToGenericConfessionMove_HEquivalent_canonical method methodRankEq⟩

end OperatorKO7.Meta.ConfessionMethodUniversalInstances
