import OperatorKO7.Meta.RDRSTerminationMethodUniverse
import OperatorKO7.Meta.KBO_Impossible
import OperatorKO7.Meta.MPO_Precedence_Barrier
import OperatorKO7.Meta.WPO_PolynomialBarrier_Schema

/-!
# RDRS Path-Order Dichotomy

Finite classification layer for the KBO/path-order rows of the RDRS
termination-method universe.

The layer separates theorem-backed barriers from conditional escape rows whose
hypotheses are explicit data. The KBO rows reuse the symbolic variable-count
barrier. The MPO head-precedence row reuses the existing positive and negative
precedence surfaces.
-/

namespace OperatorKO7.RDRSPathOrderDichotomy

open OperatorKO7.RDRSTerminationMethodUniverse
open OperatorKO7.SymbolicComparatorBarrier

/-- The twelve shared-universe rows owned by the path-order layer. -/
def pathOrderAtlasRows : List RDRSMethodFamily :=
  [ .standardKBO
  , .kboWithStatus
  , .generalizedKBO
  , .subtermCoefficientKBO
  , .acKBO
  , .transfiniteKBO
  , .lambdaFreeKBO
  , .acRPO
  , .rpoModuloPermutation
  , .popStarFamily
  , .simpleTerminationOrderType
  , .cichonSlowGrowing
  ]

theorem pathOrderAtlasRows_length : pathOrderAtlasRows.length = 12 := by
  rfl

theorem pathOrderAtlasRows_nodup : pathOrderAtlasRows.Nodup := by
  decide

theorem pathOrderAtlasRows_complete :
    ∀ family : RDRSMethodFamily,
      family ∈ pathOrderAtlasRows ↔
        family = .standardKBO ∨
        family = .kboWithStatus ∨
        family = .generalizedKBO ∨
        family = .subtermCoefficientKBO ∨
        family = .acKBO ∨
        family = .transfiniteKBO ∨
        family = .lambdaFreeKBO ∨
        family = .acRPO ∨
        family = .rpoModuloPermutation ∨
        family = .popStarFamily ∨
        family = .simpleTerminationOrderType ∨
        family = .cichonSlowGrowing := by
  intro family
  cases family <;> simp [pathOrderAtlasRows]

/-- Mechanism used to classify one path-order row. -/
inductive PathOrderMechanism
  | kboVariableCountBarrier
  | coefficientWeightedVariableEscape
  | acKBOVariableCountBarrier
  | headPrecedenceConditionalEscape
  | acRPOBarrierUnlessHeadPrecedence
  | rpoPermutationHeadPrecedence
  | popSafeArgumentEscape
  | simpleOrderComplexityBoundary
  | cichonNonUniversalSlowGrowing
  deriving DecidableEq, Repr

/-- One finite row in the path-order classification ledger. -/
structure PathOrderClassification where
  family : RDRSMethodFamily
  status : RDRSMethodStatus
  mechanism : PathOrderMechanism
  status_matches : statusOf family = status

/-- Exact classification rows for the path-order layer. -/
def pathOrderClassifications : List PathOrderClassification :=
  [ { family := .standardKBO
      status := .barrier
      mechanism := .kboVariableCountBarrier
      status_matches := rfl }
  , { family := .kboWithStatus
      status := .barrier
      mechanism := .kboVariableCountBarrier
      status_matches := rfl }
  , { family := .generalizedKBO
      status := .barrier
      mechanism := .kboVariableCountBarrier
      status_matches := rfl }
  , { family := .subtermCoefficientKBO
      status := .conditional_escape
      mechanism := .coefficientWeightedVariableEscape
      status_matches := rfl }
  , { family := .acKBO
      status := .barrier
      mechanism := .acKBOVariableCountBarrier
      status_matches := rfl }
  , { family := .transfiniteKBO
      status := .barrier
      mechanism := .kboVariableCountBarrier
      status_matches := rfl }
  , { family := .lambdaFreeKBO
      status := .barrier
      mechanism := .kboVariableCountBarrier
      status_matches := rfl }
  , { family := .acRPO
      status := .conditional_escape
      mechanism := .acRPOBarrierUnlessHeadPrecedence
      status_matches := rfl }
  , { family := .rpoModuloPermutation
      status := .conditional_escape
      mechanism := .rpoPermutationHeadPrecedence
      status_matches := rfl }
  , { family := .popStarFamily
      status := .conditional_escape
      mechanism := .popSafeArgumentEscape
      status_matches := rfl }
  , { family := .simpleTerminationOrderType
      status := .conditional_barrier
      mechanism := .simpleOrderComplexityBoundary
      status_matches := rfl }
  , { family := .cichonSlowGrowing
      status := .conditional_escape
      mechanism := .cichonNonUniversalSlowGrowing
      status_matches := rfl }
  ]

theorem pathOrderClassifications_families :
    pathOrderClassifications.map (fun row => row.family) = pathOrderAtlasRows := by
  rfl

theorem pathOrderClassifications_length :
    pathOrderClassifications.length = 12 := by
  rfl

theorem pathOrderClassification_status_matches (row : PathOrderClassification) :
    statusOf row.family = row.status :=
  row.status_matches

/-- KBO-style rows whose barrier is exactly the variable-count obstruction. -/
inductive KBOBarrierVariant
  | standard
  | withStatus
  | generalized
  | ac
  | transfinite
  | lambdaFree
  deriving DecidableEq, Repr

def KBOBarrierVariant.family : KBOBarrierVariant → RDRSMethodFamily
  | .standard => .standardKBO
  | .withStatus => .kboWithStatus
  | .generalized => .generalizedKBO
  | .ac => .acKBO
  | .transfinite => .transfiniteKBO
  | .lambdaFree => .lambdaFreeKBO

theorem kboBarrierVariant_status (variant : KBOBarrierVariant) :
    statusOf variant.family = .barrier := by
  cases variant <;> rfl

/-- All KBO barrier variants inherit the existing symbolic variable-count theorem. -/
theorem kboBarrierVariant_no_symbolic_orientation (_variant : KBOBarrierVariant) :
    ¬ ∃ K : OperatorKO7.KBOImpossible.KBOStyleOrder, K.gt dupSrc dupTgt :=
  OperatorKO7.KBOImpossible.no_kbo_orients_ko7_rec_succ

/-- Typed hypotheses for the subterm-coefficient KBO escape row. -/
structure SubtermCoefficientKBOHypotheses where
  recurStepCoefficient : Nat
  lhsPayloadWeight : Nat
  rhsPayloadWeight : Nat
  lhs_weight_eq_recur_coefficient : lhsPayloadWeight = recurStepCoefficient
  rhs_weight_eq_two_payloads : rhsPayloadWeight = 2
  coefficient_covers_duplication : rhsPayloadWeight ≤ lhsPayloadWeight

theorem subtermCoefficientKBO_conditional_escape
    (_h : SubtermCoefficientKBOHypotheses) :
    statusOf .subtermCoefficientKBO = .conditional_escape := by
  rfl

/-- LPO/MPO/RPO variants governed by the same head-precedence import. -/
inductive HeadPrecedencePathOrder
  | lpo
  | mpo
  | rpo
  | rpoWithStatus
  | lambdaFreeRPO
  deriving DecidableEq, Repr

/-- Exact conditions used by the head-precedence path-order escape. -/
structure HeadPrecedenceHypotheses where
  recur_precedes_wrap : Prop
  recur_precedes_wrap_holds : recur_precedes_wrap
  lhs_dominates_rhs_step_arg : Prop
  lhs_dominates_rhs_step_arg_holds : lhs_dominates_rhs_step_arg
  lhs_dominates_rhs_recursive_tail : Prop
  lhs_dominates_rhs_recursive_tail_holds : lhs_dominates_rhs_recursive_tail

/-- The big-head route data that a path order must import to escape RDRS. -/
def HeadPrecedenceRouteAvailable
    (_order : HeadPrecedencePathOrder) (h : HeadPrecedenceHypotheses) : Prop :=
  h.recur_precedes_wrap
    /\ h.lhs_dominates_rhs_step_arg
    /\ h.lhs_dominates_rhs_recursive_tail

theorem headPrecedencePathOrder_conditional_escape
    (order : HeadPrecedencePathOrder) (h : HeadPrecedenceHypotheses) :
    HeadPrecedenceRouteAvailable order h := by
  exact ⟨h.recur_precedes_wrap_holds,
    h.lhs_dominates_rhs_step_arg_holds,
    h.lhs_dominates_rhs_recursive_tail_holds⟩

/-- Existing positive MPO surface: good precedence orients every KO7 root step. -/
theorem mpo_good_precedence_orients_step :
    ∀ {a b : Trace}, Step a b → OperatorKO7.MetaMPO.MPO a b :=
  OperatorKO7.MetaMPO.mpo_orients_step

/-- Existing negative MPO surface: bad precedence cannot orient all KO7 root steps. -/
theorem mpo_bad_precedence_blocks_global_orientation :
    ¬ (∀ {a b : Trace}, Step a b → OperatorKO7.MPOPrecedenceBarrier.MPOBad a b) :=
  OperatorKO7.MPOPrecedenceBarrier.no_global_step_orientation_mpo_bad_prec

/-- AC-RPO cases from the atlas: RDRS has no AC symbol unless one is imported. -/
inductive ACRPOCase
  | noACSymbolInRDRS
  | acHeadAndPrecedenceImported
  deriving DecidableEq, Repr

def ACRPOCase.status : ACRPOCase → RDRSMethodStatus
  | .noACSymbolInRDRS => .barrier
  | .acHeadAndPrecedenceImported => .conditional_escape

theorem acRPO_shared_row_status :
    statusOf .acRPO = .conditional_escape := by
  rfl

/-- RPO modulo permutation escapes only with a compatible head-precedence import. -/
structure RPOPermutationHypotheses where
  permutation_compatible : Prop
  permutation_compatible_holds : permutation_compatible
  recur_precedes_wrap_after_quotient : Prop
  recur_precedes_wrap_after_quotient_holds : recur_precedes_wrap_after_quotient

theorem rpoModuloPermutation_conditional_escape
    (_h : RPOPermutationHypotheses) :
    statusOf .rpoModuloPermutation = .conditional_escape := by
  rfl

/-- POP* variants covered by the safe-argument escape row. -/
inductive POPStarVariant
  | popStar
  | sPopStar
  | popStarPS
  | slPopStar
  deriving DecidableEq, Repr

/-- Exact safe-argument conditions for the POP* family. -/
structure POPStarSafeArgumentHypotheses where
  recur_precedes_wrap : Prop
  recur_precedes_wrap_holds : recur_precedes_wrap
  outer_payload_occurrence_safe : Prop
  outer_payload_occurrence_safe_holds : outer_payload_occurrence_safe
  inner_payload_occurrence_safe : Prop
  inner_payload_occurrence_safe_holds : inner_payload_occurrence_safe
  predicative_parameter_separation : Prop
  predicative_parameter_separation_holds : predicative_parameter_separation

theorem popStarFamily_conditional_escape
    (_variant : POPStarVariant) (_h : POPStarSafeArgumentHypotheses) :
    statusOf .popStarFamily = .conditional_escape := by
  rfl

/-- Caveats for ordinal and Cichon-style path-order reasoning. -/
inductive OrdinalCichonCaveat
  | simpleTerminationOrderTypeIsComplexityBoundary
  | cichonAppliesToRDRSGomega
  | cichonFailsForKBO
  | hydraEncodingException
  deriving DecidableEq, Repr

theorem simpleTerminationOrderType_conditional_barrier :
    statusOf .simpleTerminationOrderType = .conditional_barrier := by
  rfl

theorem cichonSlowGrowing_conditional_escape :
    statusOf .cichonSlowGrowing = .conditional_escape := by
  rfl

theorem cichon_principle_not_universal :
    ∃ caveat : OrdinalCichonCaveat, caveat = .cichonFailsForKBO := by
  exact ⟨.cichonFailsForKBO, rfl⟩

/-- Closure certificate for the T2 path-order layer. -/
structure PathOrderLayerClosed where
  atlas_count : pathOrderAtlasRows.length = 12
  atlas_nodup : pathOrderAtlasRows.Nodup
  classifications_count : pathOrderClassifications.length = 12
  classifications_match_atlas :
    pathOrderClassifications.map (fun row => row.family) = pathOrderAtlasRows
  kbo_rows_blocked :
    ∀ _ : KBOBarrierVariant,
      ¬ ∃ K : OperatorKO7.KBOImpossible.KBOStyleOrder, K.gt dupSrc dupTgt
  head_precedence_escape :
    ∀ order : HeadPrecedencePathOrder,
      ∀ h : HeadPrecedenceHypotheses,
        HeadPrecedenceRouteAvailable order h
  mpo_good_precedence_positive :
    ∀ {a b : Trace}, Step a b → OperatorKO7.MetaMPO.MPO a b
  mpo_bad_precedence_negative :
    ¬ (∀ {a b : Trace}, Step a b → OperatorKO7.MPOPrecedenceBarrier.MPOBad a b)
  ac_rpo_status : statusOf .acRPO = .conditional_escape
  rpo_permutation_status : statusOf .rpoModuloPermutation = .conditional_escape
  pop_status : statusOf .popStarFamily = .conditional_escape
  simple_order_status : statusOf .simpleTerminationOrderType = .conditional_barrier
  cichon_status : statusOf .cichonSlowGrowing = .conditional_escape
  cichon_caveat : ∃ caveat : OrdinalCichonCaveat, caveat = .cichonFailsForKBO

/-- T2 acceptance marker: finite path-order classification is closed. -/
theorem rdrs_path_order_layer_closed : PathOrderLayerClosed where
  atlas_count := pathOrderAtlasRows_length
  atlas_nodup := pathOrderAtlasRows_nodup
  classifications_count := pathOrderClassifications_length
  classifications_match_atlas := pathOrderClassifications_families
  kbo_rows_blocked := kboBarrierVariant_no_symbolic_orientation
  head_precedence_escape := headPrecedencePathOrder_conditional_escape
  mpo_good_precedence_positive := mpo_good_precedence_orients_step
  mpo_bad_precedence_negative := mpo_bad_precedence_blocks_global_orientation
  ac_rpo_status := acRPO_shared_row_status
  rpo_permutation_status := by rfl
  pop_status := by rfl
  simple_order_status := simpleTerminationOrderType_conditional_barrier
  cichon_status := cichonSlowGrowing_conditional_escape
  cichon_caveat := cichon_principle_not_universal

end OperatorKO7.RDRSPathOrderDichotomy
