import OperatorKO7.Meta.DistinctionBoundary.GodelSigmaOne

set_option autoImplicit false

/-!
# Internal Sigma-one route: compiled prerequisite kill

The HBL roadmap requested an internal provability predicate for the induction
checker and a theorem `φ -> BewI(φ)` for every Sigma-one `φ`. The construction
was explicitly predicated on external Sigma-one completeness for the same
checker.

`GodelSigmaOne.lean` proves that external premise false: a standard-true closed
atomic formula belongs to the Sigma-one class but is not `ProvableI`. This
module records the resulting route theorem. It also types the stronger objects
that an internal construction would have to provide, without postulating them.
-/

namespace OperatorKO7.Meta.DistinctionBoundary.GodelArith

/-- Semantic representation requirement for any proposed internal provability
predicate of the induction checker. -/
def RepresentsCheckerI (BewI : Formula → Formula) : Prop :=
  ∀ φ : Formula, ∀ env : Nat → Nat,
    evalForm env (BewI φ) ↔ ProvableI φ

/-- The internal Sigma-one theorem requested by the HBL route. -/
def InternalSigmaOneCompleteness (BewI : Formula → Formula) : Prop :=
  ∀ φ : Formula, IsSigma1 φ →
    ProvableI (Formula.imp φ (BewI φ))

/-- Full prerequisite package for the internal Sigma-one construction. The
external completeness field is not bureaucratic: it is the exact Step-2 theorem
used to turn standard witnesses into checker proofs before internalization. -/
structure InternalSigmaOneRoute : Type where
  externalComplete : Sigma1Completeness
  BewI : Formula → Formula
  represents : RepresentsCheckerI BewI
  internalComplete : InternalSigmaOneCompleteness BewI

/-- No internal Sigma-one route satisfying the declared checker prerequisites
exists. -/
theorem internal_sigma1_route_impossible : ¬ Nonempty InternalSigmaOneRoute := by
  rintro ⟨h⟩
  exact sigma1_complete_impossible h.externalComplete

/-- The route is killed before the arithmetized induction-axiom recognizer can
be load-bearing. -/
structure InternalSigmaOneRouteKill : Prop where
  inductionCheckerSound : ∀ {φ : Formula}, ProvableI φ → evalForm env0 φ
  atomicWitnessSigmaOne : IsSigma1 sigmaOneCounterexample
  atomicWitnessTrue : evalForm env0 sigmaOneCounterexample
  atomicWitnessUnprovable : ¬ ProvableI sigmaOneCounterexample
  routeUninhabited : ¬ Nonempty InternalSigmaOneRoute

/-- Closed package for the Step-3 disposition. -/
theorem internal_sigma1_route_killed : InternalSigmaOneRouteKill where
  inductionCheckerSound := fun h => provableI_sound h env0
  atomicWitnessSigmaOne := sigmaOneCounterexample_isSigma1
  atomicWitnessTrue := sigmaOneCounterexample_true
  atomicWitnessUnprovable := sigmaOneCounterexample_not_provableI
  routeUninhabited := internal_sigma1_route_impossible

#check @RepresentsCheckerI
#check @InternalSigmaOneCompleteness
#check @InternalSigmaOneRoute
#check @internal_sigma1_route_impossible
#check @InternalSigmaOneRouteKill
#check @internal_sigma1_route_killed
#print axioms internal_sigma1_route_impossible
#print axioms internal_sigma1_route_killed

end OperatorKO7.Meta.DistinctionBoundary.GodelArith
