import OperatorKO7.Meta.DistinctionBoundary.GodelInternalSigmaOne
import OperatorKO7.Meta.DistinctionBoundary.GodelNonstandardModel

set_option autoImplicit false

/-!
# Terminal disposition of the internal HBL route

The model-theoretic route for the live compiled Q checker is already complete:
`godel_second_incompleteness_Q_unconditional` proves that `ConQ` is not
provable. This module types the stronger induction/HBL route and proves that its
declared prerequisite package is uninhabited for the current equality calculus.

The result is not a generic rejection of HBL mathematics. It is a theorem about
this checker: full induction was added and proved sound, but a weak
interpretation validates the entire checker while refuting a standard-true
atomic equality. External Sigma-one completeness therefore fails before the
internal D3 construction begins.
-/

namespace OperatorKO7.Meta.DistinctionBoundary.GodelArith

/-- Object-level D1 for a proposed induction-checker provability predicate. -/
def HBLD1I (BewI : Formula → Formula) : Prop :=
  ∀ φ : Formula, ProvableI φ → ProvableI (BewI φ)

/-- Object-level D2 for a proposed induction-checker provability predicate. -/
def HBLD2I (BewI : Formula → Formula) : Prop :=
  ∀ φ ψ : Formula,
    ProvableI
      (Formula.imp (BewI (Formula.imp φ ψ))
        (Formula.imp (BewI φ) (BewI ψ)))

/-- Object-level D3 for a proposed induction-checker provability predicate. -/
def HBLD3I (BewI : Formula → Formula) : Prop :=
  ∀ φ : Formula,
    ProvableI (Formula.imp (BewI φ) (BewI (BewI φ)))

/-- The full declared internal route. -/
structure HBLRouteI : Type where
  sigmaRoute : InternalSigmaOneRoute
  d1 : HBLD1I sigmaRoute.BewI
  d2 : HBLD2I sigmaRoute.BewI
  d3 : HBLD3I sigmaRoute.BewI

/-- The HBL route is uninhabited because its Sigma-one prerequisite is already
refuted by `sigmaOneCounterexample`. -/
theorem hbl_routeI_impossible : ¬ Nonempty HBLRouteI := by
  rintro ⟨h⟩
  exact internal_sigma1_route_impossible ⟨h.sigmaRoute⟩

/-- Route A is a theorem and the declared Route B is impossible on the current
checker. This is the terminal comparison result. -/
structure GodelIIRouteDisposition : Prop where
  routeA : ¬ Provable ConQ
  routeBImpossible : ¬ Nonempty HBLRouteI
  inductionExtensionConsistent : ¬ ProvableI falsum
  sigmaFailureWitness :
    IsSigma1 sigmaOneCounterexample ∧
      evalForm env0 sigmaOneCounterexample ∧
      ¬ ProvableI sigmaOneCounterexample

/-- Complete route disposition: model-theoretic Gödel II lands; the proposed
internal HBL route is killed at external Sigma-one completeness. -/
theorem godelII_routes_terminal : GodelIIRouteDisposition where
  routeA := godel_second_incompleteness_Q_unconditional
  routeBImpossible := hbl_routeI_impossible
  inductionExtensionConsistent := induction_checker_consistent
  sigmaFailureWitness :=
    ⟨sigmaOneCounterexample_isSigma1,
      sigmaOneCounterexample_true,
      sigmaOneCounterexample_not_provableI⟩

/-- The final Gödel-II verdict is independent of the failed internal route. -/
theorem godelII_live_checker_closed_despite_HBL_kill :
    (¬ Provable ConQ) ∧ (¬ Nonempty HBLRouteI) :=
  ⟨godel_second_incompleteness_Q_unconditional, hbl_routeI_impossible⟩

#check @HBLD1I
#check @HBLD2I
#check @HBLD3I
#check @HBLRouteI
#check @hbl_routeI_impossible
#check @GodelIIRouteDisposition
#check @godelII_routes_terminal
#check @godelII_live_checker_closed_despite_HBL_kill
#print axioms hbl_routeI_impossible
#print axioms godelII_routes_terminal
#print axioms godelII_live_checker_closed_despite_HBL_kill

end OperatorKO7.Meta.DistinctionBoundary.GodelArith
