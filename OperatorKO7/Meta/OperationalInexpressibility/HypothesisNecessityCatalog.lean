import OperatorKO7.Meta.OperationalInexpressibility.NormalFormFaithfulTransport
import OperatorKO7.Meta.OperationalInexpressibility.ConfusabilityGraph
import OperatorKO7.Meta.OperationalInexpressibility.RelationalRecovery
import OperatorKO7.Meta.OperationalInexpressibility.NoisyRecovery
import OperatorKO7.Meta.OperationalInexpressibility.CostComparison
import OperatorKO7.Meta.OperationalInexpressibility.JointTargetCapacity
import OperatorKO7.Meta.OperationalInexpressibility.FiniteObserverRecurrence
import OperatorKO7.Meta.OperationalInexpressibility.DefinitionUnification
import OperatorKO7.Meta.OperationalInexpressibility.ConfluenceTransport
import OperatorKO7.Meta.OperationalInexpressibility.DirectGrammarBoundary
import OperatorKO7.Meta.OperationalInexpressibility.BlackwellOrder
import OperatorKO7.Meta.OperationalInexpressibility.SufficiencyInstance
import OperatorKO7.Meta.OperationalInexpressibility.FiberEntropyBound
import OperatorKO7.Meta.OperationalInexpressibility.RelationalSideCapacity
import OperatorKO7.Meta.OperationalInexpressibility.ExecutableLicense

/-!
# Hypothesis-necessity catalog

Each theorem of the package carries hypotheses. For each hypothesis this module records a fixture
in which the hypothesis fails and the conclusion of the theorem fails with it. Most fixtures live
beside their theorems; this module adds three: a rotation of three states read by the test for
zero, whose orbit-observer kernels keep changing without observation compatibility; the natural
numbers under the constant observer, whose infinite fiber admits no finite side channel; and a
certificate task with no admissible certificate, on which the capacity search returns `none`. The
theorem `hypothesisNecessity_catalog` conjoins every fixture statement, each read off the fixture
theorem itself.

Relation: the relation of each source theorem.
Property: necessity of each hypothesis, witnessed by a fixture.
Trust: kernel only; the finite fixtures are evaluated by `decide`.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.OperationalInexpressibility.HypothesisNecessityCatalog

/-! ## Compatibility for finite stabilization -/

/-- Rotation of three states. -/
def rotate3 (x : Fin 3) : Fin 3 := x + 1

/-- The observer that tests whether the state is `0`. -/
def isZeroObserver (x : Fin 3) : Bool := decide (x = 0)

/-- **Compatibility is required for finite stabilization.** Rotation of three states read by the
test for `0` is not observation-compatible; its orbit-observer kernel at stage two differs from the
kernel at the bound `card Bool - 1`; and a target licensed at the bound is not licensed at every
stage. -/
theorem compatibility_is_required_for_finite_stabilization :
    ¬ FiniteObserverRecurrence.ObservationCompatible rotate3 isZeroObserver ∧
      ¬ (∀ n, Fintype.card Bool - 1 ≤ n → ∀ x y : Fin 3,
          (FiniteObserverRecurrence.orbitObserver rotate3 isZeroObserver n x =
              FiniteObserverRecurrence.orbitObserver rotate3 isZeroObserver n y ↔
            FiniteObserverRecurrence.orbitObserver rotate3 isZeroObserver
                (Fintype.card Bool - 1) x =
              FiniteObserverRecurrence.orbitObserver rotate3 isZeroObserver
                (Fintype.card Bool - 1) y)) ∧
      LicenseCriterion.Licensed
        (FiniteObserverRecurrence.orbitObserver rotate3 isZeroObserver (Fintype.card Bool - 1))
        (FiniteObserverRecurrence.orbitObserver rotate3 isZeroObserver 1) ∧
      ¬ ∀ n, LicenseCriterion.Licensed
        (FiniteObserverRecurrence.orbitObserver rotate3 isZeroObserver n)
        (FiniteObserverRecurrence.orbitObserver rotate3 isZeroObserver 1) := by
  refine ⟨fun hc => ?_, fun h => ?_, ?_, fun h => ?_⟩
  · have h12 := hc 1 2 (by decide)
    revert h12
    decide
  · have h01 := (h 2 (by decide) 0 1).2 (by decide)
    revert h01
    decide
  · unfold LicenseCriterion.Licensed
    decide
  · have h02 := h 2 0 2 (by decide)
    revert h02
    decide

/-! ## Finiteness for exact capacity -/

/-- **Finiteness is required for exact capacity.** On the natural numbers read by the constant
observer, the identity target has an infinite fiber, and no finite side channel resolves it. -/
theorem finiteness_is_required_for_exact_capacity (m : ℕ) :
    ¬ ∃ s : ℕ → Fin m, ObserverKernel.FactorsThrough (fun x => ((fun _ : ℕ => ()) x, s x))
      (fun x : ℕ => x) := by
  rintro ⟨s, hs⟩
  obtain ⟨a, b, hne, hab⟩ :=
    Fintype.exists_ne_map_eq_of_card_lt (fun i : Fin (m + 1) => s i.val) (by simp)
  exact hne (Fin.ext (hs (Prod.ext rfl hab)))

/-! ## Certificate existence for a finite capacity -/

/-- **Certificate existence is required for a finite capacity.** When no certificate is admissible
at the single state, the exhaustive capacity search returns `none`. -/
theorem certificate_existence_is_required :
    RelationalSideCapacity.relationalSideCapacity? ExecutableLicense.unitEnumeration
      ExecutableLicense.unitEnumeration (fun _ : Unit => ()) (fun _ _ => False) = none :=
  (RelationalSideCapacity.relationalSideCapacity?_eq_none_iff _ _ _ _).2 ⟨(), fun _ h => h⟩

/-! ## The catalog -/

/-- **Hypothesis-necessity catalog.** Each conjunct is the statement of a fixture in which one
hypothesis of a theorem of the package fails and the conclusion fails with it. -/
theorem hypothesisNecessity_catalog :
    -- a nonempty verdict type: factorization through the observer without a total decoder
    type_of% @DirectGrammarBoundary.emptyWorldTarget_factorsThrough ∧
    type_of% @DirectGrammarBoundary.emptyWorldTarget_not_verdictDeterminedBy ∧
    -- normal-form injectivity for uniqueness transport: the collapsed fork
    type_of% @NormalFormFaithfulTransport.normalForm_injectivity_is_required ∧
    -- a strict stutter rank for termination transport: the one-state loop
    type_of% @NormalFormFaithfulTransport.stutter_descent_is_required_for_termination_transport ∧
    -- coarsening for stagewise channels: the three-pair fixture
    type_of% @Confusability.threePair_stagewise_two_symbols ∧
    type_of% @Confusability.threePair_no_common_two_symbols ∧
    type_of% @Confusability.threePair_not_coarsening ∧
    -- global common witnesses, not pairwise ones: the three-way fixture
    type_of% @RelationalRecovery.pairwiseFiberCompatible_not_sufficient ∧
    -- the decoder language: the constant-false language
    type_of% @RelationalRecovery.boolIdentity_directRelationalRecovery ∧
    type_of% @RelationalRecovery.boolIdentity_falseOnlyLanguage_fails ∧
    -- full support for zero risk: the zero-mass collision
    type_of% @NoisyRecovery.zeroMassCollision_support_pure ∧
    type_of% @NoisyRecovery.zeroMassCollision_not_fullCarrier ∧
    -- positive payload for a crossing: zero payload never crosses
    type_of% @CostComparison.zero_payload_never_strict ∧
    -- independent targets for the product bound: the duplicated target
    type_of% @JointTargetCapacity.duplicated_target_product_bound_not_tight ∧
    -- observation compatibility for finite stabilization: the rotation
    type_of% @compatibility_is_required_for_finite_stabilization ∧
    -- a finite source for exact capacity: the infinite fiber
    type_of% @finiteness_is_required_for_exact_capacity ∧
    -- certificate existence for a finite capacity
    type_of% @certificate_existence_is_required ∧
    -- the three hypotheses of definition unification
    type_of% @DefinitionUnification.observerSeesDimension_is_required ∧
    type_of% @DefinitionUnification.complete_is_required ∧
    type_of% @DefinitionUnification.sound_is_required ∧
    -- unique normal forms for confluence of a terminating relation: the fork
    type_of% @ConfluenceTransport.uniqueness_is_required_for_confluence ∧
    -- the denotational subgrammar premise of the grammar boundary
    type_of% @DirectGrammarBoundary.denotational_subgrammar_premise_necessary ∧
    -- every target for the Blackwell order: one target leaves refinement open
    type_of% @BlackwellOrder.single_target_does_not_determine_refinement ∧
    -- deterministic observation for sufficiency as licensing: the fully noisy model
    type_of% @SufficiencyInstance.fullyNoisyBinary_sufficient_not_licensedOnJointSupport ∧
    -- a nonempty verdict type for the Padoa criterion
    type_of% @LicenseStabilizer.padoa_nonempty_verdict_is_required ∧
    -- the support in the zero-entropy case: a collision on a zero-mass state
    type_of% @FiberEntropy.zeroMass_collision_conditionalEntropy_eq_zero :=
  ⟨DirectGrammarBoundary.emptyWorldTarget_factorsThrough,
    DirectGrammarBoundary.emptyWorldTarget_not_verdictDeterminedBy,
    NormalFormFaithfulTransport.normalForm_injectivity_is_required,
    NormalFormFaithfulTransport.stutter_descent_is_required_for_termination_transport,
    Confusability.threePair_stagewise_two_symbols,
    Confusability.threePair_no_common_two_symbols,
    Confusability.threePair_not_coarsening,
    RelationalRecovery.pairwiseFiberCompatible_not_sufficient,
    RelationalRecovery.boolIdentity_directRelationalRecovery,
    RelationalRecovery.boolIdentity_falseOnlyLanguage_fails,
    NoisyRecovery.zeroMassCollision_support_pure,
    NoisyRecovery.zeroMassCollision_not_fullCarrier,
    CostComparison.zero_payload_never_strict,
    JointTargetCapacity.duplicated_target_product_bound_not_tight,
    compatibility_is_required_for_finite_stabilization,
    finiteness_is_required_for_exact_capacity,
    certificate_existence_is_required,
    DefinitionUnification.observerSeesDimension_is_required,
    DefinitionUnification.complete_is_required,
    DefinitionUnification.sound_is_required,
    ConfluenceTransport.uniqueness_is_required_for_confluence,
    DirectGrammarBoundary.denotational_subgrammar_premise_necessary,
    BlackwellOrder.single_target_does_not_determine_refinement,
    SufficiencyInstance.fullyNoisyBinary_sufficient_not_licensedOnJointSupport,
    LicenseStabilizer.padoa_nonempty_verdict_is_required,
    FiberEntropy.zeroMass_collision_conditionalEntropy_eq_zero⟩

end OperatorKO7.Meta.OperationalInexpressibility.HypothesisNecessityCatalog
