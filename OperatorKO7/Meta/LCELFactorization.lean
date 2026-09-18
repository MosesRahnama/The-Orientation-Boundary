import OperatorKO7.Meta.OperationalInexpressibility.ObserverKernel
import OperatorKO7.Meta.DependencyPairs_Works

set_option autoImplicit false

/-!
# Extensional boundary factorization and projection irreversibility

The boundary predicate is exactly failure to factor through an observer.  The
factorization theorem is an extensional `iff`, and the quotient map and its
unique factor are inherited from the actual observer-kernel quotient.

The second half records the equations a section must satisfy and proves that a
nontrivial kernel forbids a left inverse.  Thus a projection can split on its
codomain while remaining irreversible on its source.
-/

namespace OperatorKO7.Meta.LCELFactorization

open OperatorKO7.Meta.OperationalInexpressibility.ObserverKernel
open OperatorKO7
open OperatorKO7.Trace
open OperatorKO7.CompositionalImpossibility
open OperatorKO7.MetaDependencyPairs

universe u v w uS uM uR uI

/-- Boundary as failure of extensional factorization through the observer. -/
def Boundary {X : Type u} {Y : Type v} {Z : Type w}
    (observe : X -> Y) (target : X -> Z) : Prop :=
  ¬ FactorsThrough observe target

/-- Extensional factorization is precisely fiber constancy. -/
theorem factorsThrough_iff_fiberConstant
    {X : Type u} {Y : Type v} {Z : Type w}
    (observe : X -> Y) (target : X -> Z) :
    FactorsThrough observe target ↔
      ∀ {x y}, observe x = observe y -> target x = target y :=
  Iff.rfl

/-- The boundary form of the same extensional theorem. -/
theorem boundary_iff_not_fiberConstant
    {X : Type u} {Y : Type v} {Z : Type w}
    (observe : X -> Y) (target : X -> Z) :
    Boundary observe target ↔
      ¬ (∀ {x y}, observe x = observe y -> target x = target y) :=
  Iff.rfl

/-- A split projection with its right-inverse equation.  A left-inverse
equation is a separate property and is not silently included. -/
structure SplitProjection (X : Type u) (Y : Type v) where
  project : X -> Y
  rightInverseMap : Y -> X
  right_inverse : ∀ y, project (rightInverseMap y) = y

/-- A left inverse would recover every source value. -/
def HasLeftInverse {X : Type u} {Y : Type v}
    (project : X -> Y) : Prop :=
  ∃ recover : Y -> X, ∀ x, recover (project x) = x

/-- A nontrivial kernel forbids every left inverse. -/
theorem no_leftInverse_of_nontrivial_kernel
    {X : Type u} {Y : Type v}
    (project : X -> Y) {x1 x2 : X}
    (distinct : x1 ≠ x2) (collapsed : project x1 = project x2) :
    ¬ HasLeftInverse project := by
  rintro ⟨recover, hleft⟩
  apply distinct
  calc
    x1 = recover (project x1) := (hleft x1).symm
    _ = recover (project x2) := congrArg recover collapsed
    _ = x2 := hleft x2

/-- A split projection with a nontrivial kernel is right-invertible but not
left-invertible. -/
theorem splitProjection_irreversible_of_nontrivial_kernel
    {X : Type u} {Y : Type v}
    (P : SplitProjection X Y) {x1 x2 : X}
    (distinct : x1 ≠ x2) (collapsed : P.project x1 = P.project x2) :
    (∀ y, P.project (P.rightInverseMap y) = y) ∧
      ¬ HasLeftInverse P.project :=
  ⟨P.right_inverse,
    no_leftInverse_of_nontrivial_kernel P.project distinct collapsed⟩

/-- Concrete split projection: forget the second Boolean coordinate. -/
def boolFirstProjection : SplitProjection (Bool × Bool) Bool where
  project := Prod.fst
  rightInverseMap := fun b => (b, false)
  right_inverse := fun _ => rfl

/-- The concrete projection has a nontrivial kernel. -/
theorem boolFirstProjection_kernel_nontrivial :
    boolFirstProjection.project (false, false) =
      boolFirstProjection.project (false, true) ∧
    (false, false) ≠ (false, true) := by
  constructor
  · rfl
  · intro h
    cases h

/-- Concrete right-invertible but irreversible fixture. -/
theorem boolFirstProjection_is_split_but_not_leftInvertible :
    (∀ y,
      boolFirstProjection.project (boolFirstProjection.rightInverseMap y) = y) ∧
      ¬ HasLeftInverse boolFirstProjection.project :=
  splitProjection_irreversible_of_nontrivial_kernel boolFirstProjection
    boolFirstProjection_kernel_nontrivial.2
    boolFirstProjection_kernel_nontrivial.1

/-! ## Sound boundary inclusion under a named reversible-coordinate factorization -/

/-- Semantic data for the repaired LCEL boundary-factorization statement.
`piRev` is the content visible to base derivations; `piIrr` is the independently
varying coordinate whose sensitivity may witness the boundary. -/
structure FactorizationBoundaryModel
    (Sentence : Type uS) (Model : Type uM)
    (Rev : Type uR) (Irr : Type uI) where
  reference : Model
  piRev : Model -> Rev
  piIrr : Model -> Irr
  trueIn : Model -> Sentence -> Prop
  provesBase : Sentence -> Prop

/-- A statement is reference-true and sensitive to the irreversible coordinate
when a comparison model agrees on `piRev`, differs on `piIrr`, and falsifies it. -/
def PiIrrSensitiveAtReference
    {Sentence : Type uS} {Model : Type uM}
    {Rev : Type uR} {Irr : Type uI}
    (D : FactorizationBoundaryModel Sentence Model Rev Irr)
    (psi : Sentence) : Prop :=
  D.trueIn D.reference psi ∧
    ∃ alternate : Model,
      D.piRev alternate = D.piRev D.reference ∧
        D.piIrr alternate ≠ D.piIrr D.reference ∧
          ¬ D.trueIn alternate psi

/-- Boundary-admissible statements are true in the reference model but have no
base derivation. -/
def BoundaryAdmissible
    {Sentence : Type uS} {Model : Type uM}
    {Rev : Type uR} {Irr : Type uI}
    (D : FactorizationBoundaryModel Sentence Model Rev Irr)
    (psi : Sentence) : Prop :=
  D.trueIn D.reference psi ∧ ¬ D.provesBase psi

/-- Named sensitivity restriction: the truth of every base-derived statement
factors through reversible-coordinate content. -/
structure BaseDerivationsFactorThroughRev
    {Sentence : Type uS} {Model : Type uM}
    {Rev : Type uR} {Irr : Type uI}
    (D : FactorizationBoundaryModel Sentence Model Rev Irr) where
  factorizedTruth : Sentence -> Rev -> Prop
  factorization : ∀ psi, D.provesBase psi -> ∀ model,
    D.trueIn model psi ↔ factorizedTruth psi (D.piRev model)

/-- Sound inclusion: a reference-true statement that changes only with the
irreversible coordinate cannot be derived by a base layer whose derived truth
factors through `piRev`. -/
theorem piIrrSensitive_underivable_of_baseFactorization
    {Sentence : Type uS} {Model : Type uM}
    {Rev : Type uR} {Irr : Type uI}
    {D : FactorizationBoundaryModel Sentence Model Rev Irr}
    (F : BaseDerivationsFactorThroughRev D)
    {psi : Sentence}
    (hsensitive : PiIrrSensitiveAtReference D psi) :
    ¬ D.provesBase psi := by
  intro hbase
  rcases hsensitive with ⟨href, alternate, hrev, _, halt⟩
  have hrefFactor :
      F.factorizedTruth psi (D.piRev D.reference) :=
    (F.factorization psi hbase D.reference).1 href
  have haltFactor :
      F.factorizedTruth psi (D.piRev alternate) := by
    rw [hrev]
    exact hrefFactor
  exact halt ((F.factorization psi hbase alternate).2 haltFactor)

/-- The manuscript-safe inclusion from `piIrr` sensitivity into the admissible
boundary. -/
theorem piIrrSensitive_implies_boundaryAdmissible
    {Sentence : Type uS} {Model : Type uM}
    {Rev : Type uR} {Irr : Type uI}
    {D : FactorizationBoundaryModel Sentence Model Rev Irr}
    (F : BaseDerivationsFactorThroughRev D)
    {psi : Sentence}
    (hsensitive : PiIrrSensitiveAtReference D psi) :
    BoundaryAdmissible D psi :=
  ⟨hsensitive.1,
    piIrrSensitive_underivable_of_baseFactorization F hsensitive⟩

/-- Additional completeness needed for equality rather than only the sound
inclusion.  This hypothesis is per-instance and remains visible in the type. -/
structure ExtensionalFactorization
    {Sentence : Type uS} {Model : Type uM}
    {Rev : Type uR} {Irr : Type uI}
    (D : FactorizationBoundaryModel Sentence Model Rev Irr) where
  baseFactorization : BaseDerivationsFactorThroughRev D
  boundary_complete : ∀ psi,
    BoundaryAdmissible D psi -> PiIrrSensitiveAtReference D psi

/-- Set equality is available exactly under the named extensional-completeness
hypothesis. -/
theorem boundaryAdmissible_set_eq_piIrrSensitive_set
    {Sentence : Type uS} {Model : Type uM}
    {Rev : Type uR} {Irr : Type uI}
    {D : FactorizationBoundaryModel Sentence Model Rev Irr}
    (E : ExtensionalFactorization D) :
    {psi : Sentence | BoundaryAdmissible D psi} =
      {psi : Sentence | PiIrrSensitiveAtReference D psi} := by
  ext psi
  constructor
  · exact E.boundary_complete psi
  · exact piIrrSensitive_implies_boundaryAdmissible E.baseFactorization

/-! ### Non-vacuous two-coordinate, two-sentence fixture -/

/-- The fixture language distinguishes a reversible-coordinate statement from
an irreversible-coordinate statement. -/
inductive BoolFactorizationSentence where
  | reversibleTrue
  | irreversibleTrue
  deriving DecidableEq, Fintype, Repr

/-- A Boolean model in which the first coordinate is reversible content and
the second is invisible to base derivations.  The base language genuinely
derives `reversibleTrue`; it does not derive `irreversibleTrue`. -/
def boolFactorizationBoundaryModel :
    FactorizationBoundaryModel BoolFactorizationSentence
      (Bool × Bool) Bool Bool where
  reference := (true, true)
  piRev := Prod.fst
  piIrr := Prod.snd
  trueIn := fun model psi =>
    match psi with
    | .reversibleTrue => model.1 = true
    | .irreversibleTrue => model.2 = true
  provesBase := fun psi => psi = .reversibleTrue

/-- The base derivation judgment is genuinely inhabited. -/
theorem boolBaseDerivation_nonempty :
    ∃ psi, boolFactorizationBoundaryModel.provesBase psi :=
  ⟨.reversibleTrue, rfl⟩

/-- The irreversible-coordinate sentence is genuinely outside the base
derivation judgment. -/
theorem boolIrreversible_not_provesBase :
    ¬ boolFactorizationBoundaryModel.provesBase
      .irreversibleTrue := by
  intro h
  cases h

/-- Truth of every actually base-derived sentence factors through `piRev`. -/
def boolBaseDerivationsFactorThroughRev :
    BaseDerivationsFactorThroughRev boolFactorizationBoundaryModel where
  factorizedTruth := fun psi rev =>
    match psi with
    | .reversibleTrue => rev = true
    | .irreversibleTrue => False
  factorization := by
    intro psi hbase model
    cases psi with
    | reversibleTrue => rfl
    | irreversibleTrue => exact False.elim (boolIrreversible_not_provesBase hbase)

/-- The non-base fixture statement is genuinely sensitive to `piIrr`. -/
theorem boolIrreversible_piIrrSensitive :
    PiIrrSensitiveAtReference boolFactorizationBoundaryModel
      .irreversibleTrue := by
  refine ⟨rfl, (true, false), rfl, ?_, ?_⟩
  · intro h
    cases h
  · intro h
    cases h

/-- The equality hypothesis is inhabited without making base derivability
empty: its reversible sentence is derived and its irreversible sentence is the
boundary witness. -/
def boolExtensionalFactorization :
    ExtensionalFactorization boolFactorizationBoundaryModel where
  baseFactorization := boolBaseDerivationsFactorThroughRev
  boundary_complete := by
    intro psi hboundary
    cases psi with
    | reversibleTrue =>
        exact False.elim (hboundary.2 rfl)
    | irreversibleTrue =>
        exact boolIrreversible_piIrrSensitive

/-! ## Concrete KO7 dependency-pair factorization model

The finite Boolean fixture above proves that the abstract interfaces are
inhabited.  The declarations below realize the same interfaces on actual KO7
`Trace` terms.  The reversible coordinate is the dependency-pair counter
projection `dpRank`; the irreversible coordinate is the multiplicity of the
schema wrapper `app` in the full term.  The sentence language is deliberately
the exact two-observation language needed for the factorization theorem.  Its
extensional-completeness result must not be generalized beyond that enumerated
language.
-/

/-- Multiplicity of the KO7 schema wrapper `app` in a full trace.  Other
constructors transport the multiplicities of their children without adding a
wrapper occurrence. -/
def ko7WrapperMultiplicity : Trace → Nat
  | .void => 0
  | .delta t => ko7WrapperMultiplicity t
  | .integrate t => ko7WrapperMultiplicity t
  | .merge left right =>
      ko7WrapperMultiplicity left + ko7WrapperMultiplicity right
  | .app left right =>
      ko7WrapperMultiplicity left + ko7WrapperMultiplicity right + 1
  | .recΔ base step counter =>
      ko7WrapperMultiplicity base + ko7WrapperMultiplicity step +
        ko7WrapperMultiplicity counter
  | .eqW left right =>
      ko7WrapperMultiplicity left + ko7WrapperMultiplicity right

/-- The actual `R_rec_succ` target deposits one outer wrapper in addition to
the copied wrapper content of the step argument. -/
theorem ko7WrapperMultiplicity_rec_succ_deposit
    (base step counter : Trace) :
    ko7WrapperMultiplicity (app step (recΔ base step counter)) =
      ko7WrapperMultiplicity (recΔ base step (delta counter)) +
        ko7WrapperMultiplicity step + 1 := by
  simp only [ko7WrapperMultiplicity]
  omega

/-- The actual source rewrite therefore strictly increases the irreversible
wrapper coordinate. -/
theorem ko7WrapperMultiplicity_rec_succ_strictly_increases
    (base step counter : Trace) :
    ko7WrapperMultiplicity (recΔ base step (delta counter)) <
      ko7WrapperMultiplicity (app step (recΔ base step counter)) := by
  rw [ko7WrapperMultiplicity_rec_succ_deposit]
  omega

/-- Exact two-sentence language for the concrete DP factorization model. -/
inductive KO7DPFactorizationSentence where
  | counterPositive
  | wrapperMultiplicityEven
  deriving DecidableEq, Fintype, Repr

/-- Reference trace: a one-successor recursive call with no `app` wrapper. -/
def ko7DPFactorizationReference : Trace :=
  recΔ void void (delta void)

/-- Same dependency-pair counter as the reference, with one wrapper inserted
in the base argument.  This is the concrete irreversible-coordinate
comparison point. -/
def ko7DPFactorizationAlternate : Trace :=
  recΔ (app void void) void (delta void)

/-- Concrete KO7 DP boundary model.  `piRev` is exactly the DP counter rank;
`piIrr` is exactly full-term wrapper multiplicity.  The base derives only the
counter sentence. -/
def ko7DPFactorizationBoundaryModel :
    FactorizationBoundaryModel KO7DPFactorizationSentence
      Trace Nat Nat where
  reference := ko7DPFactorizationReference
  piRev := dpRank
  piIrr := ko7WrapperMultiplicity
  trueIn := fun model sentence =>
    match sentence with
    | .counterPositive => 0 < dpRank model
    | .wrapperMultiplicityEven => ko7WrapperMultiplicity model % 2 = 0
  provesBase := fun sentence => sentence = .counterPositive

/-- The reversible projection in the concrete model is definitionally the
actual dependency-pair counter rank. -/
theorem ko7DPFactorization_piRev_eq_dpRank (model : Trace) :
    ko7DPFactorizationBoundaryModel.piRev model = dpRank model :=
  rfl

/-- The irreversible projection in the concrete model is definitionally the
actual wrapper-multiplicity observable. -/
theorem ko7DPFactorization_piIrr_eq_wrapperMultiplicity (model : Trace) :
    ko7DPFactorizationBoundaryModel.piIrr model =
      ko7WrapperMultiplicity model :=
  rfl

/-- The manually extracted KO7 pair relation is inhabited. -/
theorem ko7DPPair_nonempty :
    ∃ source target, DPPair source target :=
  ⟨recΔ void void (delta void), recΔ void void void,
    DPPair.rec_succ void void void⟩

/-- Along every extracted dependency-pair edge, the concrete reversible
coordinate strictly decreases. -/
theorem ko7DPFactorization_piRev_decreases_on_pair
    {source target : Trace} (hPair : DPPair source target) :
    ko7DPFactorizationBoundaryModel.piRev target <
      ko7DPFactorizationBoundaryModel.piRev source :=
  dpPair_decreases hPair

/-- The extracted dependency-pair edge preserves wrapper multiplicity: the
actual source rewrite's wrapper deposit lies outside the pair target. -/
theorem ko7DPFactorization_piIrr_preserved_on_pair
    {source target : Trace} (hPair : DPPair source target) :
    ko7DPFactorizationBoundaryModel.piIrr target =
      ko7DPFactorizationBoundaryModel.piIrr source := by
  cases hPair with
  | rec_succ base step counter =>
      rfl

/-- One theorem displays the factorization mechanism on the actual KO7 rule:
the pair rank decreases, while the source rewrite deposits the wrapper content
that the pair target omits. -/
theorem ko7DP_pair_counter_descent_and_source_wrapper_deposit
    (base step counter : Trace) :
    DPPair (recΔ base step (delta counter)) (recΔ base step counter) ∧
      Step (recΔ base step (delta counter))
        (app step (recΔ base step counter)) ∧
      ko7DPFactorizationBoundaryModel.piRev (recΔ base step counter) <
        ko7DPFactorizationBoundaryModel.piRev
          (recΔ base step (delta counter)) ∧
      ko7DPFactorizationBoundaryModel.piIrr
          (app step (recΔ base step counter)) =
        ko7DPFactorizationBoundaryModel.piIrr
            (recΔ base step (delta counter)) +
          ko7DPFactorizationBoundaryModel.piIrr step + 1 := by
  have hPair :
      DPPair (recΔ base step (delta counter)) (recΔ base step counter) :=
    DPPair.rec_succ base step counter
  exact ⟨hPair, Step.R_rec_succ base step counter,
    ko7DPFactorization_piRev_decreases_on_pair hPair,
    ko7WrapperMultiplicity_rec_succ_deposit base step counter⟩

/-- The concrete base derivation judgment is genuinely inhabited. -/
theorem ko7DPBaseDerivation_nonempty :
    ∃ sentence, ko7DPFactorizationBoundaryModel.provesBase sentence :=
  ⟨.counterPositive, rfl⟩

/-- The wrapper-multiplicity sentence is genuinely absent from the base
derivation judgment. -/
theorem ko7DPWrapperMultiplicityEven_not_provesBase :
    ¬ ko7DPFactorizationBoundaryModel.provesBase
      .wrapperMultiplicityEven := by
  intro h
  cases h

/-- Truth of every actually base-derived sentence in the concrete DP model
factors through the counter projection `piRev = dpRank`. -/
def ko7DPBaseDerivationsFactorThroughRev :
    BaseDerivationsFactorThroughRev ko7DPFactorizationBoundaryModel where
  factorizedTruth := fun sentence counter =>
    match sentence with
    | .counterPositive => 0 < counter
    | .wrapperMultiplicityEven => False
  factorization := by
    intro sentence hBase model
    cases sentence with
    | counterPositive =>
        rfl
    | wrapperMultiplicityEven =>
        exact False.elim
          (ko7DPWrapperMultiplicityEven_not_provesBase hBase)

/-- The reference and alternate traces agree on the actual DP counter and
disagree on actual wrapper multiplicity. -/
theorem ko7DPFactorization_reference_alternate_coordinates :
    ko7DPFactorizationBoundaryModel.piRev ko7DPFactorizationAlternate =
        ko7DPFactorizationBoundaryModel.piRev ko7DPFactorizationReference ∧
      ko7DPFactorizationBoundaryModel.piIrr ko7DPFactorizationAlternate ≠
        ko7DPFactorizationBoundaryModel.piIrr ko7DPFactorizationReference := by
  constructor
  · rfl
  · decide

/-- The actual dependency-pair counter projection does not determine full-term
wrapper multiplicity.  This is the concrete no-transport obstruction behind
the restriction to a named sentence language. -/
theorem ko7_dpRank_does_not_determine_wrapperMultiplicity :
    Boundary dpRank ko7WrapperMultiplicity := by
  intro hFactors
  exact ko7DPFactorization_reference_alternate_coordinates.2
    (hFactors ko7DPFactorization_reference_alternate_coordinates.1)

/-- Even the Boolean wrapper-parity observable does not factor through the
actual dependency-pair counter projection. -/
theorem ko7_dpRank_does_not_determine_wrapperParity :
    Boundary dpRank (fun model => ko7WrapperMultiplicity model % 2) := by
  intro hFactors
  have hParity := hFactors
    ko7DPFactorization_reference_alternate_coordinates.1
  change (1 : Nat) % 2 = (0 : Nat) % 2 at hParity
  omega

/-- Since two distinct traces have the same actual DP counter, no map from the
counter value can recover every source trace. -/
theorem ko7_dpRank_has_no_trace_leftInverse :
    ¬ HasLeftInverse dpRank := by
  exact no_leftInverse_of_nontrivial_kernel dpRank
    (x1 := ko7DPFactorizationAlternate)
    (x2 := ko7DPFactorizationReference)
    (by decide)
    ko7DPFactorization_reference_alternate_coordinates.1

/-- Concrete irreversible-sensitive witness: wrapper parity is true at the
reference, false at a trace with the same DP counter and one additional
wrapper. -/
theorem ko7DPWrapperMultiplicityEven_piIrrSensitive :
    PiIrrSensitiveAtReference ko7DPFactorizationBoundaryModel
      .wrapperMultiplicityEven := by
  refine ⟨?_, ko7DPFactorizationAlternate, ?_, ?_, ?_⟩
  · change (0 : Nat) % 2 = 0
    decide
  · change (1 : Nat) = 1
    rfl
  · change (1 : Nat) ≠ 0
    decide
  · change ¬ ((1 : Nat) % 2 = 0)
    decide

/-- Specialized sound inclusion: the wrapper-sensitive sentence is a genuine
boundary-admissible statement in the concrete DP model. -/
theorem ko7DPWrapperMultiplicityEven_boundaryAdmissible :
    BoundaryAdmissible ko7DPFactorizationBoundaryModel
      .wrapperMultiplicityEven :=
  piIrrSensitive_implies_boundaryAdmissible
    ko7DPBaseDerivationsFactorThroughRev
    ko7DPWrapperMultiplicityEven_piIrrSensitive

/-- In the exact two-sentence concrete DP language, the named extensional
factorization hypothesis is honestly inhabited.  This is not a completeness
claim for arbitrary KO7 predicates or arbitrary dependency-pair processors. -/
def ko7DPExtensionalFactorization :
    ExtensionalFactorization ko7DPFactorizationBoundaryModel where
  baseFactorization := ko7DPBaseDerivationsFactorThroughRev
  boundary_complete := by
    intro sentence hBoundary
    cases sentence with
    | counterPositive =>
        exact False.elim (hBoundary.2 rfl)
    | wrapperMultiplicityEven =>
        exact ko7DPWrapperMultiplicityEven_piIrrSensitive

/-- Specialized set equality for the exact two-sentence concrete DP model.
The extensional hypothesis is supplied by `ko7DPExtensionalFactorization` and
its scope remains this finite sentence language. -/
theorem ko7DP_boundaryAdmissible_set_eq_piIrrSensitive_set :
    {sentence : KO7DPFactorizationSentence |
        BoundaryAdmissible ko7DPFactorizationBoundaryModel sentence} =
      {sentence : KO7DPFactorizationSentence |
        PiIrrSensitiveAtReference ko7DPFactorizationBoundaryModel sentence} :=
  boundaryAdmissible_set_eq_piIrrSensitive_set
    ko7DPExtensionalFactorization

section AuditChecks

#check @Boundary
#check @factorsThrough_iff_fiberConstant
#check @boundary_iff_not_fiberConstant
#check @SplitProjection
#check @no_leftInverse_of_nontrivial_kernel
#check @splitProjection_irreversible_of_nontrivial_kernel
#check @boolFirstProjection_is_split_but_not_leftInvertible
#check @FactorizationBoundaryModel
#check @PiIrrSensitiveAtReference
#check @BoundaryAdmissible
#check @BaseDerivationsFactorThroughRev
#check @piIrrSensitive_underivable_of_baseFactorization
#check @piIrrSensitive_implies_boundaryAdmissible
#check @ExtensionalFactorization
#check @boundaryAdmissible_set_eq_piIrrSensitive_set
#check @boolBaseDerivation_nonempty
#check @boolIrreversible_piIrrSensitive
#check @boolExtensionalFactorization
#check @ko7WrapperMultiplicity_rec_succ_deposit
#check @ko7WrapperMultiplicity_rec_succ_strictly_increases
#check @ko7DPFactorizationBoundaryModel
#check @ko7DPFactorization_piRev_eq_dpRank
#check @ko7DPFactorization_piIrr_eq_wrapperMultiplicity
#check @ko7DPPair_nonempty
#check @ko7DPFactorization_piRev_decreases_on_pair
#check @ko7DPFactorization_piIrr_preserved_on_pair
#check @ko7DP_pair_counter_descent_and_source_wrapper_deposit
#check @ko7DPBaseDerivation_nonempty
#check @ko7DPWrapperMultiplicityEven_not_provesBase
#check @ko7DPBaseDerivationsFactorThroughRev
#check @ko7DPFactorization_reference_alternate_coordinates
#check @ko7_dpRank_does_not_determine_wrapperMultiplicity
#check @ko7_dpRank_does_not_determine_wrapperParity
#check @ko7_dpRank_has_no_trace_leftInverse
#check @ko7DPWrapperMultiplicityEven_piIrrSensitive
#check @ko7DPWrapperMultiplicityEven_boundaryAdmissible
#check @ko7DPExtensionalFactorization
#check @ko7DP_boundaryAdmissible_set_eq_piIrrSensitive_set

#print axioms factorsThrough_iff_fiberConstant
#print axioms boundary_iff_not_fiberConstant
#print axioms no_leftInverse_of_nontrivial_kernel
#print axioms splitProjection_irreversible_of_nontrivial_kernel
#print axioms boolFirstProjection_is_split_but_not_leftInvertible
#print axioms piIrrSensitive_underivable_of_baseFactorization
#print axioms piIrrSensitive_implies_boundaryAdmissible
#print axioms boundaryAdmissible_set_eq_piIrrSensitive_set
#print axioms boolBaseDerivation_nonempty
#print axioms boolIrreversible_piIrrSensitive
#print axioms ko7WrapperMultiplicity_rec_succ_deposit
#print axioms ko7WrapperMultiplicity_rec_succ_strictly_increases
#print axioms ko7DPPair_nonempty
#print axioms ko7DPFactorization_piRev_decreases_on_pair
#print axioms ko7DPFactorization_piIrr_preserved_on_pair
#print axioms ko7DP_pair_counter_descent_and_source_wrapper_deposit
#print axioms ko7DPBaseDerivation_nonempty
#print axioms ko7DPWrapperMultiplicityEven_not_provesBase
#print axioms ko7DPBaseDerivationsFactorThroughRev
#print axioms ko7DPFactorization_reference_alternate_coordinates
#print axioms ko7_dpRank_does_not_determine_wrapperMultiplicity
#print axioms ko7_dpRank_does_not_determine_wrapperParity
#print axioms ko7_dpRank_has_no_trace_leftInverse
#print axioms ko7DPWrapperMultiplicityEven_piIrrSensitive
#print axioms ko7DPWrapperMultiplicityEven_boundaryAdmissible
#print axioms ko7DPExtensionalFactorization
#print axioms ko7DP_boundaryAdmissible_set_eq_piIrrSensitive_set

end AuditChecks

end OperatorKO7.Meta.LCELFactorization
