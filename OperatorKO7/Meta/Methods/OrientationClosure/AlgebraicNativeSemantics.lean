import OperatorKO7.Meta.Methods.AlgebraicInterpretationRows
import OperatorKO7.Meta.Methods.OrderedMatrixInterpretationRows
import OperatorKO7.Meta.HigherOrderRewriting_Syntax

/-!
# Native algebraic semantics for ORI-2

This file adds concrete inhabitants and method data for the algebraic rows that
were previously represented only by row propositions. The existing universal
barriers remain the classification theorems. The constructions here provide
method-specific data and controls.
-/

set_option autoImplicit false

namespace OperatorKO7.Methods.OrientationClosure.AlgebraicNativeSemantics

open OperatorKO7.StepDuplicating
open OperatorKO7.StepDuplicating.StepDuplicatingSchema
open OperatorKO7.Methods.AlgebraicInterpretationRows
open OperatorKO7.Methods.OrderedMatrixInterpretationRows
open OperatorKO7.HigherOrderRewritingSyntax

/-! ## Truncated negative-constant polynomial -/

/-- A constructor-local evaluation with a genuine subtractive wrapper
constant. The wrapper computes `x + y - 1`, so the method exercises the
truncation semantics instead of merely naming a negative-coefficient class. -/
def truncatedDebtEval : FreeTerm -> Nat
  | .base => 1
  | .succ t => 2 + truncatedDebtEval t
  | .wrap x y => truncatedDebtEval x + truncatedDebtEval y - 1
  | .recur b s n => 1 + truncatedDebtEval b + truncatedDebtEval s + truncatedDebtEval n

/-- Concrete truncated affine method with an active debt of one. -/
def truncatedDebtMethod : TruncatedAffineMeasure freeSchema where
  eval := truncatedDebtEval
  wrapDebt := 1
  wrapLeft := 1
  wrapRight := 1
  succGain := 2
  eval_wrap := by
    intro x y
    simp [freeSchema, truncatedDebtEval]
  succ_strict := by
    intro t
    simp [freeSchema, truncatedDebtEval]
  h_wrap_left_pos := by decide
  h_wrap_right_pos := by decide
  counter_gain := by
    intro b s n
    simp [freeSchema, truncatedDebtEval]
    omega

/-- The subtractive constant changes an actual evaluation. -/
theorem truncatedDebtMethod_debt_active :
    truncatedDebtMethod.eval (.wrap .base .base) <
      truncatedDebtMethod.eval .base + truncatedDebtMethod.eval .base := by
  decide

/-- The concrete negative-constant method is blocked by the row theorem. -/
theorem truncatedDebtMethod_no_dup_orientation :
    Not (forall b s n : FreeTerm,
      truncatedDebtMethod.eval (freeSchema.wrap s (freeSchema.recur b s n)) <
        truncatedDebtMethod.eval (freeSchema.recur b s (freeSchema.succ n))) :=
  negativeCoefficientPolynomial_row_anchor freeSchema truncatedDebtMethod

/-! ## Native max interpretation -/

/-- A max-plus evaluation whose right wrapper branch receives the required
positive offset. -/
def maxNativeEval : FreeTerm -> Nat
  | .base => 0
  | .succ t => 1 + maxNativeEval t
  | .wrap x y => max (maxNativeEval x) (1 + maxNativeEval y)
  | .recur b s n => max (maxNativeEval b) (max (maxNativeEval s) (maxNativeEval n))

/-- Concrete max method on the free duplicating schema. -/
def maxNativeMethod : MaxMeasure freeSchema where
  eval := maxNativeEval
  c_base := 0
  succ_const := 1
  wrap_const := 0
  wrap_left := 0
  wrap_right := 1
  recur_const := 0
  recur_base := 0
  recur_step := 0
  recur_counter := 0
  eval_base := rfl
  eval_succ := by intro t; rfl
  eval_wrap := by intro x y; simp [freeSchema, maxNativeEval]
  eval_recur := by intro b s n; simp [freeSchema, maxNativeEval]
  h_wrap_right_pos := by decide

/-- The max method has a nonconstant successor branch. -/
theorem maxNativeMethod_nonconstant :
    maxNativeMethod.eval .base < maxNativeMethod.eval (.succ .base) := by decide

/-- The concrete max method is blocked from uniform duplicator orientation. -/
theorem maxNativeMethod_no_dup_orientation :
    Not (forall b s n : FreeTerm,
      maxNativeMethod.eval (freeSchema.wrap s (freeSchema.recur b s n)) <
        maxNativeMethod.eval (freeSchema.recur b s (freeSchema.succ n))) :=
  no_max_orients_dup_step_of_succ_pump maxNativeMethod (by decide)

/-! ## Bounded polynomial and multilinear witnesses -/

/-- Linear constructor size as an inhabited member of the bounded polynomial
class. The nonlinear table is empty, which supplies an inside-the-contract
method while the existing cross-coupled method supplies the outside control. -/
def unitBoundedPolynomial : BoundedPolynomialMeasure freeSchema where
  eval := unitAffineNatEval
  c_base := 1
  succ_bias := 1
  succ_scale := 1
  wrap_const := 1
  wrap_left := 1
  wrap_right := 1
  recur_const := 1
  recur_base := 1
  recur_step := 1
  recur_counter := 1
  monomials := []
  eval_base := rfl
  eval_succ := by intro t; simp [freeSchema, unitAffineNatEval]
  eval_wrap := by intro x y; simp [freeSchema, unitAffineNatEval]
  eval_recur := by intro b s n; simp [freeSchema, unitAffineNatEval]
  h_wrap_left_pos := by decide
  h_wrap_right_pos := by decide

/-- The concrete polynomial table has no counter exponent. -/
theorem unitBoundedPolynomial_noCounterExponent :
    NoCounterExponent unitBoundedPolynomial := by
  intro m hm
  simp [unitBoundedPolynomial] at hm

/-- Its dominance law is derived from the table, rather than stored as a
classification field. -/
theorem unitBoundedPolynomial_dominated :
    EventuallyDominatedAtBase unitBoundedPolynomial :=
  eventuallyDominatedAtBase_of_no_counter_exponent
    unitBoundedPolynomial unitBoundedPolynomial_noCounterExponent

/-- Native two-sided witness for the higher-degree polynomial boundary. -/
structure PolynomialBoundaryWitness where
  inside : BoundedPolynomialMeasure freeSchema
  insideNoCounterExponent : NoCounterExponent inside
  outside : BoundedPolynomialMeasure freeSchema
  outsideViolatesDominance : Not (EventuallyDominatedAtBase outside)
  outsideOrients : forall b s n : FreeTerm,
    outside.eval (freeSchema.wrap s (freeSchema.recur b s n)) <
      outside.eval (freeSchema.recur b s (freeSchema.succ n))

/-- The boundary contains both an in-class method and the compiled
cross-coupled orienter outside the dominance subclass. -/
def polynomialBoundaryWitness : PolynomialBoundaryWitness where
  inside := unitBoundedPolynomial
  insideNoCounterExponent := unitBoundedPolynomial_noCounterExponent
  outside := crossCoupledPolynomial
  outsideViolatesDominance := crossCoupledPolynomial_not_eventuallyDominated
  outsideOrients := crossCoupledWeight_strictly_orients

/-- Empty multilinear table as an inhabited uncoupled method. -/
def unitBoundedMultilinear : BoundedMultilinearMeasure freeSchema where
  eval := unitAffineNatEval
  c_base := 1
  succ_bias := 1
  succ_scale := 1
  wrap_const := 1
  wrap_left := 1
  wrap_right := 1
  recur_const := 1
  recur_base := 1
  recur_step := 1
  recur_counter := 1
  monomials := []
  eval_base := rfl
  eval_succ := by intro t; simp [freeSchema, unitAffineNatEval]
  eval_wrap := by intro x y; simp [freeSchema, unitAffineNatEval]
  eval_recur := by intro b s n; simp [freeSchema, unitAffineNatEval]
  h_wrap_left_pos := by decide
  h_wrap_right_pos := by decide

/-- The concrete multilinear method contains no step-counter coupling. -/
theorem unitBoundedMultilinear_noCoupling :
    NoStepCounterCoupling unitBoundedMultilinear := by
  intro m hm
  simp [unitBoundedMultilinear] at hm

structure MultilinearBoundaryWitness where
  inside : BoundedMultilinearMeasure freeSchema
  insideNoCoupling : NoStepCounterCoupling inside
  outside : BoundedMultilinearMeasure freeSchema
  outsideViolatesDominance : Not (MultilinearDominatedAtBase outside)
  outsideOrients : forall b s n : FreeTerm,
    outside.eval (freeSchema.wrap s (freeSchema.recur b s n)) <
      outside.eval (freeSchema.recur b s (freeSchema.succ n))

/-- The multilinear boundary contains an uncoupled inhabitant and the existing
cross-coupled orienter. -/
def multilinearBoundaryWitness : MultilinearBoundaryWitness where
  inside := unitBoundedMultilinear
  insideNoCoupling := unitBoundedMultilinear_noCoupling
  outside := crossCoupledMultilinear
  outsideViolatesDominance := crossCoupledMultilinear_not_dominatedAtBase
  outsideOrients := crossCoupledWeight_strictly_orients

/-! ## Ordered-field matrix family -/

/-- One method object for each of the two advertised ordered fields. -/
structure OrderedFieldMatrixFamily where
  rational : OrderedMatrixMethod freeSchema 2 ℚ
  real : OrderedMatrixMethod freeSchema 2 ℝ
  rationalHasNonNatEntry :
    Not (∃ n : Nat, rational.interpretation.succ_mat.coeff 0 0 = (n : ℚ))
  realNonconstant : real.interpretation.eval .base ≠ real.interpretation.eval (.succ .base)

/-- The field-native family uses the `3/2` method in both fields. -/
noncomputable def orderedFieldMatrixFamily : OrderedFieldMatrixFamily where
  rational := fractionalMatrixMethod 2
  real := fractionalMatrixMethod 2
  rationalHasNonNatEntry := fractionalMatrixMethod_entry_not_nat 2
  realNonconstant := fractionalMatrixMethod_nonconstant 2

/-! ## Higher-order tuple interpretation -/

/-- Structural cost on the explicit higher-order syntax. -/
def hoTupleCost : HOTerm -> Nat
  | .var _ => 1
  | .atom => 1
  | .succ t => 1 + hoTupleCost t
  | .app f a => 1 + hoTupleCost f + hoTupleCost a
  | .lam _ body => 1 + hoTupleCost body
  | .recur b s n => 1 + hoTupleCost b + hoTupleCost s + hoTupleCost n
  | .share x y => 1 + hoTupleCost x + hoTupleCost y

/-- Binder count supplies a second component that is genuinely higher-order. -/
def hoBinderCount : HOTerm -> Nat
  | .var _ | .atom => 0
  | .succ t => hoBinderCount t
  | .app f a => hoBinderCount f + hoBinderCount a
  | .lam _ body => 1 + hoBinderCount body
  | .recur b s n => hoBinderCount b + hoBinderCount s + hoBinderCount n
  | .share x y => hoBinderCount x + hoBinderCount y

/-- Native tuple evaluation on higher-order terms. -/
def hoTupleEval (t : HOTerm) : Nat × Nat :=
  (hoTupleCost t, hoBinderCount t)

/-- First-order embedding into the explicit higher-order syntax. Wrapper is
represented by binary application. -/
def encodeFreeTermHO : FreeTerm -> HOTerm
  | .base => .atom
  | .succ t => .succ (encodeFreeTermHO t)
  | .wrap x y => .app (encodeFreeTermHO x) (encodeFreeTermHO y)
  | .recur b s n => .recur (encodeFreeTermHO b) (encodeFreeTermHO s) (encodeFreeTermHO n)

/-- The first tuple component agrees with the concrete affine first-order
interpretation on the embedded fragment. -/
theorem hoTupleCost_encodeFreeTermHO (t : FreeTerm) :
    hoTupleCost (encodeFreeTermHO t) = unitAffineNatEval t := by
  induction t with
  | base => rfl
  | succ t ih => simp [encodeFreeTermHO, hoTupleCost, unitAffineNatEval, ih]
  | wrap x y ihx ihy =>
      simp [encodeFreeTermHO, hoTupleCost, unitAffineNatEval, ihx, ihy]
  | recur b s n ihb ihs ihn =>
      simp [encodeFreeTermHO, hoTupleCost, unitAffineNatEval, ihb, ihs, ihn]

/-- Method data for the higher-order tuple row. -/
structure HigherOrderTupleMethod where
  eval : HOTerm -> Nat × Nat
  encode : FreeTerm -> HOTerm
  firstOrderCost : forall t,
    (eval (encode t)).1 = unitAffineNatEval t
  binderSensitive : (eval (.lam 0 .atom)).2 ≠ (eval .atom).2

/-- Concrete native higher-order tuple method. -/
def higherOrderTupleMethod : HigherOrderTupleMethod where
  eval := hoTupleEval
  encode := encodeFreeTermHO
  firstOrderCost := by
    intro t
    exact hoTupleCost_encodeFreeTermHO t
  binderSensitive := by decide

/-- Its embedded first-order restriction inherits the affine tuple barrier. -/
theorem higherOrderTupleMethod_no_dup_orientation :
    Not (forall b s n : FreeTerm,
      (higherOrderTupleMethod.eval
        (higherOrderTupleMethod.encode (freeSchema.wrap s (freeSchema.recur b s n)))).1 <
      (higherOrderTupleMethod.eval
        (higherOrderTupleMethod.encode (freeSchema.recur b s (freeSchema.succ n)))).1) := by
  intro h
  apply no_affine_orients_dup_step unitAffineNatMeasure
  intro b s n
  have h' := h b s n
  rw [higherOrderTupleMethod.firstOrderCost, higherOrderTupleMethod.firstOrderCost] at h'
  simpa [unitAffineNatMeasure] using h'

/-! ## Strict monotone Archimedean algebra -/

/-- Concrete natural-valued Archimedean algebra. -/
def unitArchimedeanAlgebra : ArchimedeanMonotoneAlgebra freeSchema where
  eval := unitAffineNatEval
  succ_strict := by
    intro t
    simp [freeSchema, unitAffineNatEval]
  wrap_dominates := by
    intro x y
    simp [freeSchema, unitAffineNatEval]
  counterGain := 1
  counter_gain := by
    intro b s n
    simp [freeSchema, unitAffineNatEval]
    omega

/-- The Archimedean row is inhabited by a nonconstant method. -/
theorem unitArchimedeanAlgebra_nonconstant :
    unitArchimedeanAlgebra.eval .base < unitArchimedeanAlgebra.eval (.succ .base) := by
  decide

/-- The concrete method is covered by the universal Archimedean row theorem. -/
theorem unitArchimedeanAlgebra_no_dup_orientation :
    Not (forall b s n : FreeTerm,
      unitArchimedeanAlgebra.eval (freeSchema.wrap s (freeSchema.recur b s n)) <
        unitArchimedeanAlgebra.eval (freeSchema.recur b s (freeSchema.succ n))) :=
  strictMonotoneAlgebraArchimedean_row_anchor freeSchema unitArchimedeanAlgebra

/-! ## Free-schema Arctic boundary instance -/

/-- A one-dimensional Arctic interpretation with finite positive wrapper diagonals.
It is nonconstant and lives on the independent free step-duplicating syntax. -/
def freeFiniteArcticWeight :
    OperatorKO7.StepDuplicating.StepDuplicatingSchema.FreeTerm → Nat
  | .base => 0
  | .succ t => 1 + freeFiniteArcticWeight t
  | .wrap x y => 1 + max (freeFiniteArcticWeight x) (freeFiniteArcticWeight y)
  | .recur b s n => max (freeFiniteArcticWeight b)
      (max (freeFiniteArcticWeight s) (freeFiniteArcticWeight n))

/-- Native finite-diagonal Arctic interpretation on the free schema. -/
def freeFiniteArcticMeasure : ArcticNatMatrixMeasure
    OperatorKO7.StepDuplicating.StepDuplicatingSchema.freeSchema 1 where
  eval := fun t _ => ArcticNat.fin (freeFiniteArcticWeight t)
  base_vec := fun _ => ArcticNat.fin 0
  succ_bias := fun _ => ArcticNat.fin 0
  succ_mat := ⟨fun _ _ => ArcticNat.fin 1⟩
  wrap_bias := fun _ => ArcticNat.fin 0
  wrap_left := ⟨fun _ _ => ArcticNat.fin 1⟩
  wrap_right := ⟨fun _ _ => ArcticNat.fin 1⟩
  recur_bias := fun _ => ArcticNat.fin 0
  recur_base := ⟨fun _ _ => ArcticNat.fin 0⟩
  recur_step := ⟨fun _ _ => ArcticNat.fin 0⟩
  recur_counter := ⟨fun _ _ => ArcticNat.fin 0⟩
  eval_base := rfl
  eval_succ := by
    intro t
    funext i
    fin_cases i
    simp [OperatorKO7.StepDuplicating.StepDuplicatingSchema.freeSchema,
      freeFiniteArcticWeight, arcticVecMax, arcticMax, ArcticMatrix.act,
      arcticPlus, List.finRange]
  eval_wrap := by
    intro x y
    funext i
    fin_cases i
    simp [OperatorKO7.StepDuplicating.StepDuplicatingSchema.freeSchema,
      freeFiniteArcticWeight, arcticVecMax, arcticMax, ArcticMatrix.act,
      arcticPlus, List.finRange]
  eval_recur := by
    intro b s n
    funext i
    fin_cases i
    simp [OperatorKO7.StepDuplicating.StepDuplicatingSchema.freeSchema,
      freeFiniteArcticWeight, arcticVecMax, arcticMax, ArcticMatrix.act,
      arcticPlus, List.finRange]

/-- The free interpretation satisfies the exact finite-diagonal premise of the
pump-free strict Arctic barrier. -/
theorem freeFiniteArcticMeasure_wrapDiagFinite :
    ArcticWrapDiagFinite freeFiniteArcticMeasure 0 := by
  exact ⟨⟨1, rfl⟩, ⟨1, rfl⟩⟩

/-- The free interpretation is nonconstant. -/
theorem freeFiniteArcticMeasure_nonconstant :
    freeFiniteArcticMeasure.eval
        OperatorKO7.StepDuplicating.StepDuplicatingSchema.freeSchema.base 0 ≠
      freeFiniteArcticMeasure.eval
        (OperatorKO7.StepDuplicating.StepDuplicatingSchema.freeSchema.succ
          OperatorKO7.StepDuplicating.StepDuplicatingSchema.freeSchema.base) 0 := by
  decide

/-- The generic pump-free theorem blocks strict orientation of this actual
finite-diagonal free-schema interpretation. -/
theorem freeFiniteArcticMeasure_blocked :
    ¬ ∀ b s n : OperatorKO7.StepDuplicating.StepDuplicatingSchema.FreeTerm,
      ArcticLt
        (freeFiniteArcticMeasure.eval
          (OperatorKO7.StepDuplicating.StepDuplicatingSchema.freeSchema.wrap s
            (OperatorKO7.StepDuplicating.StepDuplicatingSchema.freeSchema.recur b s n)) 0)
        (freeFiniteArcticMeasure.eval
          (OperatorKO7.StepDuplicating.StepDuplicatingSchema.freeSchema.recur b s
            (OperatorKO7.StepDuplicating.StepDuplicatingSchema.freeSchema.succ n)) 0) := by
  exact no_arcticMatrix_orients_dup_step_of_tracked_strict_pumpFree
    freeFiniteArcticMeasure freeFiniteArcticMeasure_wrapDiagFinite
    (R := fun u v => ArcticLt (u 0) (v 0)) (fun h => h)

/-! ## ORI-2 capstone -/

/-- Native method data for all ten ORI-2 rows. Arctic and tropical fields store
actual matrix interpretations. The tuple field stores the explicit
cross-coupled interpretation that proves the affine-first-projection premise is
load-bearing. -/
structure AlgebraicNativeBundle where
  negative : TruncatedAffineMeasure freeSchema
  negativeDebtActive :
    negative.eval (.wrap .base .base) < negative.eval .base + negative.eval .base
  maxMethod : MaxMeasure freeSchema
  maxNonconstant : maxMethod.eval .base < maxMethod.eval (.succ .base)
  maxBlocked :
    Not (forall b s n : FreeTerm,
      maxMethod.eval (freeSchema.wrap s (freeSchema.recur b s n)) <
        maxMethod.eval (freeSchema.recur b s (freeSchema.succ n)))
  polynomialBoundary : PolynomialBoundaryWitness
  multilinearBoundary : MultilinearBoundaryWitness
  matrixFields : OrderedFieldMatrixFamily
  arcticMethod : ArcticNatMatrixMeasure
    OperatorKO7.StepDuplicating.StepDuplicatingSchema.freeSchema 1
  arcticFinite : ArcticWrapDiagFinite arcticMethod 0
  arcticNonconstant :
    arcticMethod.eval
        OperatorKO7.StepDuplicating.StepDuplicatingSchema.freeSchema.base 0 ≠
      arcticMethod.eval
        (OperatorKO7.StepDuplicating.StepDuplicatingSchema.freeSchema.succ
          OperatorKO7.StepDuplicating.StepDuplicatingSchema.freeSchema.base) 0
  arcticBlocked :
    ¬ ∀ b s n : OperatorKO7.StepDuplicating.StepDuplicatingSchema.FreeTerm,
      ArcticLt
        (arcticMethod.eval
          (OperatorKO7.StepDuplicating.StepDuplicatingSchema.freeSchema.wrap s
            (OperatorKO7.StepDuplicating.StepDuplicatingSchema.freeSchema.recur b s n)) 0)
        (arcticMethod.eval
          (OperatorKO7.StepDuplicating.StepDuplicatingSchema.freeSchema.recur b s
            (OperatorKO7.StepDuplicating.StepDuplicatingSchema.freeSchema.succ n)) 0)
  arcticEscape : ArcticNatMatrixMeasure
    OperatorKO7.StepDuplicating.StepDuplicatingSchema.freeSchema 1
  arcticEscapeViolatesFinite : ¬ ArcticWrapDiagFinite arcticEscape 0
  arcticEscapeOrients :
    ∀ b s n : OperatorKO7.StepDuplicating.StepDuplicatingSchema.FreeTerm,
      ArcticLt
        (arcticEscape.eval
          (OperatorKO7.StepDuplicating.StepDuplicatingSchema.freeSchema.wrap s
            (OperatorKO7.StepDuplicating.StepDuplicatingSchema.freeSchema.recur b s n)) 0)
        (arcticEscape.eval
          (OperatorKO7.StepDuplicating.StepDuplicatingSchema.freeSchema.recur b s
            (OperatorKO7.StepDuplicating.StepDuplicatingSchema.freeSchema.succ n)) 0)
  tropicalMethod : TropicalNatMatrixMeasure freeSchema 1
  tropicalRootOrients :
    ∀ b s n : FreeTerm,
      TropicalLt
        (tropicalMethod.eval (freeSchema.wrap s (freeSchema.recur b s n)) 0)
        (tropicalMethod.eval (freeSchema.recur b s (freeSchema.succ n)) 0)
  tropicalContextBlocked :
    ¬ ∀ {a b : FreeTerm}, FreeDupStepCtx a b →
      TropicalLt (tropicalMethod.eval b 0) (tropicalMethod.eval a 0)
  tupleMethod : FreeTerm → Nat × Nat
  tupleOrients :
    ∀ b s n : FreeTerm,
      (tupleMethod (freeSchema.wrap s (freeSchema.recur b s n))).1 <
        (tupleMethod (freeSchema.recur b s (freeSchema.succ n))).1
  tupleNotAffineFirst :
    ¬ ∃ T : CostSizeTupleInterpretation freeSchema, ∀ t, T.eval t = tupleMethod t
  higherOrderTuple : HigherOrderTupleMethod
  higherOrderTupleBlocked :
    Not (forall b s n : FreeTerm,
      (higherOrderTuple.eval
        (higherOrderTuple.encode (freeSchema.wrap s (freeSchema.recur b s n)))).1 <
      (higherOrderTuple.eval
        (higherOrderTuple.encode (freeSchema.recur b s (freeSchema.succ n)))).1)
  archimedean : ArchimedeanMonotoneAlgebra freeSchema
  archimedeanNonconstant : archimedean.eval .base < archimedean.eval (.succ .base)
  archimedeanBlocked :
    Not (forall b s n : FreeTerm,
      archimedean.eval (freeSchema.wrap s (freeSchema.recur b s n)) <
        archimedean.eval (freeSchema.recur b s (freeSchema.succ n)))

/-- Concrete ORI-2 method package. -/
noncomputable def algebraicNativeBundle : AlgebraicNativeBundle where
  negative := truncatedDebtMethod
  negativeDebtActive := truncatedDebtMethod_debt_active
  maxMethod := maxNativeMethod
  maxNonconstant := maxNativeMethod_nonconstant
  maxBlocked := maxNativeMethod_no_dup_orientation
  polynomialBoundary := polynomialBoundaryWitness
  multilinearBoundary := multilinearBoundaryWitness
  matrixFields := orderedFieldMatrixFamily
  arcticMethod := freeFiniteArcticMeasure
  arcticFinite := freeFiniteArcticMeasure_wrapDiagFinite
  arcticNonconstant := freeFiniteArcticMeasure_nonconstant
  arcticBlocked := freeFiniteArcticMeasure_blocked
  arcticEscape := OperatorKO7.StepDuplicating.StepDuplicatingSchema.arcticBotRightMeasure
  arcticEscapeViolatesFinite :=
    OperatorKO7.StepDuplicating.StepDuplicatingSchema.arcticBotRightMeasure_not_wrapDiagFinite
  arcticEscapeOrients :=
    OperatorKO7.StepDuplicating.StepDuplicatingSchema.arcticBotRightMeasure_strictly_orients
  tropicalMethod := tropicalEscapeMeasure
  tropicalRootOrients := tropicalEscapeMeasure_strictly_orients
  tropicalContextBlocked := tropicalEscapeMeasure_not_context_orienter
  tupleMethod := crossCoupledTupleEval
  tupleOrients := crossCoupledTupleEval_orients
  tupleNotAffineFirst := crossCoupledTupleEval_not_affine_first_component
  higherOrderTuple := higherOrderTupleMethod
  higherOrderTupleBlocked := higherOrderTupleMethod_no_dup_orientation
  archimedean := unitArchimedeanAlgebra
  archimedeanNonconstant := unitArchimedeanAlgebra_nonconstant
  archimedeanBlocked := unitArchimedeanAlgebra_no_dup_orientation

end OperatorKO7.Methods.OrientationClosure.AlgebraicNativeSemantics
