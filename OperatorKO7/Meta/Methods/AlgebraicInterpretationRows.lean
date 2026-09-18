import OperatorKO7.Meta.BarrierPumpDischarge
import OperatorKO7.Meta.AffineBarrierOrderedField_Schema
import OperatorKO7.Meta.MatrixBarrierOrderedField_Schema
import OperatorKO7.Meta.MatrixBarrierNatural
import OperatorKO7.Meta.MatrixBarrierNatural_EWZ
import OperatorKO7.Meta.MatrixBarrierArcticNatural
import OperatorKO7.Meta.MatrixBarrierTropicalNatural_Schema
import OperatorKO7.Meta.DominancePremiseSharpness
import OperatorKO7.Meta.NonlinearUnconstrainedExactLaw
import OperatorKO7.Meta.ScalarProjectionBarrier

/-!
# Carriers for the algebraic interpretation rows of the RDRS coverage ledger (lane E2)

Fourteen names in the 76-row termination-method universe concern algebraic interpretations: linear
polynomials over the rationals and reals, negative-coefficient polynomials with truncation, max
polynomials, higher-degree polynomials, multilinear tables, natural and ordered-field matrices,
arctic and tropical matrices, triangular matrices, cost/size tuple interpretations and their
higher-order version, and strictly monotone Archimedean algebras. The row claims expose every
method axiom consumed by the KO7 verdict and preserve every load-bearing premise.

Three rows carry a premise and are typed CONTRACT with the premise's necessity compiled beside
them: `nonlinearHigherDegreePolynomial`, `multilinearInterpretation`, and
`tupleInterpretationStrictS`. The tropical row records the exact boundary: the primary-projection
class is blocked unconditionally, the wider matrix class is blocked by an explicit scalarization
certificate, the certificate-free root barrier is false, and its root orienter is not compatible
with strict context monotonicity.

Relation: the schema duplicating step at the root, and `Step` for the KO7 instances.
Closure: root.
External trust: none. Mathlib only.
-/

namespace OperatorKO7.Methods.AlgebraicInterpretationRows

open OperatorKO7
open OperatorKO7.StepDuplicating
open OperatorKO7.StepDuplicating.StepDuplicatingSchema
open OperatorKO7.CompositionalImpossibility

/-! ## Linear polynomials over ordered fields -/

/-- Constructor size supplies a nonconstant member of the affine classes. -/
def unitAffineNatEval : FreeTerm → Nat
  | .base => 1
  | .succ t => 1 + unitAffineNatEval t
  | .wrap x y => 1 + unitAffineNatEval x + unitAffineNatEval y
  | .recur b s n => 1 + unitAffineNatEval b + unitAffineNatEval s + unitAffineNatEval n

def unitAffineNatMeasure : AffineMeasure freeSchema where
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
  eval_base := rfl
  eval_succ := by intro t; simp [freeSchema, unitAffineNatEval]
  eval_wrap := by intro x y; simp [freeSchema, unitAffineNatEval]
  eval_recur := by intro b s n; simp [freeSchema, unitAffineNatEval]
  h_wrap_left_pos := by decide
  h_wrap_right_pos := by decide

theorem unitAffineNatMeasure_nonconstant :
    unitAffineNatMeasure.eval (.succ .base) ≠ unitAffineNatMeasure.eval .base := by decide

def unitRationalAffine : FieldAffineMeasure freeSchema NNRat :=
  fieldAffineMeasureNNRat unitAffineNatMeasure

def unitRealAffine : FieldAffineMeasure freeSchema NNReal :=
  fieldAffineMeasureNNReal unitAffineNatMeasure

theorem unitRationalAffine_nonconstant :
    unitRationalAffine.eval (.succ .base) ≠ unitRationalAffine.eval .base := by
  norm_num [unitRationalAffine, fieldAffineMeasureNNRat, unitAffineNatMeasure, unitAffineNatEval]

theorem unitRealAffine_nonconstant :
    unitRealAffine.eval (.succ .base) ≠ unitRealAffine.eval .base := by
  norm_num [unitRealAffine, fieldAffineMeasureNNReal, unitAffineNatMeasure, unitAffineNatEval]

/-- **linearPolyQ.** Affine interpretations with nonnegative rational coefficients. -/
abbrev LinearPolyQRowClaim : Prop :=
  ∀ (S : StepDuplicatingSchema) (M : FieldAffineMeasure S NNRat) (δ : NNRat),
    0 < δ → ¬ FieldAffineOrients M δ

theorem linearPolyQ_row_anchor : LinearPolyQRowClaim :=
  fun _ M δ hδ => no_affine_orients_dup_step_field M δ hδ

/-- **linearPolyR.** The same over the nonnegative reals. -/
abbrev LinearPolyRRowClaim : Prop :=
  ∀ (S : StepDuplicatingSchema) (M : FieldAffineMeasure S NNReal) (δ : NNReal),
    0 < δ → ¬ FieldAffineOrients M δ

theorem linearPolyR_row_anchor : LinearPolyRRowClaim :=
  fun _ M δ hδ => no_affine_orients_dup_step_field M δ hδ

/-! ## Negative coefficients with truncation -/

/-- A zero-truncated affine interpretation with an arbitrary negative wrapper constant.  Natural
subtraction is exactly clipping at zero: `a - wrapDebt` represents `max(0, a - wrapDebt)`.  The two
wrapper coefficients are positive, successor is strictly monotone, and the recursive counter gain
is uniformly bounded. -/
structure TruncatedAffineMeasure (S : StepDuplicatingSchema) where
  eval : S.T → Nat
  wrapDebt : Nat
  wrapLeft : Nat
  wrapRight : Nat
  succGain : Nat
  eval_wrap : ∀ x y,
    eval (S.wrap x y) = wrapLeft * eval x + wrapRight * eval y - wrapDebt
  succ_strict : ∀ t, eval t < eval (S.succ t)
  h_wrap_left_pos : 1 ≤ wrapLeft
  h_wrap_right_pos : 1 ≤ wrapRight
  counter_gain : ∀ b s n, eval (S.recur b s (S.succ n)) ≤ succGain + eval (S.recur b s n)

/-- Truncation can lose at most the fixed debt: after paying that debt, the wrapper still contains
the full value of both arguments.  This is derived from the affine equation, not stored. -/
theorem truncatedAffine_wrap_debt_bound {S : StepDuplicatingSchema}
    (M : TruncatedAffineMeasure S) (x y : S.T) :
    M.eval x + M.eval y ≤ M.wrapDebt + M.eval (S.wrap x y) := by
  rw [M.eval_wrap]
  have hx : M.eval x ≤ M.wrapLeft * M.eval x :=
    Nat.le_mul_of_pos_left _ M.h_wrap_left_pos
  have hy : M.eval y ≤ M.wrapRight * M.eval y :=
    Nat.le_mul_of_pos_left _ M.h_wrap_right_pos
  omega

/-- Strict successor monotonicity supplies an unbounded closed pump internally. -/
theorem truncatedAffine_succIter_ge {S : StepDuplicatingSchema}
    (M : TruncatedAffineMeasure S) (k : Nat) :
    k ≤ M.eval (succIter S k) := by
  induction k with
  | zero => exact Nat.zero_le _
  | succ k ih =>
      have hs := M.succ_strict (succIter S k)
      simp only [succIter]
      omega

/-- **negativeCoefficientPolynomial.** An arbitrary negative wrapper constant and zero truncation
do not help.  Strict successor monotonicity produces a payload larger than the truncation debt plus
the bounded counter gain; the duplicated target then cannot remain below the source. -/
abbrev NegativeCoefficientPolynomialRowClaim : Prop :=
  ∀ (S : StepDuplicatingSchema) (M : TruncatedAffineMeasure S),
    ¬ (∀ (b s n : S.T),
      M.eval (S.wrap s (S.recur b s n)) < M.eval (S.recur b s (S.succ n)))

theorem negativeCoefficientPolynomial_row_anchor : NegativeCoefficientPolynomialRowClaim := by
  intro S M h
  let k := M.wrapDebt + M.succGain + 1
  let s := succIter S k
  have hs : M.wrapDebt + M.succGain + 1 ≤ M.eval s := by
    simpa [k, s] using truncatedAffine_succIter_ge M k
  have horient := h S.base s S.base
  have hdebt := truncatedAffine_wrap_debt_bound M s (S.recur S.base s S.base)
  have hgain := M.counter_gain S.base s S.base
  omega

/-! ## Max polynomials -/

/-- **maxPolynomial.** Unconditional after the pump discharge. -/
abbrev MaxPolynomialRowClaim : Prop :=
  ∀ (Sys : StepDuplicatingSystem) (M : MaxMeasure Sys.toStepDuplicatingSchema),
    ¬ GlobalOrients Sys M.eval (· < ·)

theorem maxPolynomial_row_anchor : MaxPolynomialRowClaim :=
  fun _ M => no_global_orients_max M

/-! ## Higher-degree and multilinear polynomials -/

/-- **nonlinearHigherDegreePolynomial.** CONTRACT: the barrier holds under frozen base dominance,
that premise is discharged on the counter-uncoupled subclass, and it is load-bearing elsewhere with
a compiled orienter. -/
abbrev NonlinearHigherDegreePolynomialRowClaim : Prop :=
  (∀ (S : StepDuplicatingSchema) (M : BoundedPolynomialMeasure S),
      EventuallyDominatedAtBase M →
        ¬ (∀ (b s n : S.T),
          M.eval (S.wrap s (S.recur b s n)) < M.eval (S.recur b s (S.succ n))))
    ∧ (∀ (S : StepDuplicatingSchema) (M : BoundedPolynomialMeasure S),
        NoCounterExponent M → EventuallyDominatedAtBase M)
    ∧ ¬ EventuallyDominatedAtBase crossCoupledPolynomial

theorem nonlinearHigherDegreePolynomial_row_anchor : NonlinearHigherDegreePolynomialRowClaim :=
  ⟨fun _ M hdom => no_polynomial_orients_dup_step_of_dominated M hdom,
    fun _ M h => eventuallyDominatedAtBase_of_no_counter_exponent M h,
    crossCoupledPolynomial_not_eventuallyDominated⟩

/-- **multilinearInterpretation.** CONTRACT, same shape. The row's earlier unconditional wording
is corrected: the dominance premise is necessary, and the necessity witness is compiled. -/
abbrev MultilinearInterpretationRowClaim : Prop :=
  (∀ (S : StepDuplicatingSchema) (M : BoundedMultilinearMeasure S),
      MultilinearDominatedAtBase M →
        ¬ (∀ (b s n : S.T),
          M.eval (S.wrap s (S.recur b s n)) < M.eval (S.recur b s (S.succ n))))
    ∧ (∀ (S : StepDuplicatingSchema) (M : BoundedMultilinearMeasure S),
        NoStepCounterCoupling M → MultilinearDominatedAtBase M)
    ∧ ¬ MultilinearDominatedAtBase crossCoupledMultilinear

theorem multilinearInterpretation_row_anchor : MultilinearInterpretationRowClaim :=
  ⟨fun _ M hdom => no_multilinear_orients_dup_step_of_dominated M hdom,
    fun _ M h => multilinearDominatedAtBase_of_no_coupling M h,
    crossCoupledMultilinear_not_dominatedAtBase⟩

/-! ## Matrix interpretations -/

/-- **matrixNScalarProjection.** The certificate-free natural-matrix barrier with the
Endrullis-Waldmann-Zantema monotonicity condition supplying the positive diagonal. -/
abbrev MatrixNScalarProjectionRowClaim : Prop :=
  ∀ (Sys : StepDuplicatingSystem) (d : Nat) (_ : NeZero d)
    (M : NatMatrixMeasure Sys.toStepDuplicatingSchema d),
    EWZMonotoneInterpretation M → ¬ GlobalOrients Sys M.eval (VecLeLt 0)

theorem matrixNScalarProjection_row_anchor : MatrixNScalarProjectionRowClaim :=
  fun _ _ _ M hewz => no_global_orients_ewzMonotone M hewz

/-- **matrixQRScalarProjection.** The same over the nonnegative rationals and reals. -/
abbrev MatrixQRScalarProjectionRowClaim : Prop :=
  (∀ (S : StepDuplicatingSchema) (d : Nat) (M : NatMatrixMeasure S d) (i : Fin d),
      WrapDiagPositive M i →
        ∀ (R : FieldMatrixVec d NNRat → FieldMatrixVec d NNRat → Prop),
          (∀ {u v : FieldMatrixVec d NNRat}, R u v → u i < v i) →
            ¬ (∀ (b s n : S.T),
              R ((fieldNatMatrixMeasureOfNat (K := NNRat) M).eval (S.wrap s (S.recur b s n)))
                ((fieldNatMatrixMeasureOfNat (K := NNRat) M).eval (S.recur b s (S.succ n)))))
    ∧ (∀ (S : StepDuplicatingSchema) (d : Nat) (M : NatMatrixMeasure S d) (i : Fin d),
        WrapDiagPositive M i →
          ∀ (R : FieldMatrixVec d NNReal → FieldMatrixVec d NNReal → Prop),
            (∀ {u v : FieldMatrixVec d NNReal}, R u v → u i < v i) →
              ¬ (∀ (b s n : S.T),
                R ((fieldNatMatrixMeasureOfNat (K := NNReal) M).eval (S.wrap s (S.recur b s n)))
                  ((fieldNatMatrixMeasureOfNat (K := NNReal) M).eval (S.recur b s (S.succ n)))))

theorem matrixQRScalarProjection_row_anchor : MatrixQRScalarProjectionRowClaim :=
  ⟨fun _ _ M _ hi _ hR => no_matrix_orients_dup_step_nnrat M hi hR,
    fun _ _ M _ hi _ hR => no_matrix_orients_dup_step_nnreal M hi hR⟩

/-- **arcticScalarProjection.** The arctic barrier at the KO7 layer, in the pump-free strict form
and in the context-closed form. -/
abbrev ArcticScalarProjectionRowClaim : Prop :=
  (∀ (d : Nat) (M : ArcticNatMatrixMeasure ko7Schema d) (i : Fin d),
      ArcticWrapDiagFinite M i →
        ¬ GlobalOrients ko7System M.eval (fun u v => ArcticLt (u i) (v i)))
    ∧ ¬ OperatorKO7.ContextClosedBarrier.GlobalOrientsStepCtxFull
        OperatorKO7.MatrixBarrierArcticNatural.sizeArcticMeasure.eval
        (fun u v => ArcticLt (u 0) (v 0))

theorem arcticScalarProjection_row_anchor : ArcticScalarProjectionRowClaim :=
  ⟨fun _ M _ hi =>
      OperatorKO7.MatrixBarrierArcticNatural.no_global_step_orientation_arcticMatrix_of_tracked_strict_pumpFree
        M hi (fun h => h),
    OperatorKO7.MatrixBarrierArcticNatural.sizeArcticMeasure_no_ctx_orientation⟩

/-- **tropicalScalarProjection.** The actual primary-projection class is blocked unconditionally.
For the wider tropical-matrix class, the barrier follows from an explicit scalarization certificate
and unbounded scalarized range. The certificate-free strengthening is false at the root, and the
escaping root interpretation is not a contextual termination interpretation. -/
abbrev TropicalScalarProjectionRowClaim : Prop :=
  (∀ (S : StepDuplicatingSchema) (β : Type) (M : TropicalPrimaryMeasure S β),
      ¬ (∀ (b s n : S.T),
        M.lt (M.eval (S.wrap s (S.recur b s n)))
          (M.eval (S.recur b s (S.succ n)))))
    ∧ (∀ (S : StepDuplicatingSchema) (d : Nat) (M : TropicalMatrixMeasure S d)
      (C : TropicalMatrixCertificate d),
      C.weight = M.scalarMeasure.weight →
        (∀ t : S.T, C.scalarize (M.eval t) = M.scalarMeasure.eval t) →
          HasUnboundedScalarizedRange M.scalarMeasure →
            ¬ (∀ (b s n : S.T),
              C.lt (M.eval (S.wrap s (S.recur b s n)))
                (M.eval (S.recur b s (S.succ n)))))
    ∧ (∃ (M : TropicalNatMatrixMeasure freeSchema 1),
        TropicalWrapDiagPositive M 0 ∧
          (∃ (t : FreeTerm) (a : Nat), M.eval t 0 = TropicalNat.fin a) ∧
          (∀ (b s n : FreeTerm),
            TropicalLt (M.eval (freeSchema.wrap s (freeSchema.recur b s n)) 0)
              (M.eval (freeSchema.recur b s (freeSchema.succ n)) 0)))
    ∧ ¬ TropicalWrapStrictAt tropicalEscapeMeasure 0
    ∧ ¬ (∀ {a b : FreeTerm}, FreeDupStepCtx a b →
        TropicalLt (tropicalEscapeMeasure.eval b 0) (tropicalEscapeMeasure.eval a 0))

theorem tropicalScalarProjection_row_anchor : TropicalScalarProjectionRowClaim :=
  ⟨fun _ _ M => no_tropical_primary_orients_dup_step M,
    fun _ _ M C hweight hscalarize hunbounded =>
      no_tropicalMatrix_orients_dup_step_of_scalar_dominance_pump
        M C hweight hscalarize hunbounded,
    certificate_free_tropical_barrier_false,
    tropical_root_escape_not_context_compatible.2,
    tropicalEscapeMeasure_not_context_orienter⟩

/-- A triangular natural matrix: zero below the diagonal and diagonal entries at most one
(Moser, Schnabl, Waldmann, FSTTCS 2008, Definition 3). -/
def UpperTriangular {d : Nat} (A : MixedMatrix d) : Prop :=
  (∀ i j : Fin d, j.val < i.val → A.coeff i j = 0) ∧ ∀ i : Fin d, A.coeff i i ≤ 1

/-- **triangularMatrix.** Triangular natural matrices are natural matrix interpretations, and
Endrullis-Waldmann-Zantema monotonicity forces a positive diagonal, so the certificate-free
barrier applies with no extra hypothesis. -/
abbrev TriangularMatrixRowClaim : Prop :=
  ∀ (Sys : StepDuplicatingSystem) (d : Nat) (_ : NeZero d)
    (M : NatMatrixMeasure Sys.toStepDuplicatingSchema d),
    EWZMonotoneInterpretation M →
      UpperTriangular M.wrap_left → UpperTriangular M.wrap_right →
        ¬ GlobalOrients Sys M.eval (VecLeLt 0)

theorem triangularMatrix_row_anchor : TriangularMatrixRowClaim :=
  fun _ _ _ M hewz _ _ => no_global_orients_ewzMonotone M hewz

/-! ## Tuple interpretations -/

/-- A cost/size tuple interpretation strict in the cost component. The cost projection is an
affine measure on the schema, which is what makes the scalar-projection theorem apply. -/
structure CostSizeTupleInterpretation (S : StepDuplicatingSchema) where
  eval : S.T → Nat × Nat
  cost : AffineMeasure S
  cost_is_first : ∀ t, (eval t).1 = cost.eval t

/-- Unrestricted tuple interpretation induced by the cross-coupled polynomial witness.  Its first
component orients the duplicating step; the second component is irrelevant. -/
def crossCoupledTupleEval : FreeTerm → Nat × Nat :=
  fun t => (crossCoupledWeight t, 0)

theorem crossCoupledTupleEval_orients :
    ∀ b s n : FreeTerm,
      (crossCoupledTupleEval (freeSchema.wrap s (freeSchema.recur b s n))).1 <
        (crossCoupledTupleEval (freeSchema.recur b s (freeSchema.succ n))).1 := by
  intro b s n
  exact crossCoupledWeight_strictly_orients b s n

/-- **tupleInterpretationStrictS.** CONTRACT: the contract clause is that the cost component is
the projection of an affine measure, and under it the barrier is unconditional. The clause is
load-bearing: the cross-coupled first component below strictly orients every duplicating instance
and cannot be represented by any member of the affine first-projection class. -/
abbrev TupleInterpretationStrictSRowClaim : Prop :=
  (∀ (S : StepDuplicatingSchema) (T : CostSizeTupleInterpretation S),
      ¬ (∀ (b s n : S.T),
        (T.eval (S.wrap s (S.recur b s n))).1 < (T.eval (S.recur b s (S.succ n))).1))
    ∧ (∀ (S : StepDuplicatingSchema) (T : CostSizeTupleInterpretation S) (x y : S.T),
        T.cost.eval x + T.cost.eval y ≤ T.cost.eval (S.wrap x y))

theorem tupleInterpretationStrictS_row_anchor : TupleInterpretationStrictSRowClaim := by
  refine ⟨fun S T h => ?_, ?_⟩
  · refine no_affine_orients_dup_step T.cost (fun b s n => ?_)
    have := h b s n
    rwa [T.cost_is_first, T.cost_is_first] at this
  · intro S T x y
    have hl := T.cost.h_wrap_left_pos
    have hr := T.cost.h_wrap_right_pos
    have hx : T.cost.eval x ≤ T.cost.wrap_left * T.cost.eval x := Nat.le_mul_of_pos_left _ hl
    have hy : T.cost.eval y ≤ T.cost.wrap_right * T.cost.eval y := Nat.le_mul_of_pos_left _ hr
    rw [T.cost.eval_wrap]
    omega

/-- The affine first-component contract is load-bearing.  The compiled orienting tuple cannot be
the evaluation of any `CostSizeTupleInterpretation`, because that would contradict the universal
affine-projection barrier above. -/
theorem crossCoupledTupleEval_not_affine_first_component :
    ¬ ∃ T : CostSizeTupleInterpretation freeSchema,
      ∀ t : FreeTerm, T.eval t = crossCoupledTupleEval t := by
  rintro ⟨T, hT⟩
  apply tupleInterpretationStrictS_row_anchor.1 freeSchema T
  intro b s n
  simpa [hT] using crossCoupledTupleEval_orients b s n

/-- Exact sharpness package for the tuple boundary: affine first projections are universally
blocked, while an unrestricted cost/size tuple orients, and that tuple lies outside the affine
first-projection class. -/
theorem tupleInterpretationStrictS_exact_boundary :
    TupleInterpretationStrictSRowClaim
      ∧ (∀ b s n : FreeTerm,
        (crossCoupledTupleEval (freeSchema.wrap s (freeSchema.recur b s n))).1 <
          (crossCoupledTupleEval (freeSchema.recur b s (freeSchema.succ n))).1)
      ∧ ¬ ∃ T : CostSizeTupleInterpretation freeSchema,
        ∀ t : FreeTerm, T.eval t = crossCoupledTupleEval t :=
  ⟨tupleInterpretationStrictS_row_anchor, crossCoupledTupleEval_orients,
    crossCoupledTupleEval_not_affine_first_component⟩

/-- The first-order restriction of a higher-order tuple interpretation: the applicative layer is
erased and the ground terms carry the same cost/size pair. -/
structure HigherOrderTupleRestriction (S : StepDuplicatingSchema) where
  ambient : CostSizeTupleInterpretation S
  restriction : S.T → S.T
  restriction_preserves_cost : ∀ t, (ambient.eval (restriction t)).1 = (ambient.eval t).1

@[simp] theorem HigherOrderTupleRestriction.eval_restriction_first
    {S : StepDuplicatingSchema} (H : HigherOrderTupleRestriction S) (t : S.T) :
    (H.ambient.eval (H.restriction t)).1 = (H.ambient.eval t).1 :=
  H.restriction_preserves_cost t

/-- **higherOrderTupleInterpretation.** The first-order restriction reduces to the row above, so
the barrier transports without a new argument. -/
abbrev HigherOrderTupleInterpretationRowClaim : Prop :=
  ∀ (S : StepDuplicatingSchema) (H : HigherOrderTupleRestriction S),
    ¬ (∀ (b s n : S.T),
      (H.ambient.eval (H.restriction (S.wrap s (S.recur b s n)))).1 <
        (H.ambient.eval (H.restriction (S.recur b s (S.succ n)))).1)

theorem higherOrderTupleInterpretation_row_anchor : HigherOrderTupleInterpretationRowClaim := by
  intro S H h
  apply tupleInterpretationStrictS_row_anchor.1 S H.ambient
  intro b s n
  simpa using h b s n

/-! ## Strictly monotone Archimedean algebras -/

/-- An interpretation into a linearly ordered Archimedean commutative monoid in which the wrapper
dominates the sum of its arguments and the successor strictly increases. -/
structure ArchimedeanMonotoneAlgebra (S : StepDuplicatingSchema) where
  eval : S.T → Nat
  succ_strict : ∀ t, eval t < eval (S.succ t)
  wrap_dominates : ∀ x y, eval x + eval y ≤ eval (S.wrap x y)
  counterGain : Nat
  counter_gain : ∀ b s n, eval (S.recur b s (S.succ n)) ≤ counterGain + eval (S.recur b s n)

/-- The successor chain of a strictly monotone algebra is unbounded, which is the Archimedean
content in the natural-valued setting. -/
theorem archimedean_unbounded {S : StepDuplicatingSchema} (A : ArchimedeanMonotoneAlgebra S)
    (k : Nat) : k ≤ A.eval (succIter S k) := by
  induction k with
  | zero => exact Nat.zero_le _
  | succ k ih =>
      have h := A.succ_strict (succIter S k)
      simp only [succIter]
      omega

/-- **strictMonotoneAlgebraArchimedean.** A strictly monotone Archimedean algebra whose wrapper
dominates the sum of its arguments fails to orient the duplicating step. -/
abbrev StrictMonotoneAlgebraArchimedeanRowClaim : Prop :=
  ∀ (S : StepDuplicatingSchema) (A : ArchimedeanMonotoneAlgebra S),
    ¬ (∀ (b s n : S.T),
      A.eval (S.wrap s (S.recur b s n)) < A.eval (S.recur b s (S.succ n)))

theorem strictMonotoneAlgebraArchimedean_row_anchor :
    StrictMonotoneAlgebraArchimedeanRowClaim := by
  intro S A
  exact no_unconstrainedDirect_orients_dup_step
    { eval := A.eval
      wrapCost := 0
      wrap_keeps_arguments := fun x y => by
        have := A.wrap_dominates x y
        omega
      succGain := A.counterGain
      counter_gain := A.counter_gain
      }

end OperatorKO7.Methods.AlgebraicInterpretationRows
