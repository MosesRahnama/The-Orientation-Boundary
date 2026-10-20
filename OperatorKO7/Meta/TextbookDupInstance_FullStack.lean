import OperatorKO7.Meta.TextbookDupInstance
import OperatorKO7.Meta.BarrierPumpDischarge_Schema
import OperatorKO7.Meta.MatrixBarrierNatural_EWZ
import OperatorKO7.Meta.MatrixBarrierArcticNatural
import OperatorKO7.Meta.MatrixBarrierArcticTropical_Schema
import OperatorKO7.Meta.MatrixBarrierOrderedField_Schema
import OperatorKO7.Meta.AffineBarrierOrderedField_Schema
import OperatorKO7.Meta.SchemaBarrier_OrderedCarrier
import OperatorKO7.Meta.NonlinearUnconstrainedExactLaw
import OperatorKO7.Meta.DominancePremiseSharpness

/-!
# The classic duplicating rule carries the whole barrier stack

`Meta/TextbookDupInstance.lean` builds the schema instance for the first-order rule
`f(x, s(y)) → g(x, f(x, y))` and proves three barriers on it. The remark in the manuscript claims
more: that the textbook rule is a schema instance, so **every** schema-level barrier applies to it.
This module makes that claim a theorem by instantiating the barrier stack at `textbookSystem`:
additive, transparent-compositional, affine, quadratic, bounded cross-term quadratic, bounded
multilinear, generalized bounded-polynomial, max-plus, the certificate-free natural-matrix family
with its Endrullis-Waldmann-Zantema, componentwise, lexicographic, permuted-lexicographic,
functional, mixed, and arbitrary-with-scalar-dominance branches, the pump-free strict arctic
family, the certificate-backed arctic and tropical branches, the ordered-field and ordered-carrier
corollaries, and the exact law of the unconstrained nonlinear direct row.

The affine barrier is unconditional here: the growth half is discharged in
`Meta/BarrierPumpDischarge_Schema.lean`, so `no_global_textbook_orientation_affine` replaces the
older `no_global_textbook_orientation_affine_of_unbounded`, which is kept as the weaker corollary.

Relation: `TextbookStep`. Closure: root.
External trust: none. Mathlib only.
Named method: every direct interpretation class carried by the step-duplicating schema.
-/

namespace OperatorKO7.TextbookDupInstance

open OperatorKO7.StepDuplicating
open OperatorKO7.StepDuplicating.StepDuplicatingSchema

/-! ## Tier 1: additive, transparent-compositional, affine -/

/-- **The affine barrier at the textbook rule, unconditional.** -/
theorem no_global_textbook_orientation_affine
    (M : AffineMeasure textbookSchema) :
    ¬ GlobalOrients textbookSystem M.eval (· < ·) :=
  no_global_orients_affine (Sys := textbookSystem) M

/-! ## Tier 2: the nonlinear scalar families -/

/-- The counter-square quadratic barrier at the textbook rule, unconditional. -/
theorem no_global_textbook_orientation_quadratic
    (M : QuadraticCounterMeasure textbookSchema) :
    ¬ GlobalOrients textbookSystem M.eval (· < ·) :=
  no_global_orients_quadratic (Sys := textbookSystem) M

/-- The bounded cross-term quadratic barrier at the textbook rule. -/
theorem no_global_textbook_orientation_cross_quadratic
    (M : CrossTermQuadraticMeasure textbookSchema) (hb : CrossTermBoundedAtBase M) :
    ¬ GlobalOrients textbookSystem M.eval (· < ·) :=
  no_global_orients_cross_quadratic_of_bounded (Sys := textbookSystem) M hb

/-- The bounded cross-term quadratic barrier at the textbook rule, unconditional on the uncoupled
subclass. -/
theorem no_global_textbook_orientation_cross_quadratic_of_no_cross
    (M : CrossTermQuadraticMeasure textbookSchema) (hx : M.recur_cross = 0) :
    ¬ GlobalOrients textbookSystem M.eval (· < ·) :=
  no_global_orients_cross_quadratic_of_bounded (Sys := textbookSystem) M
    (crossTermBoundedAtBase_of_no_cross M hx)

/-- The bounded multilinear barrier at the textbook rule. -/
theorem no_global_textbook_orientation_multilinear
    (M : BoundedMultilinearMeasure textbookSchema) (hdom : MultilinearDominatedAtBase M) :
    ¬ GlobalOrients textbookSystem M.eval (· < ·) :=
  no_global_orients_multilinear_of_dominated (Sys := textbookSystem) M hdom

/-- The bounded multilinear barrier at the textbook rule, unconditional on the uncoupled
subclass. -/
theorem no_global_textbook_orientation_multilinear_of_no_coupling
    (M : BoundedMultilinearMeasure textbookSchema) (h : NoStepCounterCoupling M) :
    ¬ GlobalOrients textbookSystem M.eval (· < ·) :=
  no_global_orients_multilinear_of_dominated (Sys := textbookSystem) M
    (multilinearDominatedAtBase_of_no_coupling M h)

/-- The generalized bounded-polynomial barrier at the textbook rule. -/
theorem no_global_textbook_orientation_polynomial
    (M : BoundedPolynomialMeasure textbookSchema) (hdom : EventuallyDominatedAtBase M) :
    ¬ GlobalOrients textbookSystem M.eval (· < ·) :=
  no_global_orients_polynomial_of_dominated (Sys := textbookSystem) M hdom

/-- The generalized bounded-polynomial barrier at the textbook rule, unconditional on the
counter-uncoupled subclass. -/
theorem no_global_textbook_orientation_polynomial_of_no_counter_exponent
    (M : BoundedPolynomialMeasure textbookSchema) (h : NoCounterExponent M) :
    ¬ GlobalOrients textbookSystem M.eval (· < ·) :=
  no_global_orients_polynomial_of_dominated (Sys := textbookSystem) M
    (eventuallyDominatedAtBase_of_no_counter_exponent M h)

/-- The WPO-style bounded polynomial branch at the textbook rule. -/
theorem no_global_textbook_orientation_wpoPolynomialDirect
    (W : WPOPolynomialDirectOrder textbookSchema)
    (hdom : EventuallyDominatedAtBase W.measure) :
    ¬ GlobalOrients textbookSystem (fun t => t) (fun x y => W.gt y x) :=
  no_global_orients_wpoPolynomialDirect_of_dominated (Sys := textbookSystem) W hdom

/-- The max-plus barrier at the textbook rule, unconditional. -/
theorem no_global_textbook_orientation_max
    (M : MaxMeasure textbookSchema) :
    ¬ GlobalOrients textbookSystem M.eval (· < ·) :=
  no_global_orients_max (Sys := textbookSystem) M

/-! ## Exact sharpness on the textbook carrier -/

/-- Cross-coupled textbook interpretation.  Advancing the counter creates exactly one additional
copy of the step value, which pays for the duplicated occurrence on the right. -/
def textbookCrossCoupledWeight : TextbookTerm → Nat
  | TextbookTerm.zero => 1
  | TextbookTerm.succ t => 1 + textbookCrossCoupledWeight t
  | TextbookTerm.g x y => textbookCrossCoupledWeight x + textbookCrossCoupledWeight y
  | TextbookTerm.f x y =>
      textbookCrossCoupledWeight y +
        textbookCrossCoupledWeight x * textbookCrossCoupledWeight y

theorem textbookCrossCoupledWeight_strictly_orients (x y : TextbookTerm) :
    textbookCrossCoupledWeight (TextbookTerm.g x (TextbookTerm.f x y)) <
      textbookCrossCoupledWeight (TextbookTerm.f x (TextbookTerm.succ y)) := by
  simp only [textbookCrossCoupledWeight]
  rw [Nat.mul_add]
  simp only [Nat.mul_one]
  omega

theorem textbookCrossCoupledWeight_global_orients :
    GlobalOrients textbookSystem textbookCrossCoupledWeight (· < ·) := by
  intro source target h
  cases h with
  | dup x y => exact textbookCrossCoupledWeight_strictly_orients x y

def textbookCrossCoupledQuadratic : CrossTermQuadraticMeasure textbookSchema where
  eval := textbookCrossCoupledWeight
  c_base := 1
  succ_bias := 1
  succ_scale := 1
  wrap_const := 0
  wrap_left := 1
  wrap_right := 1
  recur_const := 0
  recur_base := 0
  recur_step := 0
  recur_counter := 1
  recur_quad := 0
  recur_cross := 1
  eval_base := rfl
  eval_succ := fun t => by simp [textbookSchema, textbookCrossCoupledWeight]
  eval_wrap := fun x y => by simp [textbookSchema, textbookCrossCoupledWeight]
  eval_recur := fun b s n => by simp [textbookSchema, textbookCrossCoupledWeight]
  h_wrap_left_pos := le_refl 1
  h_wrap_right_pos := le_refl 1

def textbookCrossCoupledMultilinear : BoundedMultilinearMeasure textbookSchema where
  eval := textbookCrossCoupledWeight
  c_base := 1
  succ_bias := 1
  succ_scale := 1
  wrap_const := 0
  wrap_left := 1
  wrap_right := 1
  recur_const := 0
  recur_base := 0
  recur_step := 0
  recur_counter := 1
  monomials := [{ coeff := 1, useBase := false, useStep := true, useCounter := true }]
  eval_base := rfl
  eval_succ := fun t => by simp [textbookSchema, textbookCrossCoupledWeight]
  eval_wrap := fun x y => by simp [textbookSchema, textbookCrossCoupledWeight]
  eval_recur := fun b s n => by simp [textbookSchema, textbookCrossCoupledWeight]
  h_wrap_left_pos := le_refl 1
  h_wrap_right_pos := le_refl 1

def textbookCrossCoupledPolynomial : BoundedPolynomialMeasure textbookSchema where
  eval := textbookCrossCoupledWeight
  c_base := 1
  succ_bias := 1
  succ_scale := 1
  wrap_const := 0
  wrap_left := 1
  wrap_right := 1
  recur_const := 0
  recur_base := 0
  recur_step := 0
  recur_counter := 1
  monomials := [{ coeff := 1, basePow := 0, stepPow := 1, counterPow := 1 }]
  eval_base := rfl
  eval_succ := fun t => by simp [textbookSchema, textbookCrossCoupledWeight]
  eval_wrap := fun x y => by simp [textbookSchema, textbookCrossCoupledWeight]
  eval_recur := fun b s n => by simp [textbookSchema, textbookCrossCoupledWeight]
  h_wrap_left_pos := le_refl 1
  h_wrap_right_pos := le_refl 1

theorem textbookCrossCoupledQuadratic_not_boundedAtBase :
    ¬ CrossTermBoundedAtBase textbookCrossCoupledQuadratic := by
  simp [CrossTermBoundedAtBase, textbookCrossCoupledQuadratic]

theorem textbookCrossCoupledMultilinear_not_dominatedAtBase :
    ¬ MultilinearDominatedAtBase textbookCrossCoupledMultilinear := by
  simp [MultilinearDominatedAtBase, textbookCrossCoupledMultilinear,
    BoundedMultilinearMeasure.stepCoeffSum]

theorem textbookCrossCoupledPolynomial_not_eventuallyDominated :
    ¬ EventuallyDominatedAtBase textbookCrossCoupledPolynomial := by
  rintro ⟨K, hK⟩
  have h := hK K (le_refl K)
  simp [BoundedPolynomialMeasure.sourceFrozenAtBase,
    BoundedPolynomialMeasure.targetFrozenAtBase, textbookCrossCoupledPolynomial] at h
  omega

/-- **Exact textbook boundary.**  The three dominance-qualified barriers cannot be promoted to
unrestricted class-wide barriers: one interpretation on the textbook carrier lies in all three
classes, globally orients the rule, and violates exactly the premise each theorem requires. -/
theorem textbook_three_dominance_premises_are_sharp :
    (¬ CrossTermBoundedAtBase textbookCrossCoupledQuadratic
      ∧ GlobalOrients textbookSystem textbookCrossCoupledQuadratic.eval (· < ·))
    ∧ (¬ MultilinearDominatedAtBase textbookCrossCoupledMultilinear
      ∧ GlobalOrients textbookSystem textbookCrossCoupledMultilinear.eval (· < ·))
    ∧ (¬ EventuallyDominatedAtBase textbookCrossCoupledPolynomial
      ∧ GlobalOrients textbookSystem textbookCrossCoupledPolynomial.eval (· < ·)) := by
  exact ⟨⟨textbookCrossCoupledQuadratic_not_boundedAtBase,
      textbookCrossCoupledWeight_global_orients⟩,
    ⟨textbookCrossCoupledMultilinear_not_dominatedAtBase,
      textbookCrossCoupledWeight_global_orients⟩,
    ⟨textbookCrossCoupledPolynomial_not_eventuallyDominated,
      textbookCrossCoupledWeight_global_orients⟩⟩

/-! ## Tier 3: the matrix families -/

/-- The certificate-free natural-matrix barrier at the textbook rule, strict form. -/
theorem no_global_textbook_orientation_naturalMatrix_of_tracked_strict
    {d : Nat} (M : NatMatrixMeasure textbookSchema d) {i : Fin d} (hi : WrapDiagPositive M i)
    {R : MatrixVec d → MatrixVec d → Prop}
    (hR : ∀ {u v : MatrixVec d}, R u v → u i < v i) :
    ¬ GlobalOrients textbookSystem M.eval R :=
  no_global_orients_natMatrix_of_tracked_strict (Sys := textbookSystem) M hi hR

/-- The certificate-free natural-matrix barrier at the textbook rule, componentwise order. -/
theorem no_global_textbook_orientation_naturalMatrix_componentwise
    {d : Nat} (M : NatMatrixMeasure textbookSchema d) {i : Fin d} (hi : WrapDiagPositive M i) :
    ¬ GlobalOrients textbookSystem M.eval VecLt :=
  no_global_orients_natMatrix_componentwise (Sys := textbookSystem) M hi

/-- The certificate-free natural-matrix barrier at the textbook rule, lexicographic order. -/
theorem no_global_textbook_orientation_naturalMatrix_lex
    {d : Nat} (M : NatMatrixMeasure textbookSchema (d + 1))
    (hi : WrapDiagPositive M (primaryIdx d))
    (hpos : ∃ t : TextbookTerm, 1 ≤ M.eval t (primaryIdx d)) :
    ¬ GlobalOrients textbookSystem M.eval VecLexLt :=
  no_global_orients_natMatrix_lexD_of_primary_pos (Sys := textbookSystem) M hi hpos

/-- The certificate-free natural-matrix barrier at the textbook rule, arbitrary permutation
priority. -/
theorem no_global_textbook_orientation_naturalMatrix_permLex
    {d : Nat} (σ : Equiv.Perm (Fin (d + 1)))
    (M : NatMatrixMeasure textbookSchema (d + 1))
    (hi : WrapDiagPositive M (permPrimaryIdx σ))
    (hpos : ∃ t : TextbookTerm, 1 ≤ M.eval t (permPrimaryIdx σ)) :
    ¬ GlobalOrients textbookSystem M.eval (VecPermLexLt σ) :=
  no_global_orients_natMatrix_lexPermD_of_primary_pos (Sys := textbookSystem) σ M hi hpos

/-- The Endrullis-Waldmann-Zantema monotone-matrix barrier at the textbook rule. -/
theorem no_global_textbook_orientation_ewzMonotone
    {d : Nat} [NeZero d] (M : NatMatrixMeasure textbookSchema d)
    (hewz : EWZMonotoneInterpretation M) :
    ¬ GlobalOrients textbookSystem M.eval (VecLeLt 0) :=
  no_global_orients_ewzMonotone (Sys := textbookSystem) M hewz

/-- The tracked-primary matrix barrier at the textbook rule. -/
theorem no_global_textbook_orientation_matrixD
    {d : Nat} {tracked : Fin d} (M : MatrixMeasureD textbookSchema d tracked) :
    ¬ GlobalOrients textbookSystem M.eval VecLt :=
  no_global_orients_matrixD (Sys := textbookSystem) M

/-- The tracked-primary pair barrier at the textbook rule. -/
theorem no_global_textbook_orientation_matrix2
    (M : MatrixMeasure2 textbookSchema) :
    ¬ GlobalOrients textbookSystem M.eval PairLt :=
  no_global_orients_matrix2 (Sys := textbookSystem) M

/-- The lexicographic pair barrier at the textbook rule. -/
theorem no_global_textbook_orientation_matrix2_lex
    (M : MatrixMeasure2 textbookSchema)
    (hpos : ∃ t : TextbookTerm, 1 ≤ (M.eval t).1) :
    ¬ GlobalOrients textbookSystem M.eval PairLexLt :=
  no_global_orients_matrix2_lex_of_fst_pos (Sys := textbookSystem) M hpos

/-- The functional matrix barrier at the textbook rule. -/
theorem no_global_textbook_orientation_matrixFunctional
    {d : Nat} (M : MatrixFunctionalMeasure textbookSchema d) :
    ¬ GlobalOrients textbookSystem M.eval VecLt :=
  no_global_orients_matrixFunctional (Sys := textbookSystem) M

/-- The mixed-coordinate matrix barrier at the textbook rule. -/
theorem no_global_textbook_orientation_matrixMix2
    (M : MatrixMix2Measure textbookSchema) :
    ¬ GlobalOrients textbookSystem M.eval PairLt :=
  no_global_orients_matrixMix2 (Sys := textbookSystem) M

/-- The finite tracked-primary lexicographic matrix barrier at the textbook rule. -/
theorem no_global_textbook_orientation_matrixLexD
    {d : Nat} (M : MatrixLexMeasureD textbookSchema d)
    (hpos : ∃ t : TextbookTerm, 1 ≤ M.eval t (primaryIdx d)) :
    ¬ GlobalOrients textbookSystem M.eval VecLexLt :=
  no_global_orients_matrixLexD_of_primary_pos (Sys := textbookSystem) M hpos

/-- The permutation-priority tracked lexicographic matrix barrier at the textbook rule. -/
theorem no_global_textbook_orientation_matrixLexPermD
    {d : Nat} (M : MatrixLexPermMeasureD textbookSchema d)
    (hpos : ∃ t : TextbookTerm, 1 ≤ M.eval t (permPrimaryIdx M.priority)) :
    ¬ GlobalOrients textbookSystem M.eval (VecPermLexLt M.priority) :=
  no_global_orients_matrixLexPermD_of_primary_pos (Sys := textbookSystem) M hpos

/-- The arbitrary matrix barrier with a scalar dominance certificate at the textbook rule. -/
theorem no_global_textbook_orientation_matrixArbitrary
    {d : Nat} (M : MatrixArbitraryMeasure textbookSchema d)
    {R : MatrixVec d → MatrixVec d → Prop} (D : MatrixScalarDominance M.weight R)
    (hpos : ∃ t : TextbookTerm, 1 ≤ matrixScalarize M.weight (M.eval t)) :
    ¬ GlobalOrients textbookSystem M.eval R :=
  no_global_orients_matrixArbitrary_of_scalar_dominance_of_pos (Sys := textbookSystem) M D hpos

/-- The arctic matrix barrier at the textbook rule, strict form, pump free. -/
theorem no_global_textbook_orientation_arcticMatrix
    {d : Nat} (M : ArcticNatMatrixMeasure textbookSchema d) {i : Fin d}
    (hi : ArcticWrapDiagFinite M i)
    {R : ArcticVec d → ArcticVec d → Prop}
    (hR : ∀ {u v : ArcticVec d}, R u v → ArcticLt (u i) (v i)) :
    ¬ GlobalOrients textbookSystem M.eval R :=
  no_global_orients_arcticMatrix_of_tracked_strict_pumpFree (Sys := textbookSystem) M hi hR

/-- The certificate-backed arctic scalarization barrier at the textbook rule. -/
theorem no_global_textbook_orientation_arcticMatrix_certificate
    {d : Nat} (M : ArcticMatrixMeasure textbookSchema d) (C : ArcticMatrixCertificate d)
    (hweight : C.weight = M.scalarMeasure.weight)
    (hscalarize : ∀ t : TextbookTerm, C.scalarize (M.eval t) = M.scalarMeasure.eval t)
    (hunbounded : HasUnboundedScalarizedRange M.scalarMeasure) :
    ¬ GlobalOrients textbookSystem M.eval C.lt := by
  intro h
  exact no_arcticMatrix_orients_dup_step_of_scalar_dominance_pump M C hweight hscalarize
    hunbounded (fun b s n => h (textbookSystem.dup_step b s n))

/-- The certificate-backed tropical scalarization barrier at the textbook rule. The
certificate-free tropical class is excluded by the compiled root orienter, so this explicit
scalarization datum is load-bearing. -/
theorem no_global_textbook_orientation_tropicalMatrix_certificate
    {d : Nat} (M : TropicalMatrixMeasure textbookSchema d) (C : TropicalMatrixCertificate d)
    (hweight : C.weight = M.scalarMeasure.weight)
    (hscalarize : ∀ t : TextbookTerm, C.scalarize (M.eval t) = M.scalarMeasure.eval t)
    (hunbounded : HasUnboundedScalarizedRange M.scalarMeasure) :
    ¬ GlobalOrients textbookSystem M.eval C.lt := by
  intro h
  exact no_tropicalMatrix_orients_dup_step_of_scalar_dominance_pump M C hweight hscalarize
    hunbounded (fun b s n => h (textbookSystem.dup_step b s n))

/-! ## Tier 4: the ordered-carrier and ordered-field corollaries -/

/-- The ordered-carrier additive barrier at the textbook rule. -/
theorem no_textbook_orientation_ordered_additive {α : Type*} [AddCommMonoid α]
    [PartialOrder α] [IsOrderedAddMonoid α]
    (M : OrderedAdditiveMeasure textbookSchema α)
    (hattained : ∃ t : TextbookTerm, M.w_succ ≤ M.eval t) :
    ¬ (∀ (b s n : TextbookTerm),
      M.eval (textbookSchema.wrap s (textbookSchema.recur b s n)) <
        M.eval (textbookSchema.recur b s (textbookSchema.succ n))) :=
  no_ordered_additive_orients_dup_step M hattained

/-- The ordered-carrier transparent-compositional barrier at the textbook rule. -/
theorem no_textbook_orientation_ordered_compositional {α : Type*} [Preorder α]
    (M : OrderedCompositionalMeasure textbookSchema α)
    (htrans : M.c_succ M.c_base = M.c_base) :
    ¬ (∀ (b s n : TextbookTerm),
      M.eval (textbookSchema.wrap s (textbookSchema.recur b s n)) <
        M.eval (textbookSchema.recur b s (textbookSchema.succ n))) :=
  no_ordered_compositional_orients_dup_step_transparent M htrans

/-- The nonnegative-rational affine barrier at the textbook rule. -/
theorem no_textbook_orientation_affine_nnrat (M : AffineMeasure textbookSchema) :
    ¬ FieldAffineOrients (fieldAffineMeasureNNRat (S := textbookSchema) M) 1 :=
  no_affine_orients_dup_step_nnrat M

/-- The nonnegative-real affine barrier at the textbook rule. -/
theorem no_textbook_orientation_affine_nnreal (M : AffineMeasure textbookSchema) :
    ¬ FieldAffineOrients (fieldAffineMeasureNNReal (S := textbookSchema) M) 1 :=
  no_affine_orients_dup_step_nnreal M

/-! ## Tier 5: the exact law of the unconstrained nonlinear direct row -/

/-- The exact-law barrier at the textbook rule. -/
theorem no_global_textbook_orientation_unconstrainedDirect
    (L : UnconstrainedDirectLaw textbookSchema) :
    ¬ GlobalOrients textbookSystem L.eval (· < ·) :=
  no_global_orients_unconstrainedDirect (Sys := textbookSystem) L

/-! ## The remark as one theorem -/

/-- Every advertised branch of the textbook instantiation, with exactly the premises of its
schema theorem. This prevents a small unconditional conjunction from being cited as the full
stack. -/
structure TextbookFullBarrierStack : Prop where
  additive : ∀ M : AdditiveMeasure textbookSchema,
    ¬ GlobalOrients textbookSystem M.eval (· < ·)
  compositionalTransparent : ∀ M : CompositionalMeasure textbookSchema,
    M.c_succ M.c_base = M.c_base → ¬ GlobalOrients textbookSystem M.eval (· < ·)
  affine : ∀ M : AffineMeasure textbookSchema,
    ¬ GlobalOrients textbookSystem M.eval (· < ·)
  quadratic : ∀ M : QuadraticCounterMeasure textbookSchema,
    ¬ GlobalOrients textbookSystem M.eval (· < ·)
  crossQuadratic : ∀ M : CrossTermQuadraticMeasure textbookSchema,
    CrossTermBoundedAtBase M → ¬ GlobalOrients textbookSystem M.eval (· < ·)
  crossQuadraticNoCross : ∀ M : CrossTermQuadraticMeasure textbookSchema,
    M.recur_cross = 0 → ¬ GlobalOrients textbookSystem M.eval (· < ·)
  multilinear : ∀ M : BoundedMultilinearMeasure textbookSchema,
    MultilinearDominatedAtBase M → ¬ GlobalOrients textbookSystem M.eval (· < ·)
  multilinearNoCoupling : ∀ M : BoundedMultilinearMeasure textbookSchema,
    NoStepCounterCoupling M → ¬ GlobalOrients textbookSystem M.eval (· < ·)
  polynomial : ∀ M : BoundedPolynomialMeasure textbookSchema,
    EventuallyDominatedAtBase M → ¬ GlobalOrients textbookSystem M.eval (· < ·)
  polynomialNoCounterExponent : ∀ M : BoundedPolynomialMeasure textbookSchema,
    NoCounterExponent M → ¬ GlobalOrients textbookSystem M.eval (· < ·)
  wpoPolynomial : ∀ W : WPOPolynomialDirectOrder textbookSchema,
    EventuallyDominatedAtBase W.measure →
      ¬ GlobalOrients textbookSystem (fun t => t) (fun x y => W.gt y x)
  maxPlus : ∀ M : MaxMeasure textbookSchema,
    ¬ GlobalOrients textbookSystem M.eval (· < ·)
  naturalMatrixTracked : ∀ {d : Nat} (M : NatMatrixMeasure textbookSchema d)
      {i : Fin d}, WrapDiagPositive M i →
      ∀ {R : MatrixVec d → MatrixVec d → Prop},
        (∀ {u v : MatrixVec d}, R u v → u i < v i) →
          ¬ GlobalOrients textbookSystem M.eval R
  naturalMatrixComponentwise : ∀ {d : Nat} (M : NatMatrixMeasure textbookSchema d)
      {i : Fin d}, WrapDiagPositive M i → ¬ GlobalOrients textbookSystem M.eval VecLt
  naturalMatrixLex : ∀ {d : Nat} (M : NatMatrixMeasure textbookSchema (d + 1)),
    WrapDiagPositive M (primaryIdx d) →
      (∃ t : TextbookTerm, 1 ≤ M.eval t (primaryIdx d)) →
        ¬ GlobalOrients textbookSystem M.eval VecLexLt
  naturalMatrixPermLex : ∀ {d : Nat} (σ : Equiv.Perm (Fin (d + 1)))
      (M : NatMatrixMeasure textbookSchema (d + 1)),
    WrapDiagPositive M (permPrimaryIdx σ) →
      (∃ t : TextbookTerm, 1 ≤ M.eval t (permPrimaryIdx σ)) →
        ¬ GlobalOrients textbookSystem M.eval (VecPermLexLt σ)
  ewzMonotone : ∀ {d : Nat} [NeZero d] (M : NatMatrixMeasure textbookSchema d),
    EWZMonotoneInterpretation M → ¬ GlobalOrients textbookSystem M.eval (VecLeLt 0)
  matrixD : ∀ {d : Nat} {tracked : Fin d} (M : MatrixMeasureD textbookSchema d tracked),
    ¬ GlobalOrients textbookSystem M.eval VecLt
  matrix2 : ∀ M : MatrixMeasure2 textbookSchema,
    ¬ GlobalOrients textbookSystem M.eval PairLt
  matrix2Lex : ∀ M : MatrixMeasure2 textbookSchema,
    (∃ t : TextbookTerm, 1 ≤ (M.eval t).1) →
      ¬ GlobalOrients textbookSystem M.eval PairLexLt
  matrixFunctional : ∀ {d : Nat} (M : MatrixFunctionalMeasure textbookSchema d),
    ¬ GlobalOrients textbookSystem M.eval VecLt
  matrixMix2 : ∀ M : MatrixMix2Measure textbookSchema,
    ¬ GlobalOrients textbookSystem M.eval PairLt
  matrixLexD : ∀ {d : Nat} (M : MatrixLexMeasureD textbookSchema d),
    (∃ t : TextbookTerm, 1 ≤ M.eval t (primaryIdx d)) →
      ¬ GlobalOrients textbookSystem M.eval VecLexLt
  matrixLexPermD : ∀ {d : Nat} (M : MatrixLexPermMeasureD textbookSchema d),
    (∃ t : TextbookTerm, 1 ≤ M.eval t (permPrimaryIdx M.priority)) →
      ¬ GlobalOrients textbookSystem M.eval (VecPermLexLt M.priority)
  matrixArbitrary : ∀ {d : Nat} (M : MatrixArbitraryMeasure textbookSchema d)
      {R : MatrixVec d → MatrixVec d → Prop}, MatrixScalarDominance M.weight R →
      (∃ t : TextbookTerm, 1 ≤ matrixScalarize M.weight (M.eval t)) →
        ¬ GlobalOrients textbookSystem M.eval R
  arcticMatrix : ∀ {d : Nat} (M : ArcticNatMatrixMeasure textbookSchema d)
      {i : Fin d}, ArcticWrapDiagFinite M i →
      ∀ {R : ArcticVec d → ArcticVec d → Prop},
        (∀ {u v : ArcticVec d}, R u v → ArcticLt (u i) (v i)) →
          ¬ GlobalOrients textbookSystem M.eval R
  arcticMatrixCertificate : ∀ {d : Nat} (M : ArcticMatrixMeasure textbookSchema d)
      (C : ArcticMatrixCertificate d),
    C.weight = M.scalarMeasure.weight →
      (∀ t : TextbookTerm, C.scalarize (M.eval t) = M.scalarMeasure.eval t) →
        HasUnboundedScalarizedRange M.scalarMeasure →
          ¬ GlobalOrients textbookSystem M.eval C.lt
  tropicalMatrixCertificate : ∀ {d : Nat} (M : TropicalMatrixMeasure textbookSchema d)
      (C : TropicalMatrixCertificate d),
    C.weight = M.scalarMeasure.weight →
      (∀ t : TextbookTerm, C.scalarize (M.eval t) = M.scalarMeasure.eval t) →
        HasUnboundedScalarizedRange M.scalarMeasure →
          ¬ GlobalOrients textbookSystem M.eval C.lt
  orderedAdditive : ∀ {α : Type*} [AddCommMonoid α] [PartialOrder α]
      [IsOrderedAddMonoid α] (M : OrderedAdditiveMeasure textbookSchema α),
      (∃ t : TextbookTerm, M.w_succ ≤ M.eval t) →
        ¬ (∀ b s n : TextbookTerm,
          M.eval (textbookSchema.wrap s (textbookSchema.recur b s n)) <
            M.eval (textbookSchema.recur b s (textbookSchema.succ n)))
  orderedCompositional : ∀ {α : Type*} [Preorder α]
      (M : OrderedCompositionalMeasure textbookSchema α),
      M.c_succ M.c_base = M.c_base →
        ¬ (∀ b s n : TextbookTerm,
          M.eval (textbookSchema.wrap s (textbookSchema.recur b s n)) <
            M.eval (textbookSchema.recur b s (textbookSchema.succ n)))
  affineNNRat : ∀ M : AffineMeasure textbookSchema,
    ¬ FieldAffineOrients (fieldAffineMeasureNNRat (S := textbookSchema) M) 1
  affineNNReal : ∀ M : AffineMeasure textbookSchema,
    ¬ FieldAffineOrients (fieldAffineMeasureNNReal (S := textbookSchema) M) 1
  unconstrainedDirect : ∀ L : UnconstrainedDirectLaw textbookSchema,
    ¬ GlobalOrients textbookSystem L.eval (· < ·)

/-- **The textbook rule carries the complete barrier stack.** -/
theorem textbook_rule_carries_full_barrier_stack : TextbookFullBarrierStack where
  additive := no_global_textbook_orientation_additive
  compositionalTransparent := no_global_textbook_orientation_compositional_transparent_succ
  affine := no_global_textbook_orientation_affine
  quadratic := no_global_textbook_orientation_quadratic
  crossQuadratic := no_global_textbook_orientation_cross_quadratic
  crossQuadraticNoCross := no_global_textbook_orientation_cross_quadratic_of_no_cross
  multilinear := no_global_textbook_orientation_multilinear
  multilinearNoCoupling := no_global_textbook_orientation_multilinear_of_no_coupling
  polynomial := no_global_textbook_orientation_polynomial
  polynomialNoCounterExponent := no_global_textbook_orientation_polynomial_of_no_counter_exponent
  wpoPolynomial := no_global_textbook_orientation_wpoPolynomialDirect
  maxPlus := no_global_textbook_orientation_max
  naturalMatrixTracked := no_global_textbook_orientation_naturalMatrix_of_tracked_strict
  naturalMatrixComponentwise := no_global_textbook_orientation_naturalMatrix_componentwise
  naturalMatrixLex := no_global_textbook_orientation_naturalMatrix_lex
  naturalMatrixPermLex := no_global_textbook_orientation_naturalMatrix_permLex
  ewzMonotone := no_global_textbook_orientation_ewzMonotone
  matrixD := no_global_textbook_orientation_matrixD
  matrix2 := no_global_textbook_orientation_matrix2
  matrix2Lex := no_global_textbook_orientation_matrix2_lex
  matrixFunctional := no_global_textbook_orientation_matrixFunctional
  matrixMix2 := no_global_textbook_orientation_matrixMix2
  matrixLexD := no_global_textbook_orientation_matrixLexD
  matrixLexPermD := no_global_textbook_orientation_matrixLexPermD
  matrixArbitrary := no_global_textbook_orientation_matrixArbitrary
  arcticMatrix := no_global_textbook_orientation_arcticMatrix
  arcticMatrixCertificate := no_global_textbook_orientation_arcticMatrix_certificate
  tropicalMatrixCertificate := no_global_textbook_orientation_tropicalMatrix_certificate
  orderedAdditive := no_textbook_orientation_ordered_additive
  orderedCompositional := no_textbook_orientation_ordered_compositional
  affineNNRat := no_textbook_orientation_affine_nnrat
  affineNNReal := no_textbook_orientation_affine_nnreal
  unconstrainedDirect := no_global_textbook_orientation_unconstrainedDirect

/-- **Full exact textbook boundary.**  The complete barrier stack and the compiled sharpness
witnesses for its three dominance-qualified branches hold on the same textbook TRS. -/
theorem textbook_rule_carries_full_exact_boundary :
    TextbookFullBarrierStack
      ∧ (¬ CrossTermBoundedAtBase textbookCrossCoupledQuadratic
        ∧ GlobalOrients textbookSystem textbookCrossCoupledQuadratic.eval (· < ·))
      ∧ (¬ MultilinearDominatedAtBase textbookCrossCoupledMultilinear
        ∧ GlobalOrients textbookSystem textbookCrossCoupledMultilinear.eval (· < ·))
      ∧ (¬ EventuallyDominatedAtBase textbookCrossCoupledPolynomial
        ∧ GlobalOrients textbookSystem textbookCrossCoupledPolynomial.eval (· < ·)) :=
  ⟨textbook_rule_carries_full_barrier_stack, textbook_three_dominance_premises_are_sharp⟩

end OperatorKO7.TextbookDupInstance
