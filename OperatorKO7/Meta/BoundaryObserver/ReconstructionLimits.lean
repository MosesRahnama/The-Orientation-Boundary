import OperatorKO7.Meta.BoundaryObserver.BoundaryReconstruction
import Mathlib.Analysis.CStarAlgebra.Hom
import Mathlib.Algebra.Colimit.DirectLimit
import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Data.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Calculus.Deriv.Star

/-!
# Controlled limits of finite observation fibers

The initial directed system consists of diagonal finite fiber algebras. It is
a commutative family, not a reconstruction of arbitrary noncommutative matrix
algebras. Each stage map retains every old coordinate and repeats its final
coordinate in new positions.

For an isometric star system, the algebraic direct limit carries the descended
norm, product, scalar action, and adjoint and satisfies the C* norm identity.
The quotient topology of the underlying quotient type is not an instance on
the sealed limit definition. The uniform completion is a C* algebra; each stage
embeds isometrically and coherently, and the joint range is dense. Compatible
normalized positive stage states descend to a positive norm-one functional on
the limit and extend uniquely to a positive normalized state on the completion.
The positive form satisfies Cauchy-Schwarz, and its null space is a left ideal.
-/

set_option autoImplicit false

noncomputable section
open scoped BigOperators Classical ComplexOrder

namespace OperatorKO7.Meta.BoundaryObserver
namespace ReconstructionLimits

/-- One complex coordinate for each singleton observation fiber. -/
abbrev FiniteFiber (n : ℕ) := Fin (n + 1) → ℂ

/-- The canonical unital star embedding repeats the final old coordinate. -/
def stageEmbed (n m : ℕ) (_h : n ≤ m) :
    FiniteFiber n →⋆ₐ[ℂ] FiniteFiber m where
  toFun a i := a ⟨min i.val n, by omega⟩
  map_one' := by
    funext i
    rfl
  map_mul' := by
    intro a b
    funext i
    rfl
  map_zero' := by
    funext i
    rfl
  map_add' := by
    intro a b
    funext i
    rfl
  commutes' := by
    intro c
    funext i
    rfl
  map_star' := by
    intro a
    funext i
    rfl

theorem stageEmbed_self (n : ℕ) (a : FiniteFiber n) :
    stageEmbed n n le_rfl a = a := by
  funext i
  change a ⟨min i.val n, by omega⟩ = a i
  congr 1
  apply Fin.ext
  change min i.val n = i.val
  omega

theorem stageEmbed_comp {n m k : ℕ} (hnm : n ≤ m) (hmk : m ≤ k)
    (a : FiniteFiber n) :
    stageEmbed m k hmk (stageEmbed n m hnm a) =
      stageEmbed n k (hnm.trans hmk) a := by
  funext i
  change a ⟨min (min i.val m) n, by omega⟩ =
    a ⟨min i.val n, by omega⟩
  congr 1
  apply Fin.ext
  change min (min i.val m) n = min i.val n
  omega

theorem stageEmbed_injective {n m : ℕ} (h : n ≤ m) :
    Function.Injective (stageEmbed n m h) := by
  intro a b hab
  funext i
  have hi := congrFun hab (⟨i.val, by omega⟩ : Fin (m + 1))
  have hid : (⟨min i.val n, by omega⟩ : Fin (n + 1)) = i := by
    apply Fin.ext
    change min i.val n = i.val
    omega
  change a ⟨min i.val n, by omega⟩ =
    b ⟨min i.val n, by omega⟩ at hi
  simpa only [hid] using hi

theorem stageEmbed_norm {n m : ℕ} (h : n ≤ m) (a : FiniteFiber n) :
    ‖stageEmbed n m h a‖ = ‖a‖ := by
  exact NonUnitalStarAlgHom.norm_map (stageEmbed n m h)
    (stageEmbed_injective h) a

theorem stageEmbed_star {n m : ℕ} (h : n ≤ m) (a : FiniteFiber n) :
    stageEmbed n m h (star a) = star (stageEmbed n m h a) := by
  exact map_star (stageEmbed n m h) a

/-- The maps form a coherent directed system of finite unital star algebras. -/
instance finiteFiberDirected :
    DirectedSystem FiniteFiber (fun i j h => stageEmbed i j h) where
  map_self := by
    intro i a
    exact stageEmbed_self i a
  map_map := by
    intro k j i hij hjk a
    exact stageEmbed_comp hij hjk a

/-- The algebraic direct limit identifies elements at their common later stage. -/
abbrev FiberAlgebraicLimit : Type :=
  DirectLimit FiniteFiber (fun i j h => stageEmbed i j h)

/-- Every finite stage has a canonical unital ring map into the direct limit. -/
def intoLimit (n : ℕ) : FiniteFiber n →+* FiberAlgebraicLimit :=
  DirectLimit.Ring.of FiniteFiber (fun i j h => stageEmbed i j h) n

theorem intoLimit_compatible {n m : ℕ} (h : n ≤ m) (a : FiniteFiber n) :
    intoLimit m (stageEmbed n m h a) = intoLimit n a := by
  exact DirectLimit.Ring.of_f (f := fun i j h => stageEmbed i j h) h a

theorem intoLimit_injective (n : ℕ) : Function.Injective (intoLimit n) := by
  change Function.Injective (fun a : FiniteFiber n =>
    (⟦⟨n, a⟩⟧ : DirectLimit FiniteFiber (fun i j h => stageEmbed i j h)))
  exact DirectLimit.mk_injective
    (f := fun i j h => stageEmbed i j h)
    (fun i j h => stageEmbed_injective h) n

/-- Coherence, isometry, and faithfulness form the first operator-limit license. -/
def DirectedFiberAlgebraGoal : Prop :=
  (∀ n m (h : n ≤ m), Function.Injective (stageEmbed n m h)) ∧
  (∀ n m (h : n ≤ m) (a : FiniteFiber n),
    ‖stageEmbed n m h a‖ = ‖a‖) ∧
  (∀ n, Function.Injective (intoLimit n)) ∧
  (∀ n m (h : n ≤ m) (a : FiniteFiber n),
    intoLimit m (stageEmbed n m h a) = intoLimit n a)

theorem directedFiberAlgebraGoal : DirectedFiberAlgebraGoal := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro n m h
    exact stageEmbed_injective h
  · intro n m h a
    exact stageEmbed_norm h a
  · intro n
    exact intoLimit_injective n
  · intro n m h a
    exact intoLimit_compatible h a

/-! ### M5.7: a compatible positive normalized limit state -/

/-- Evaluation on the first retained fiber is a unital complex star-algebra map. -/
def stageState (n : ℕ) : FiniteFiber n →⋆ₐ[ℂ] ℂ :=
  Pi.evalStarAlgHom ℂ (fun _ : Fin (n + 1) => ℂ) 0

theorem stageState_compatible {n m : ℕ} (h : n ≤ m) (a : FiniteFiber n) :
    stageState m (stageEmbed n m h a) = stageState n a := by
  change a ⟨min (0 : ℕ) n, by omega⟩ = a (0 : Fin (n + 1))
  congr 1
  apply Fin.ext
  change min 0 n = (0 : ℕ)
  omega

theorem stageState_positive (n : ℕ) (a : FiniteFiber n) :
    0 ≤ ((stageState n) (star a * a)).re := by
  change 0 ≤ (star (a (0 : Fin (n + 1))) * a 0).re
  rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self]
  exact Complex.normSq_nonneg (a 0)

theorem stageState_norm_le (n : ℕ) (a : FiniteFiber n) :
    ‖stageState n a‖ ≤ ‖a‖ := by
  change ‖a (0 : Fin (n + 1))‖ ≤ ‖a‖
  exact norm_le_pi_norm a 0

/-- The compatible family descends to one unital functional on the algebraic limit. -/
def limitState : FiberAlgebraicLimit →+* ℂ :=
  DirectLimit.Ring.lift FiniteFiber
    (fun i j h => stageEmbed i j h) ℂ
    (fun n => (stageState n).toAlgHom.toRingHom)
    (by
      intro n m h a
      exact stageState_compatible h a)

theorem limitState_of (n : ℕ) (a : FiniteFiber n) :
    limitState (intoLimit n a) = stageState n a := by
  rfl

/-- A well-defined adjoint is obtained on representatives and respects the embeddings. -/
def limitAdjoint : FiberAlgebraicLimit → FiberAlgebraicLimit :=
  DirectLimit.map
    (f₁ := fun i j h => stageEmbed i j h)
    (f₂ := fun i j h => stageEmbed i j h)
    (fun n (a : FiniteFiber n) => star a)
    (by
      intro n m h a
      exact stageEmbed_star h a)

theorem limitAdjoint_of (n : ℕ) (a : FiniteFiber n) :
    limitAdjoint (intoLimit n a) = intoLimit n (star a) := by
  rfl

theorem limitAdjoint_involutive (z : FiberAlgebraicLimit) :
    limitAdjoint (limitAdjoint z) = z := by
  refine DirectLimit.induction
    (f := fun i j h => stageEmbed i j h) ?_ z
  intro n a
  change limitAdjoint (limitAdjoint (intoLimit n a)) = intoLimit n a
  rw [limitAdjoint_of, limitAdjoint_of, star_star]

theorem limitAdjoint_add (x y : FiberAlgebraicLimit) :
    limitAdjoint (x + y) = limitAdjoint x + limitAdjoint y := by
  refine DirectLimit.induction₂
    (f := fun i j h => stageEmbed i j h) ?_ x y
  intro n a b
  change limitAdjoint (intoLimit n a + intoLimit n b) =
    limitAdjoint (intoLimit n a) + limitAdjoint (intoLimit n b)
  rw [← map_add (intoLimit n) a b, limitAdjoint_of, star_add,
    map_add, limitAdjoint_of, limitAdjoint_of]

theorem limitAdjoint_mul (x y : FiberAlgebraicLimit) :
    limitAdjoint (x * y) = limitAdjoint y * limitAdjoint x := by
  refine DirectLimit.induction₂
    (f := fun i j h => stageEmbed i j h) ?_ x y
  intro n a b
  change limitAdjoint (intoLimit n a * intoLimit n b) =
    limitAdjoint (intoLimit n b) * limitAdjoint (intoLimit n a)
  rw [← map_mul (intoLimit n) a b, limitAdjoint_of, star_mul,
    map_mul, limitAdjoint_of, limitAdjoint_of]

theorem limitState_adjoint (z : FiberAlgebraicLimit) :
    limitState (limitAdjoint z) = star (limitState z) := by
  refine DirectLimit.induction
    (f := fun i j h => stageEmbed i j h) ?_ z
  intro n a
  change limitState (limitAdjoint (intoLimit n a)) = star (limitState (intoLimit n a))
  rw [limitAdjoint_of, limitState_of, limitState_of]
  exact map_star (stageState n) a

theorem limitState_positive (z : FiberAlgebraicLimit) :
    0 ≤ (limitState (limitAdjoint z * z)).re := by
  refine DirectLimit.induction
    (f := fun i j h => stageEmbed i j h) ?_ z
  intro n a
  change 0 ≤ (limitState (limitAdjoint (intoLimit n a) * intoLimit n a)).re
  rw [limitAdjoint_of, ← map_mul (intoLimit n) (star a) a, limitState_of]
  exact stageState_positive n a

/-- The finite-stage isometries make the supremum norm independent of representatives. -/
def limitSize : FiberAlgebraicLimit → ℝ :=
  DirectLimit.lift
    (f := fun i j h => stageEmbed i j h)
    (fun n (a : FiniteFiber n) => ‖a‖)
    (by
      intro n m h a
      exact (stageEmbed_norm h a).symm)

theorem limitSize_of (n : ℕ) (a : FiniteFiber n) :
    limitSize (intoLimit n a) = ‖a‖ := by
  rfl

theorem limitSize_nonneg (z : FiberAlgebraicLimit) : 0 ≤ limitSize z := by
  refine DirectLimit.induction
    (f := fun i j h => stageEmbed i j h) ?_ z
  intro n a
  rw [show (⟦⟨n, a⟩⟧ : FiberAlgebraicLimit) = intoLimit n a from rfl,
    limitSize_of]
  exact norm_nonneg a

theorem limitState_norm_le (z : FiberAlgebraicLimit) :
    ‖limitState z‖ ≤ limitSize z := by
  refine DirectLimit.induction
    (f := fun i j h => stageEmbed i j h) ?_ z
  intro n a
  change ‖limitState (intoLimit n a)‖ ≤ limitSize (intoLimit n a)
  rw [limitState_of, limitSize_of]
  exact stageState_norm_le n a

theorem limitSize_one : limitSize (1 : FiberAlgebraicLimit) = 1 := by
  have h : (1 : FiberAlgebraicLimit) = intoLimit 0 (1 : FiniteFiber 0) :=
    (map_one (intoLimit 0)).symm
  rw [h, limitSize_of, norm_one]

/-- Positivity, normalization and the sharp norm-one bound hold on the actual limit. -/
def PositiveNormalizedLimitStateGoal : Prop :=
  (∀ z, limitAdjoint (limitAdjoint z) = z) ∧
  (∀ x y, limitAdjoint (x + y) = limitAdjoint x + limitAdjoint y) ∧
  (∀ x y, limitAdjoint (x * y) = limitAdjoint y * limitAdjoint x) ∧
  limitState 1 = 1 ∧
  (∀ z, 0 ≤ (limitState (limitAdjoint z * z)).re) ∧
  (∀ z, ‖limitState z‖ ≤ limitSize z) ∧
  limitSize 1 = 1 ∧
  (∀ n a, limitState (intoLimit n a) = stageState n a)

theorem positiveNormalizedLimitStateGoal : PositiveNormalizedLimitStateGoal := by
  refine ⟨limitAdjoint_involutive, limitAdjoint_add, limitAdjoint_mul,
    map_one limitState, limitState_positive, limitState_norm_le,
    limitSize_one, limitState_of⟩

/-! ### M5.7: explicit null quotient and GNS representation for the limit state -/

/-- The positive sesquilinear form induced by the actual direct-limit state. -/
def stateForm (a b : FiberAlgebraicLimit) : ℂ :=
  limitState (limitAdjoint a * b)

theorem stateForm_eq (a b : FiberAlgebraicLimit) :
    stateForm a b = star (limitState a) * limitState b := by
  simp only [stateForm, map_mul, limitState_adjoint]

theorem stateForm_nonneg (a : FiberAlgebraicLimit) :
    0 ≤ (stateForm a a).re :=
  limitState_positive a

/-- The form's null space is not postulated: it is its zero-square locus. -/
def stateNull (a : FiberAlgebraicLimit) : Prop := stateForm a a = 0

theorem stateNull_iff (a : FiberAlgebraicLimit) :
    stateNull a ↔ limitState a = 0 := by
  rw [stateNull, stateForm_eq]
  constructor
  · intro h
    rcases mul_eq_zero.mp h with hstar | hz
    · have hz := congrArg star hstar
      simpa only [star_star, star_zero] using hz
    · exact hz
  · intro h
    rw [h, star_zero, zero_mul]

theorem stateNull_leftIdeal (a b : FiberAlgebraicLimit)
    (hb : stateNull b) : stateNull (a * b) := by
  apply (stateNull_iff (a * b)).2
  rw [map_mul, (stateNull_iff b).1 hb, mul_zero]

theorem stateNull_add (a b : FiberAlgebraicLimit)
    (ha : stateNull a) (hb : stateNull b) : stateNull (a + b) := by
  apply (stateNull_iff (a + b)).2
  rw [map_add, (stateNull_iff a).1 ha, (stateNull_iff b).1 hb, add_zero]

theorem stateForm_null_left (a b : FiberAlgebraicLimit)
    (ha : stateNull a) : stateForm a b = 0 := by
  rw [stateForm_eq, (stateNull_iff a).1 ha, star_zero, zero_mul]

theorem stateForm_null_right (a b : FiberAlgebraicLimit)
    (hb : stateNull b) : stateForm a b = 0 := by
  rw [stateForm_eq, (stateNull_iff b).1 hb, mul_zero]

/-- Equality modulo the proved null space is equality of state evaluations. -/
def stateSetoid : Setoid FiberAlgebraicLimit where
  r a b := limitState a = limitState b
  iseqv := ⟨fun _ => rfl,
    fun {a b} (h : limitState a = limitState b) => h.symm,
    fun {a b c} (h : limitState a = limitState b)
      (k : limitState b = limitState c) => h.trans k⟩

/-- The concrete GNS quotient is formed before its Hilbert completion. -/
abbrev StateQuotient : Type := Quotient stateSetoid

def stateClass (a : FiberAlgebraicLimit) : StateQuotient :=
  Quotient.mk stateSetoid a

/-- The quotient evaluation is independent of every representative. -/
def quotientEvaluation : StateQuotient → ℂ :=
  fun x => Quotient.liftOn x limitState (by
    intro a b h
    exact h)

theorem quotientEvaluation_class (a : FiberAlgebraicLimit) :
    quotientEvaluation (stateClass a) = limitState a := rfl

theorem quotientEvaluation_injective :
    Function.Injective quotientEvaluation := by
  intro x y h
  revert h
  refine Quotient.inductionOn₂ x y ?_
  intro a b hab
  exact Quotient.sound hab

theorem quotientEvaluation_surjective :
    Function.Surjective quotientEvaluation := by
  intro z
  refine ⟨stateClass (intoLimit 0 (fun _ => z)), ?_⟩
  change limitState (intoLimit 0 (fun _ => z)) = z
  rw [limitState_of]
  change z = z
  rfl

/-- The quotient inner product descends directly from the positive functional. -/
def quotientForm (x y : StateQuotient) : ℂ :=
  Quotient.liftOn₂ x y stateForm (by
    intro a a' b b' ha hb
    rw [stateForm_eq, stateForm_eq, ha, hb])

theorem quotientForm_class (a b : FiberAlgebraicLimit) :
    quotientForm (stateClass a) (stateClass b) = stateForm a b := rfl

theorem quotientForm_eval (x y : StateQuotient) :
    quotientForm x y =
      star (quotientEvaluation x) * quotientEvaluation y := by
  refine Quotient.inductionOn₂ x y ?_
  intro a b
  exact stateForm_eq a b

/-- Scalar inner products in the completed Hilbert carrier have this explicit orientation. -/
theorem scalarInner (x y : ℂ) : inner ℂ x y = star x * y := by
  have h11 : inner ℂ (1 : ℂ) (1 : ℂ) = 1 := by
    rw [inner_self_eq_norm_sq_to_K]
    norm_num
  calc
    inner ℂ x y = inner ℂ (x • (1 : ℂ)) (y • (1 : ℂ)) := by
      simp only [smul_eq_mul, mul_one]
    _ = star x * (y * inner ℂ (1 : ℂ) (1 : ℂ)) := by
      rw [inner_smul_left, inner_smul_right, starRingEnd_apply]
    _ = star x * y := by
      rw [h11]
      ring

theorem quotientForm_inner (x y : StateQuotient) :
    quotientForm x y =
      inner ℂ (quotientEvaluation x) (quotientEvaluation y) := by
  rw [quotientForm_eval, scalarInner]

theorem quotientForm_cauchySchwarz (x y : StateQuotient) :
    ‖quotientForm x y‖ * ‖quotientForm y x‖ ≤
      (quotientForm x x).re * (quotientForm y y).re := by
  simp only [quotientForm_inner]
  exact inner_mul_inner_self_le (𝕜 := ℂ) (quotientEvaluation x) (quotientEvaluation y)

theorem quotientForm_positive (x : StateQuotient) :
    0 ≤ (quotientForm x x).re := by
  rw [quotientForm_inner]
  exact inner_self_nonneg (𝕜 := ℂ) (x := quotientEvaluation x)

theorem quotientForm_definite (x : StateQuotient)
    (hx : quotientForm x x = 0) :
    x = stateClass 0 := by
  apply quotientEvaluation_injective
  rw [quotientForm_inner] at hx
  have hz : quotientEvaluation x = 0 :=
    (inner_self_eq_zero (𝕜 := ℂ)).1 hx
  rw [hz]
  change (0 : ℂ) = limitState 0
  rw [map_zero]

/-- The null quotient has an explicit, onto, inner-product-preserving Hilbert model. -/
abbrev GNSHilbert : Type := ℂ

theorem gnsHilbert_complete : CompleteSpace GNSHilbert := inferInstance

theorem quotientHilbert_bijective :
    Function.Bijective (quotientEvaluation : StateQuotient → GNSHilbert) :=
  ⟨quotientEvaluation_injective, quotientEvaluation_surjective⟩

/-- Left multiplication on the quotient is defined with the full null-ideal proof. -/
def quotientAction (a : FiberAlgebraicLimit) (x : StateQuotient) : StateQuotient :=
  Quotient.liftOn x (fun b => stateClass (a * b)) (by
    intro b c h
    apply Quotient.sound
    change limitState (a * b) = limitState (a * c)
    rw [map_mul, map_mul, h])

theorem quotientAction_class (a b : FiberAlgebraicLimit) :
    quotientAction a (stateClass b) = stateClass (a * b) := rfl

theorem quotientAction_one (x : StateQuotient) :
    quotientAction 1 x = x := by
  refine Quotient.inductionOn x ?_
  intro b
  change stateClass (1 * b) = stateClass b
  rw [one_mul]

theorem quotientAction_mul (a b : FiberAlgebraicLimit) (x : StateQuotient) :
    quotientAction (a * b) x = quotientAction a (quotientAction b x) := by
  refine Quotient.inductionOn x ?_
  intro c
  change stateClass ((a * b) * c) = stateClass (a * (b * c))
  rw [mul_assoc]

theorem quotientAction_cyclic (x : StateQuotient) :
    ∃ a : FiberAlgebraicLimit, quotientAction a (stateClass 1) = x := by
  refine Quotient.inductionOn x ?_
  intro a
  refine ⟨a, ?_⟩
  change stateClass (a * 1) = stateClass a
  rw [mul_one]

theorem quotientAction_evaluation (a : FiberAlgebraicLimit) (x : StateQuotient) :
    quotientEvaluation (quotientAction a x) =
      limitState a * quotientEvaluation x := by
  refine Quotient.inductionOn x ?_
  intro b
  change limitState (a * b) = limitState a * limitState b
  rw [map_mul]

/-- The actual bounded Hilbert-space action is multiplication by the state character. -/
def representationLinear (a : FiberAlgebraicLimit) : ℂ →ₗ[ℂ] ℂ where
  toFun z := limitState a * z
  map_add' x y := by
    exact mul_add _ _ _
  map_smul' c z := by
    change limitState a * (c * z) = c * (limitState a * z)
    ring

def gnsRepresentation (a : FiberAlgebraicLimit) : GNSHilbert →L[ℂ] GNSHilbert :=
  (representationLinear a).mkContinuous ‖limitState a‖ (by
    intro z
    change ‖limitState a * z‖ ≤ ‖limitState a‖ * ‖z‖
    rw [norm_mul])

theorem gnsRepresentation_apply (a : FiberAlgebraicLimit) (z : GNSHilbert) :
    gnsRepresentation a z = limitState a * z := rfl

theorem gnsRepresentation_one (z : GNSHilbert) :
    gnsRepresentation 1 z = z := by
  rw [gnsRepresentation_apply, map_one, one_mul]

theorem gnsRepresentation_mul (a b : FiberAlgebraicLimit) (z : GNSHilbert) :
    gnsRepresentation (a * b) z =
      gnsRepresentation a (gnsRepresentation b z) := by
  rw [gnsRepresentation_apply, gnsRepresentation_apply, gnsRepresentation_apply,
    map_mul, mul_assoc]

theorem gnsRepresentation_adjoint (a : FiberAlgebraicLimit) (x y : GNSHilbert) :
    inner ℂ (gnsRepresentation a x) y =
      inner ℂ x (gnsRepresentation (limitAdjoint a) y) := by
  rw [gnsRepresentation_apply, gnsRepresentation_apply, limitState_adjoint,
    scalarInner, scalarInner, star_mul]
  ring

theorem gnsRepresentation_bound (a : FiberAlgebraicLimit) (z : GNSHilbert) :
    ‖gnsRepresentation a z‖ ≤ limitSize a * ‖z‖ := by
  calc
    ‖gnsRepresentation a z‖ = ‖limitState a‖ * ‖z‖ := by
      rw [gnsRepresentation_apply, norm_mul]
    _ ≤ limitSize a * ‖z‖ :=
      mul_le_mul_of_nonneg_right (limitState_norm_le a) (norm_nonneg z)

theorem gnsRepresentation_intertwines (a : FiberAlgebraicLimit) (x : StateQuotient) :
    quotientEvaluation (quotientAction a x) =
      gnsRepresentation a (quotientEvaluation x) := by
  rw [gnsRepresentation_apply, quotientAction_evaluation]

theorem gnsRepresentation_cyclic (z : GNSHilbert) :
    ∃ a : FiberAlgebraicLimit, gnsRepresentation a (1 : GNSHilbert) = z := by
  refine ⟨intoLimit 0 (fun _ => z), ?_⟩
  rw [gnsRepresentation_apply, limitState_of]
  change z * 1 = z
  exact mul_one z

/-- Full GNS construction for the declared positive normalized character.
The quotient is the form's null quotient, and its exact Hilbert model is complex one-space. -/
def CharacterGNSGoal : Prop :=
  (∀ a b, stateNull b → stateNull (a * b)) ∧
  (∀ a, stateNull a ↔ limitState a = 0) ∧
  Function.Bijective quotientEvaluation ∧
  (∀ x y, quotientForm x y =
    inner ℂ (quotientEvaluation x) (quotientEvaluation y)) ∧
  (∀ x y, ‖quotientForm x y‖ * ‖quotientForm y x‖ ≤
    (quotientForm x x).re * (quotientForm y y).re) ∧
  (∀ x, 0 ≤ (quotientForm x x).re) ∧
  (∀ x, quotientForm x x = 0 → x = stateClass 0) ∧
  (∀ a x, quotientEvaluation (quotientAction a x) =
    gnsRepresentation a (quotientEvaluation x)) ∧
  (∀ a b z, gnsRepresentation (a * b) z =
    gnsRepresentation a (gnsRepresentation b z)) ∧
  (∀ a x y, inner ℂ (gnsRepresentation a x) y =
    inner ℂ x (gnsRepresentation (limitAdjoint a) y)) ∧
  (∀ a z, ‖gnsRepresentation a z‖ ≤ limitSize a * ‖z‖) ∧
  (∀ x, ∃ a, quotientAction a (stateClass 1) = x)

theorem characterGNSGoal : CharacterGNSGoal := by
  refine ⟨stateNull_leftIdeal, stateNull_iff,
    quotientHilbert_bijective, quotientForm_inner, quotientForm_cauchySchwarz,
    quotientForm_positive, quotientForm_definite, gnsRepresentation_intertwines,
    gnsRepresentation_mul, gnsRepresentation_adjoint, gnsRepresentation_bound,
    quotientAction_cyclic⟩

/-! ### M5.7-D: compatible finite flow, exact GNS lift, bounded unitary dynamics, failure control -/

/-- The compatible source star automorphism is the identity at each real time. -/
def finiteFlow (_t : ℝ) (n : ℕ) : FiniteFiber n →⋆ₐ[ℂ] FiniteFiber n :=
  StarAlgHom.id ℂ (FiniteFiber n)

theorem finiteFlow_apply (t : ℝ) (n : ℕ) (a : FiniteFiber n) :
    finiteFlow t n a = a := rfl

theorem finiteFlow_add (s t : ℝ) (n : ℕ) (a : FiniteFiber n) :
    finiteFlow (s + t) n a = finiteFlow s n (finiteFlow t n a) := rfl

theorem finiteFlow_embed (t : ℝ) {n m : ℕ} (h : n ≤ m) (a : FiniteFiber n) :
    stageEmbed n m h (finiteFlow t n a) =
      finiteFlow t m (stageEmbed n m h a) := rfl

theorem finiteFlow_state (t : ℝ) (n : ℕ) (a : FiniteFiber n) :
    stageState n (finiteFlow t n a) = stageState n a := rfl

theorem finiteFlow_norm (t : ℝ) (n : ℕ) (a : FiniteFiber n) :
    ‖finiteFlow t n a‖ = ‖a‖ := rfl

theorem finiteFlow_continuous (n : ℕ) (a : FiniteFiber n) :
    Continuous (fun t : ℝ => finiteFlow t n a) := by
  change Continuous (fun _ : ℝ => a)
  exact continuous_const

/-- Directed compatibility produces an actual algebraic-limit map. -/
def limitFlow (t : ℝ) : FiberAlgebraicLimit → FiberAlgebraicLimit :=
  DirectLimit.map
    (f₁ := fun i j h => stageEmbed i j h)
    (f₂ := fun i j h => stageEmbed i j h)
    (fun n (a : FiniteFiber n) => finiteFlow t n a)
    (by intro i j h a; exact finiteFlow_embed t h a)

theorem limitFlow_of (t : ℝ) (n : ℕ) (a : FiniteFiber n) :
    limitFlow t (intoLimit n a) = intoLimit n (finiteFlow t n a) := rfl

theorem limitFlow_eq_id (t : ℝ) (a : FiberAlgebraicLimit) :
    limitFlow t a = a := by
  refine DirectLimit.induction
    (f := fun i j h => stageEmbed i j h) ?_ a
  intro n z
  change limitFlow t (intoLimit n z) = intoLimit n z
  rw [limitFlow_of, finiteFlow_apply]

theorem limitFlow_group (s t : ℝ) (a : FiberAlgebraicLimit) :
    limitFlow (s + t) a = limitFlow s (limitFlow t a) := by
  rw [limitFlow_eq_id, limitFlow_eq_id, limitFlow_eq_id]

theorem limitFlow_state (t : ℝ) (a : FiberAlgebraicLimit) :
    limitState (limitFlow t a) = limitState a := by
  rw [limitFlow_eq_id]

theorem limitFlow_size (t : ℝ) (a : FiberAlgebraicLimit) :
    limitSize (limitFlow t a) = limitSize a := by
  rw [limitFlow_eq_id]

theorem limitFlow_star (t : ℝ) (a : FiberAlgebraicLimit) :
    limitFlow t (limitAdjoint a) = limitAdjoint (limitFlow t a) := by
  rw [limitFlow_eq_id, limitFlow_eq_id]

theorem limitFlow_null (t : ℝ) (a : FiberAlgebraicLimit) :
    stateNull (limitFlow t a) ↔ stateNull a := by
  rw [limitFlow_eq_id]

/-- Null-space invariance proves descent to the GNS quotient. -/
def quotientFlow (t : ℝ) (x : StateQuotient) : StateQuotient :=
  Quotient.liftOn x (fun a => stateClass (limitFlow t a)) (by
    intro a b h
    apply Quotient.sound
    change limitState (limitFlow t a) = limitState (limitFlow t b)
    simpa only [limitFlow_eq_id] using h)

theorem quotientFlow_class (t : ℝ) (a : FiberAlgebraicLimit) :
    quotientFlow t (stateClass a) = stateClass (limitFlow t a) := rfl

theorem quotientFlow_eq_id (t : ℝ) (x : StateQuotient) :
    quotientFlow t x = x := by
  refine Quotient.inductionOn x ?_
  intro a
  change stateClass (limitFlow t a) = stateClass a
  rw [limitFlow_eq_id]

theorem quotientFlow_inner (t : ℝ) (x y : StateQuotient) :
    quotientForm (quotientFlow t x) (quotientFlow t y) = quotientForm x y := by
  rw [quotientFlow_eq_id, quotientFlow_eq_id]

/-- The quotient image equals the entire Hilbert carrier and is therefore dense. -/
theorem quotientRange_dense :
    Dense (Set.range (quotientEvaluation : StateQuotient → GNSHilbert)) := by
  have h : Set.range (quotientEvaluation : StateQuotient → GNSHilbert) = Set.univ :=
    Set.range_eq_univ.mpr quotientEvaluation_surjective
  rw [h]
  exact dense_univ

/-- The canonical state-preserving implementation fixes the cyclic vector. -/
def canonicalGNSFlow (_t : ℝ) : GNSHilbert →L[ℂ] GNSHilbert :=
  ContinuousLinearMap.id ℂ GNSHilbert

theorem canonicalGNSFlow_apply (t : ℝ) (z : GNSHilbert) :
    canonicalGNSFlow t z = z := rfl

theorem canonicalGNSFlow_intertwines (t : ℝ) (x : StateQuotient) :
    canonicalGNSFlow t (quotientEvaluation x) =
      quotientEvaluation (quotientFlow t x) := by
  rw [canonicalGNSFlow_apply, quotientFlow_eq_id]

theorem canonicalGNSFlow_unique (t : ℝ) (F : GNSHilbert →L[ℂ] GNSHilbert)
    (h : ∀ x : StateQuotient,
      F (quotientEvaluation x) = quotientEvaluation (quotientFlow t x)) :
    F = canonicalGNSFlow t := by
  refine ContinuousLinearMap.ext (fun z => ?_)
  obtain ⟨x, rfl⟩ := quotientEvaluation_surjective z
  rw [canonicalGNSFlow_apply, h, quotientFlow_eq_id]

theorem canonicalGNSFlow_group (s t : ℝ) (z : GNSHilbert) :
    canonicalGNSFlow (s + t) z =
      canonicalGNSFlow s (canonicalGNSFlow t z) := rfl

theorem canonicalGNSFlow_inner (t : ℝ) (x y : GNSHilbert) :
    inner ℂ (canonicalGNSFlow t x) (canonicalGNSFlow t y) =
      inner ℂ x y := rfl

theorem canonicalGNSFlow_continuous (z : GNSHilbert) :
    Continuous (fun t : ℝ => canonicalGNSFlow t z) := by
  change Continuous (fun _ : ℝ => z)
  exact continuous_const

theorem canonicalGNSFlow_covariant (t : ℝ) (a : FiberAlgebraicLimit)
    (z : GNSHilbert) :
    canonicalGNSFlow t (gnsRepresentation a z) =
      gnsRepresentation (limitFlow t a) (canonicalGNSFlow t z) := by
  rw [canonicalGNSFlow_apply, canonicalGNSFlow_apply, limitFlow_eq_id]

/-- A separate scalar phase gives a nontrivial bounded unitary implementer. -/
def scalarPhase (t : ℝ) : ℂ := Complex.exp (t • Complex.I)

theorem scalarPhase_zero : scalarPhase 0 = 1 := by
  simp only [scalarPhase, zero_smul, Complex.exp_zero]

theorem scalarPhase_add (s t : ℝ) :
    scalarPhase (s + t) = scalarPhase s * scalarPhase t := by
  simp only [scalarPhase, add_smul, Complex.exp_add]

theorem scalarPhase_norm (t : ℝ) : ‖scalarPhase t‖ = 1 := by
  simpa only [scalarPhase, Complex.real_smul] using
    Complex.norm_exp_ofReal_mul_I t

theorem scalarPhase_star_mul (t : ℝ) :
    star (scalarPhase t) * scalarPhase t = 1 := by
  rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self,
    Complex.normSq_eq_norm_sq, scalarPhase_norm]
  norm_num

theorem scalarPhase_continuous : Continuous scalarPhase := by
  unfold scalarPhase
  exact Complex.continuous_exp.comp (continuous_id.smul continuous_const)

theorem scalarPhase_derivative (t : ℝ) :
    HasDerivAt scalarPhase (Complex.exp (t • Complex.I) * Complex.I) t := by
  have hlin : HasDerivAt (fun s : ℝ => s • (Complex.I : ℂ)) Complex.I t := by
    simpa only [one_smul] using
      (hasDerivAt_id' (x := t)).smul_const (Complex.I : ℂ)
  exact hlin.cexp

theorem scalarPhase_pi : scalarPhase Real.pi = -1 := by
  simp only [scalarPhase, Complex.real_smul, Complex.exp_mul_I,
    Complex.cos_pi, Complex.sin_pi, zero_mul, add_zero]

def scalarPhaseElement (t : ℝ) : FiberAlgebraicLimit :=
  intoLimit 0 (fun _ : Fin 1 => scalarPhase t)

def boundedPhaseFlow (t : ℝ) : GNSHilbert →L[ℂ] GNSHilbert :=
  gnsRepresentation (scalarPhaseElement t)

theorem boundedPhaseFlow_apply (t : ℝ) (z : GNSHilbert) :
    boundedPhaseFlow t z = scalarPhase t * z := by
  rw [boundedPhaseFlow, gnsRepresentation_apply,
    scalarPhaseElement, limitState_of]
  rfl

theorem boundedPhaseFlow_zero (z : GNSHilbert) :
    boundedPhaseFlow 0 z = z := by
  rw [boundedPhaseFlow_apply, scalarPhase_zero, one_mul]

theorem boundedPhaseFlow_add (s t : ℝ) (z : GNSHilbert) :
    boundedPhaseFlow (s + t) z =
      boundedPhaseFlow s (boundedPhaseFlow t z) := by
  rw [boundedPhaseFlow_apply, boundedPhaseFlow_apply,
    boundedPhaseFlow_apply, scalarPhase_add, mul_assoc]

theorem boundedPhaseFlow_inv (t : ℝ) (z : GNSHilbert) :
    boundedPhaseFlow (-t) (boundedPhaseFlow t z) = z := by
  rw [← boundedPhaseFlow_add, neg_add_cancel, boundedPhaseFlow_zero]

theorem boundedPhaseFlow_norm (t : ℝ) (z : GNSHilbert) :
    ‖boundedPhaseFlow t z‖ = ‖z‖ := by
  rw [boundedPhaseFlow_apply, norm_mul, scalarPhase_norm, one_mul]

theorem boundedPhaseFlow_inner (t : ℝ) (x y : GNSHilbert) :
    inner ℂ (boundedPhaseFlow t x) (boundedPhaseFlow t y) =
      inner ℂ x y := by
  rw [boundedPhaseFlow_apply, boundedPhaseFlow_apply,
    scalarInner, scalarInner, star_mul]
  calc
    star x * star (scalarPhase t) * (scalarPhase t * y) =
        (star (scalarPhase t) * scalarPhase t) * (star x * y) := by ring
    _ = star x * y := by rw [scalarPhase_star_mul, one_mul]

theorem boundedPhaseFlow_continuous (z : GNSHilbert) :
    Continuous (fun t : ℝ => boundedPhaseFlow t z) := by
  have h : Continuous (fun t : ℝ => scalarPhase t * z) :=
    scalarPhase_continuous.mul continuous_const
  simpa only [boundedPhaseFlow_apply] using h

theorem boundedPhaseFlow_covariant (t : ℝ) (a : FiberAlgebraicLimit)
    (z : GNSHilbert) :
    boundedPhaseFlow t (gnsRepresentation a z) =
      gnsRepresentation (limitFlow t a) (boundedPhaseFlow t z) := by
  rw [limitFlow_eq_id, boundedPhaseFlow_apply, boundedPhaseFlow_apply,
    gnsRepresentation_apply, gnsRepresentation_apply]
  ring

/-- The bounded Hamiltonian has the full Hilbert carrier as its domain. -/
def boundedHamiltonian : GNSHilbert →L[ℂ] GNSHilbert :=
  ContinuousLinearMap.id ℂ GNSHilbert

theorem boundedHamiltonian_apply (z : GNSHilbert) : boundedHamiltonian z = z := rfl

def boundedGeneratorDomain : Set GNSHilbert := Set.univ

theorem boundedGeneratorDomain_dense : Dense boundedGeneratorDomain := dense_univ

theorem boundedPhaseFlow_hasDerivAt (t : ℝ) (z : GNSHilbert) :
    HasDerivAt (fun s : ℝ => boundedPhaseFlow s z)
      (Complex.I * boundedPhaseFlow t z) t := by
  have hfun : (fun s : ℝ => boundedPhaseFlow s z) = fun s => scalarPhase s * z := by
    funext s
    exact boundedPhaseFlow_apply s z
  have hval : Complex.I * boundedPhaseFlow t z =
      Complex.exp (t • Complex.I) * Complex.I * z := by
    rw [boundedPhaseFlow_apply, scalarPhase]
    ring
  rw [hfun, hval]
  exact (scalarPhase_derivative t).mul_const z

theorem boundedPhaseFlow_generatorEquation (t : ℝ) (z : GNSHilbert) :
    HasDerivAt (fun s : ℝ => boundedPhaseFlow s z)
      (Complex.I * boundedHamiltonian (boundedPhaseFlow t z)) t := by
  simpa only [boundedHamiltonian_apply] using boundedPhaseFlow_hasDerivAt t z

theorem boundedPhaseFlow_nontrivial :
    boundedPhaseFlow Real.pi (1 : GNSHilbert) ≠
      canonicalGNSFlow Real.pi (1 : GNSHilbert) := by
  intro h
  have hbad : (-1 : ℂ) = 1 := by
    simpa only [boundedPhaseFlow_apply, scalarPhase_pi, neg_one_mul,
      canonicalGNSFlow_apply] using h
  norm_num at hbad

/-- A separate admissible finite star automorphism violates stage compatibility. -/
def incompatibleStageTwo : FiniteFiber 2 →⋆ₐ[ℂ] FiniteFiber 2 where
  toFun a i := a (if i = 0 then 1 else if i = 1 then 0 else 2)
  map_one' := by funext i; rfl
  map_mul' := by intro a b; funext i; rfl
  map_zero' := by funext i; rfl
  map_add' := by intro a b; funext i; rfl
  commutes' := by intro c; funext i; rfl
  map_star' := by intro a; funext i; rfl

theorem incompatibleStageTwo_involutive (a : FiniteFiber 2) :
    incompatibleStageTwo (incompatibleStageTwo a) = a := by
  funext i
  fin_cases i <;> rfl

theorem incompatibleStageTwo_bijective :
    Function.Bijective incompatibleStageTwo := by
  constructor
  · intro a b h
    have hh := congrArg (fun x : FiniteFiber 2 => incompatibleStageTwo x) h
    simpa only [incompatibleStageTwo_involutive] using hh
  · intro a
    exact ⟨incompatibleStageTwo a, incompatibleStageTwo_involutive a⟩

theorem incompatibleStageTwo_norm (a : FiniteFiber 2) :
    ‖incompatibleStageTwo a‖ = ‖a‖ := by
  exact NonUnitalStarAlgHom.norm_map incompatibleStageTwo
    incompatibleStageTwo_bijective.1 a

def incompatibleWitness : FiniteFiber 1 :=
  fun i => if i = 0 then 0 else 1

theorem incompatibleStageWitness :
    incompatibleStageTwo (stageEmbed 1 2 (by omega) incompatibleWitness) ≠
      stageEmbed 1 2 (by omega) incompatibleWitness := by
  intro h
  have h0 := congrFun h (0 : Fin 3)
  norm_num [incompatibleStageTwo, stageEmbed, incompatibleWitness] at h0

/-- The result distinguishes the canonical GNS lift from nontrivial scalar phases. -/
def BoundedDynamicsAndFailureGoal : Prop :=
  (∀ t n m (h : n ≤ m) (a : FiniteFiber n),
    stageEmbed n m h (finiteFlow t n a) =
      finiteFlow t m (stageEmbed n m h a)) ∧
  (∀ t a, limitFlow t a = a) ∧
  (∀ t x, canonicalGNSFlow t (quotientEvaluation x) =
    quotientEvaluation (quotientFlow t x)) ∧
  Dense (Set.range (quotientEvaluation : StateQuotient → GNSHilbert)) ∧
  (∀ s t z, boundedPhaseFlow (s + t) z =
    boundedPhaseFlow s (boundedPhaseFlow t z)) ∧
  (∀ t x y, inner ℂ (boundedPhaseFlow t x) (boundedPhaseFlow t y) =
    inner ℂ x y) ∧
  (∀ z, Continuous (fun t : ℝ => boundedPhaseFlow t z)) ∧
  (∀ t z, HasDerivAt (fun s : ℝ => boundedPhaseFlow s z)
    (Complex.I * boundedHamiltonian (boundedPhaseFlow t z)) t) ∧
  boundedPhaseFlow Real.pi (1 : GNSHilbert) ≠
    canonicalGNSFlow Real.pi (1 : GNSHilbert) ∧
  Function.Bijective incompatibleStageTwo ∧
  (incompatibleStageTwo (stageEmbed 1 2 (by omega) incompatibleWitness) ≠
    stageEmbed 1 2 (by omega) incompatibleWitness)

theorem boundedDynamicsAndFailureGoal : BoundedDynamicsAndFailureGoal := by
  exact ⟨finiteFlow_embed, limitFlow_eq_id, canonicalGNSFlow_intertwines,
    quotientRange_dense, boundedPhaseFlow_add, boundedPhaseFlow_inner,
    boundedPhaseFlow_continuous, boundedPhaseFlow_generatorEquation,
    boundedPhaseFlow_nontrivial, incompatibleStageTwo_bijective,
    incompatibleStageWitness⟩

/-! ### M5.7-D: transport of arbitrary compatible finite actions at the character GNS scope -/

/-- Finite-stage laws are source data; no quotient or Hilbert-space flow is a field. -/
structure CompatibleStageDynamics where
  flow : ℝ → (n : ℕ) → FiniteFiber n →⋆ₐ[ℂ] FiniteFiber n
  compatible : ∀ t n m (h : n ≤ m) (a : FiniteFiber n),
    stageEmbed n m h (flow t n a) = flow t m (stageEmbed n m h a)
  zero : ∀ n (a : FiniteFiber n), flow 0 n a = a
  add : ∀ s t n (a : FiniteFiber n),
    flow (s + t) n a = flow s n (flow t n a)
  state_invariant : ∀ t n (a : FiniteFiber n),
    stageState n (flow t n a) = stageState n a
  continuous_stage : ∀ n (a : FiniteFiber n),
    Continuous (fun t : ℝ => flow t n a)

/-- Group laws supply each finite star map with an actual inverse. -/
theorem CompatibleStageDynamics.injective (D : CompatibleStageDynamics)
    (t : ℝ) (n : ℕ) : Function.Injective (D.flow t n) := by
  intro a b hab
  calc
    a = D.flow (-t) n (D.flow t n a) := by
      rw [← D.add (-t) t n a, neg_add_cancel, D.zero]
    _ = D.flow (-t) n (D.flow t n b) :=
      congrArg (fun x : FiniteFiber n => D.flow (-t) n x) hab
    _ = b := by
      rw [← D.add (-t) t n b, neg_add_cancel, D.zero]

theorem CompatibleStageDynamics.norm (D : CompatibleStageDynamics)
    (t : ℝ) (n : ℕ) (a : FiniteFiber n) :
    ‖D.flow t n a‖ = ‖a‖ := by
  exact NonUnitalStarAlgHom.norm_map (D.flow t n) (D.injective t n) a

/-- Compatible source maps produce a well-defined algebraic direct-limit action. -/
def inducedAlgebraFlow (D : CompatibleStageDynamics) (t : ℝ) :
    FiberAlgebraicLimit → FiberAlgebraicLimit :=
  DirectLimit.map
    (f₁ := fun i j h => stageEmbed i j h)
    (f₂ := fun i j h => stageEmbed i j h)
    (fun n (a : FiniteFiber n) => D.flow t n a)
    (by intro n m h a; exact D.compatible t n m h a)

theorem inducedAlgebraFlow_of (D : CompatibleStageDynamics) (t : ℝ)
    (n : ℕ) (a : FiniteFiber n) :
    inducedAlgebraFlow D t (intoLimit n a) = intoLimit n (D.flow t n a) := rfl

theorem inducedAlgebraFlow_zero (D : CompatibleStageDynamics)
    (a : FiberAlgebraicLimit) : inducedAlgebraFlow D 0 a = a := by
  refine DirectLimit.induction (f := fun i j h => stageEmbed i j h) ?_ a
  intro n x
  change inducedAlgebraFlow D 0 (intoLimit n x) = intoLimit n x
  rw [inducedAlgebraFlow_of, D.zero]

theorem inducedAlgebraFlow_add (D : CompatibleStageDynamics)
    (s t : ℝ) (a : FiberAlgebraicLimit) :
    inducedAlgebraFlow D (s + t) a =
      inducedAlgebraFlow D s (inducedAlgebraFlow D t a) := by
  refine DirectLimit.induction (f := fun i j h => stageEmbed i j h) ?_ a
  intro n x
  change inducedAlgebraFlow D (s + t) (intoLimit n x) =
    inducedAlgebraFlow D s (inducedAlgebraFlow D t (intoLimit n x))
  rw [inducedAlgebraFlow_of, inducedAlgebraFlow_of,
    inducedAlgebraFlow_of, D.add]

theorem inducedAlgebraFlow_state (D : CompatibleStageDynamics) (t : ℝ)
    (a : FiberAlgebraicLimit) :
    limitState (inducedAlgebraFlow D t a) = limitState a := by
  refine DirectLimit.induction (f := fun i j h => stageEmbed i j h) ?_ a
  intro n x
  change limitState (inducedAlgebraFlow D t (intoLimit n x)) =
    limitState (intoLimit n x)
  rw [inducedAlgebraFlow_of, limitState_of, limitState_of]
  exact D.state_invariant t n x

theorem inducedAlgebraFlow_size (D : CompatibleStageDynamics) (t : ℝ)
    (a : FiberAlgebraicLimit) :
    limitSize (inducedAlgebraFlow D t a) = limitSize a := by
  refine DirectLimit.induction (f := fun i j h => stageEmbed i j h) ?_ a
  intro n x
  change limitSize (inducedAlgebraFlow D t (intoLimit n x)) = limitSize (intoLimit n x)
  rw [inducedAlgebraFlow_of, limitSize_of, limitSize_of]
  exact D.norm t n x

theorem inducedAlgebraFlow_star (D : CompatibleStageDynamics) (t : ℝ)
    (a : FiberAlgebraicLimit) :
    inducedAlgebraFlow D t (limitAdjoint a) =
      limitAdjoint (inducedAlgebraFlow D t a) := by
  refine DirectLimit.induction (f := fun i j h => stageEmbed i j h) ?_ a
  intro n x
  change inducedAlgebraFlow D t (limitAdjoint (intoLimit n x)) =
    limitAdjoint (inducedAlgebraFlow D t (intoLimit n x))
  rw [limitAdjoint_of, inducedAlgebraFlow_of,
    inducedAlgebraFlow_of, limitAdjoint_of]
  exact congrArg (intoLimit n) (map_star (D.flow t n) x)

theorem inducedAlgebraFlow_null (D : CompatibleStageDynamics) (t : ℝ)
    (a : FiberAlgebraicLimit) :
    stateNull (inducedAlgebraFlow D t a) ↔ stateNull a := by
  rw [stateNull_iff, stateNull_iff, inducedAlgebraFlow_state]

/-- State invariance, derived at the limit, proves congruence on null classes. -/
def inducedQuotientFlow (D : CompatibleStageDynamics) (t : ℝ)
    (x : StateQuotient) : StateQuotient :=
  Quotient.liftOn x (fun a => stateClass (inducedAlgebraFlow D t a)) (by
    intro a b h
    apply Quotient.sound
    change limitState (inducedAlgebraFlow D t a) =
      limitState (inducedAlgebraFlow D t b)
    rw [inducedAlgebraFlow_state, inducedAlgebraFlow_state]
    exact h)

theorem inducedQuotientFlow_class (D : CompatibleStageDynamics) (t : ℝ)
    (a : FiberAlgebraicLimit) :
    inducedQuotientFlow D t (stateClass a) =
      stateClass (inducedAlgebraFlow D t a) := rfl

/-- The character quotient forgets every state-preserving finite-stage motion. -/
theorem inducedQuotientFlow_eq_id (D : CompatibleStageDynamics) (t : ℝ)
    (x : StateQuotient) : inducedQuotientFlow D t x = x := by
  refine Quotient.inductionOn x ?_
  intro a
  apply quotientEvaluation_injective
  change limitState (inducedAlgebraFlow D t a) = limitState a
  exact inducedAlgebraFlow_state D t a

theorem inducedQuotientFlow_inner (D : CompatibleStageDynamics) (t : ℝ)
    (x y : StateQuotient) :
    quotientForm (inducedQuotientFlow D t x) (inducedQuotientFlow D t y) =
      quotientForm x y := by
  rw [inducedQuotientFlow_eq_id, inducedQuotientFlow_eq_id]

/-- The uniquely determined Hilbert extension acts on the entire dense quotient image. -/
def inducedCharacterGNSFlow (_D : CompatibleStageDynamics) (_t : ℝ) :
    GNSHilbert →L[ℂ] GNSHilbert :=
  ContinuousLinearMap.id ℂ GNSHilbert

theorem inducedCharacterGNSFlow_intertwines (D : CompatibleStageDynamics)
    (t : ℝ) (x : StateQuotient) :
    inducedCharacterGNSFlow D t (quotientEvaluation x) =
      quotientEvaluation (inducedQuotientFlow D t x) := by
  rw [inducedQuotientFlow_eq_id]
  rfl

theorem inducedCharacterGNSFlow_unique (D : CompatibleStageDynamics)
    (t : ℝ) (F : GNSHilbert →L[ℂ] GNSHilbert)
    (h : ∀ x, F (quotientEvaluation x) =
      quotientEvaluation (inducedQuotientFlow D t x)) :
    F = inducedCharacterGNSFlow D t := by
  refine ContinuousLinearMap.ext (fun z => ?_)
  obtain ⟨x, rfl⟩ := quotientEvaluation_surjective z
  rw [h, inducedQuotientFlow_eq_id]
  rfl

theorem inducedCharacterGNSFlow_group (D : CompatibleStageDynamics)
    (s t : ℝ) (z : GNSHilbert) :
    inducedCharacterGNSFlow D (s + t) z =
      inducedCharacterGNSFlow D s (inducedCharacterGNSFlow D t z) := rfl

theorem inducedCharacterGNSFlow_inner (D : CompatibleStageDynamics)
    (t : ℝ) (x y : GNSHilbert) :
    inner ℂ (inducedCharacterGNSFlow D t x) (inducedCharacterGNSFlow D t y) =
      inner ℂ x y := rfl

theorem inducedCharacterGNSFlow_strongContinuous (D : CompatibleStageDynamics)
    (z : GNSHilbert) :
    Continuous (fun t : ℝ => inducedCharacterGNSFlow D t z) := by
  change Continuous (fun _ : ℝ => z)
  exact continuous_const

/-- The generator of the canonical character GNS flow is the bounded zero operator. -/
def inducedCharacterGenerator (_D : CompatibleStageDynamics) :
    GNSHilbert →L[ℂ] GNSHilbert := 0

theorem inducedCharacterGNSFlow_generator (D : CompatibleStageDynamics)
    (t : ℝ) (z : GNSHilbert) :
    HasDerivAt (fun s : ℝ => inducedCharacterGNSFlow D s z)
      (Complex.I * inducedCharacterGenerator D (inducedCharacterGNSFlow D t z)) t := by
  have hval : Complex.I * inducedCharacterGenerator D (inducedCharacterGNSFlow D t z) = 0 := by
    change Complex.I * (0 : GNSHilbert →L[ℂ] GNSHilbert) (inducedCharacterGNSFlow D t z) = 0
    rw [ContinuousLinearMap.zero_apply, mul_zero]
  rw [hval]
  exact hasDerivAt_const t z

/-- The compatible identity stages witness nonvacuity of the finite source contract. -/
def compatibleIdentityDynamics : CompatibleStageDynamics where
  flow := finiteFlow
  compatible := by intro t n m h a; exact finiteFlow_embed t h a
  zero := by intro n a; exact finiteFlow_apply 0 n a
  add := finiteFlow_add
  state_invariant := finiteFlow_state
  continuous_stage := finiteFlow_continuous

theorem compatibleStageDynamics_nonempty : Nonempty CompatibleStageDynamics :=
  ⟨compatibleIdentityDynamics⟩

/-- Source-level compatibility and state invariance construct a unique strong
Hilbert lift in the present one-dimensional character GNS model. -/
def CompatibleCharacterDynamicsGoal : Prop :=
  ∀ D : CompatibleStageDynamics,
    (∀ t n a, ‖D.flow t n a‖ = ‖a‖) ∧
    (∀ s t a, inducedAlgebraFlow D (s + t) a =
      inducedAlgebraFlow D s (inducedAlgebraFlow D t a)) ∧
    (∀ t a, limitState (inducedAlgebraFlow D t a) = limitState a) ∧
    (∀ t x, inducedQuotientFlow D t x = x) ∧
    (∀ t x, inducedCharacterGNSFlow D t (quotientEvaluation x) =
      quotientEvaluation (inducedQuotientFlow D t x)) ∧
    (∀ z, Continuous (fun t : ℝ => inducedCharacterGNSFlow D t z)) ∧
    (∀ t x y, inner ℂ (inducedCharacterGNSFlow D t x)
      (inducedCharacterGNSFlow D t y) = inner ℂ x y) ∧
    (∀ t z, HasDerivAt (fun s : ℝ => inducedCharacterGNSFlow D s z)
      (Complex.I * inducedCharacterGenerator D
        (inducedCharacterGNSFlow D t z)) t)

theorem compatibleCharacterDynamicsGoal : CompatibleCharacterDynamicsGoal := by
  intro D
  exact ⟨D.norm, inducedAlgebraFlow_add D, inducedAlgebraFlow_state D,
    inducedQuotientFlow_eq_id D, inducedCharacterGNSFlow_intertwines D,
    inducedCharacterGNSFlow_strongContinuous D,
    inducedCharacterGNSFlow_inner D, inducedCharacterGNSFlow_generator D⟩

/-! ### M5.7-D: self-adjoint generators and state-preserving incompatibility -/

/-- The bounded Hamiltonian is self-adjoint in the native Hilbert operator sense. -/
theorem boundedHamiltonian_selfAdjoint : IsSelfAdjoint boundedHamiltonian := by
  apply (ContinuousLinearMap.isSelfAdjoint_iff').2
  change ContinuousLinearMap.adjoint (ContinuousLinearMap.id ℂ GNSHilbert) =
    ContinuousLinearMap.id ℂ GNSHilbert
  exact ContinuousLinearMap.adjoint_id

/-- The canonical character-GNS unitary group consists of self-adjoint identities. -/
theorem canonicalGNSFlow_selfAdjoint (t : ℝ) :
    IsSelfAdjoint (canonicalGNSFlow t) := by
  apply (ContinuousLinearMap.isSelfAdjoint_iff').2
  change ContinuousLinearMap.adjoint (ContinuousLinearMap.id ℂ GNSHilbert) =
    ContinuousLinearMap.id ℂ GNSHilbert
  exact ContinuousLinearMap.adjoint_id

/-- The zero generator of any compatible character-GNS flow is self-adjoint. -/
theorem inducedCharacterGenerator_selfAdjoint (D : CompatibleStageDynamics) :
    IsSelfAdjoint (inducedCharacterGenerator D) := by
  change IsSelfAdjoint (0 : GNSHilbert →L[ℂ] GNSHilbert)
  exact IsSelfAdjoint.zero (GNSHilbert →L[ℂ] GNSHilbert)

/-- The complex Hilbert carrier is the entire domain of both bounded generators. -/
theorem boundedGeneratorDomain_eq_univ :
    boundedGeneratorDomain = (Set.univ : Set GNSHilbert) := rfl

/-- The stage-three coordinate transposition fixes zero and exchanges coordinates one and two. -/
def characterPreservingStageThree : FiniteFiber 3 →⋆ₐ[ℂ] FiniteFiber 3 where
  toFun a i := a (if i = 1 then 2 else if i = 2 then 1 else i)
  map_one' := by
    funext i
    rfl
  map_mul' := by
    intro a b
    funext i
    rfl
  map_zero' := by
    funext i
    rfl
  map_add' := by
    intro a b
    funext i
    rfl
  commutes' := by
    intro c
    funext i
    rfl
  map_star' := by
    intro a
    funext i
    rfl

theorem characterPreservingStageThree_involutive (a : FiniteFiber 3) :
    characterPreservingStageThree (characterPreservingStageThree a) = a := by
  funext i
  fin_cases i <;> rfl

theorem characterPreservingStageThree_bijective :
    Function.Bijective characterPreservingStageThree := by
  constructor
  · intro a b h
    have hh := congrArg
      (fun x : FiniteFiber 3 => characterPreservingStageThree x) h
    simpa only [characterPreservingStageThree_involutive] using hh
  · intro a
    exact ⟨characterPreservingStageThree a,
      characterPreservingStageThree_involutive a⟩

theorem characterPreservingStageThree_norm (a : FiniteFiber 3) :
    ‖characterPreservingStageThree a‖ = ‖a‖ := by
  exact NonUnitalStarAlgHom.norm_map characterPreservingStageThree
    characterPreservingStageThree_bijective.1 a

theorem characterPreservingStageThree_state (a : FiniteFiber 3) :
    stageState 3 (characterPreservingStageThree a) = stageState 3 a := by
  change a (if (0 : Fin 4) = 1 then 2 else if (0 : Fin 4) = 2 then 1 else 0) =
    a (0 : Fin 4)
  rfl

/-- The earlier finite-stage identity is also character-state preserving. -/
theorem characterPreservingStageTwo_state (a : FiniteFiber 2) :
    stageState 2 ((StarAlgHom.id ℂ (FiniteFiber 2)) a) = stageState 2 a := rfl

/-- The lower-stage source distinguishes coordinates one and two. -/
def characterIncompatibilityWitness : FiniteFiber 2 :=
  fun i => if i = 1 then 1 else 0

/-- Character invariance does not imply directed-system compatibility. -/
theorem characterPreservingStageThree_incompatible :
    characterPreservingStageThree
        (stageEmbed 2 3 (by omega) characterIncompatibilityWitness) ≠
      stageEmbed 2 3 (by omega) characterIncompatibilityWitness := by
  intro h
  have h1 := congrFun h (1 : Fin 4)
  norm_num [characterPreservingStageThree, stageEmbed,
    characterIncompatibilityWitness] at h1

/-- No endomorphism of the direct limit can extend both state-preserving finite maps. -/
theorem noLimitMapForCharacterIncompatibility :
    ¬ ∃ T : FiberAlgebraicLimit → FiberAlgebraicLimit,
      (∀ a : FiniteFiber 2, T (intoLimit 2 a) = intoLimit 2 a) ∧
      (∀ b : FiniteFiber 3,
        T (intoLimit 3 b) = intoLimit 3 (characterPreservingStageThree b)) := by
  rintro ⟨T, htwo, hthree⟩
  apply characterPreservingStageThree_incompatible
  apply intoLimit_injective 3
  calc
    intoLimit 3
        (characterPreservingStageThree
          (stageEmbed 2 3 (by omega) characterIncompatibilityWitness)) =
      T (intoLimit 3
        (stageEmbed 2 3 (by omega) characterIncompatibilityWitness)) :=
          (hthree _).symm
    _ = T (intoLimit 2 characterIncompatibilityWitness) := by
      rw [intoLimit_compatible]
    _ = intoLimit 2 characterIncompatibilityWitness :=
      htwo characterIncompatibilityWitness
    _ = intoLimit 3 (stageEmbed 2 3 (by omega) characterIncompatibilityWitness) :=
      (intoLimit_compatible (show 2 ≤ 3 by omega)
        characterIncompatibilityWitness).symm

/-- Both local maps are state-preserving and norm-preserving yet have no common limit map. -/
def SelfAdjointStateInvariantFailureGoal : Prop :=
  IsSelfAdjoint boundedHamiltonian ∧
  (∀ D : CompatibleStageDynamics, IsSelfAdjoint (inducedCharacterGenerator D)) ∧
  (∀ t, IsSelfAdjoint (canonicalGNSFlow t)) ∧
  boundedGeneratorDomain = (Set.univ : Set GNSHilbert) ∧
  Function.Bijective characterPreservingStageThree ∧
  (∀ a, stageState 2 ((StarAlgHom.id ℂ (FiniteFiber 2)) a) = stageState 2 a) ∧
  (∀ b, stageState 3 (characterPreservingStageThree b) = stageState 3 b) ∧
  (∀ b, ‖characterPreservingStageThree b‖ = ‖b‖) ∧
  ¬ ∃ T : FiberAlgebraicLimit → FiberAlgebraicLimit,
    (∀ a : FiniteFiber 2, T (intoLimit 2 a) = intoLimit 2 a) ∧
    (∀ b : FiniteFiber 3,
      T (intoLimit 3 b) = intoLimit 3 (characterPreservingStageThree b))

theorem selfAdjointStateInvariantFailureGoal :
    SelfAdjointStateInvariantFailureGoal := by
  exact ⟨boundedHamiltonian_selfAdjoint,
    inducedCharacterGenerator_selfAdjoint, canonicalGNSFlow_selfAdjoint,
    boundedGeneratorDomain_eq_univ, characterPreservingStageThree_bijective,
    characterPreservingStageTwo_state, characterPreservingStageThree_state,
    characterPreservingStageThree_norm,
    noLimitMapForCharacterIncompatibility⟩

/-! ### M5.7-D: generator existence for the constructed character GNS action -/

/-- Every compatible source flow induces a strongly continuous unitary
character action with an explicitly constructed bounded self-adjoint generator.
This theorem concerns the displayed one-dimensional character representation. -/
def CharacterUnitaryGeneratorGoal : Prop :=
  ∀ D : CompatibleStageDynamics,
    (∀ s t z, inducedCharacterGNSFlow D (s + t) z =
      inducedCharacterGNSFlow D s (inducedCharacterGNSFlow D t z)) ∧
    (∀ t x y, inner ℂ (inducedCharacterGNSFlow D t x)
      (inducedCharacterGNSFlow D t y) = inner ℂ x y) ∧
    (∀ z, Continuous (fun t : ℝ => inducedCharacterGNSFlow D t z)) ∧
    (∃ H : GNSHilbert →L[ℂ] GNSHilbert,
      IsSelfAdjoint H ∧ Dense (Set.univ : Set GNSHilbert) ∧
      (∀ t z, HasDerivAt (fun s : ℝ => inducedCharacterGNSFlow D s z)
        (Complex.I * H (inducedCharacterGNSFlow D t z)) t))

theorem characterUnitaryGeneratorGoal : CharacterUnitaryGeneratorGoal := by
  intro D
  refine ⟨inducedCharacterGNSFlow_group D, inducedCharacterGNSFlow_inner D,
    inducedCharacterGNSFlow_strongContinuous D, ?_⟩
  refine ⟨inducedCharacterGenerator D,
    inducedCharacterGenerator_selfAdjoint D, dense_univ, ?_⟩
  intro t z
  exact inducedCharacterGNSFlow_generator D t z

/-- Nonvacuity uses the explicit compatible stage-identity family. -/
theorem characterUnitaryGenerator_nonvacuous :
    ∃ _D : CompatibleStageDynamics, CharacterUnitaryGeneratorGoal :=
  ⟨compatibleIdentityDynamics, characterUnitaryGeneratorGoal⟩


/-! ### The generator theorem for norm-continuous one-parameter groups

A norm-continuous one-parameter group in a complete normed complex algebra is the exponential
of a unique bounded generator. The average of the group over a short interval is invertible,
because its derivative at the origin is the unit; translating the average expresses the group
through its primitive, which is differentiable, so the group is differentiable with derivative
`U t * A`. The product of the group with `exp (- t A)` has derivative zero and value one at the
origin. A group of unitaries in a C* algebra has a skew-adjoint generator `A = i H` with `H`
self-adjoint, and its orbit satisfies the dynamical equation `U' = i H U`. On a
finite-dimensional Hilbert space strong continuity is norm continuity, so every strongly
continuous unitary group there has a bounded self-adjoint generator.
-/

section UniformGenerator

open NormedSpace

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℂ 𝔸] [CompleteSpace 𝔸]

/-- The primitive of a continuous one-parameter family. -/
def groupPrimitive (U : ℝ → 𝔸) (u : ℝ) : 𝔸 := ∫ s in (0 : ℝ)..u, U s

theorem groupPrimitive_hasDerivAt {U : ℝ → 𝔸} (hU : Continuous U) (u : ℝ) :
    HasDerivAt (groupPrimitive U) (U u) u :=
  (hU.integral_hasStrictDerivAt 0 u).hasDerivAt

omit [CompleteSpace 𝔸] in
theorem groupPrimitive_zero (U : ℝ → 𝔸) : groupPrimitive U 0 = 0 :=
  intervalIntegral.integral_same

/-- The primitive over a translated interval is the left translate of the primitive. -/
theorem groupPrimitive_translate {U : ℝ → 𝔸} (hadd : ∀ s t, U (s + t) = U s * U t)
    (hU : Continuous U) (t ε : ℝ) :
    groupPrimitive U (t + ε) - groupPrimitive U t = U t * groupPrimitive U ε := by
  have h1 : groupPrimitive U (t + ε) - groupPrimitive U t = ∫ s in t..t + ε, U s :=
    intervalIntegral.integral_interval_sub_left (hU.intervalIntegrable _ _)
      (hU.intervalIntegrable _ _)
  have h2 : (∫ s in t..t + ε, U s) = ∫ s in (0 : ℝ)..ε, U (t + s) := by
    have h := intervalIntegral.integral_comp_add_left (a := 0) (b := ε) (fun s => U s) t
    rw [add_zero] at h
    exact h.symm
  have h3 : (∫ s in (0 : ℝ)..ε, U (t + s)) =
      ∫ s in (0 : ℝ)..ε, ContinuousLinearMap.mul ℝ 𝔸 (U t) (U s) := by
    congr 1
    funext s
    rw [hadd]
    rfl
  rw [h1, h2, h3, ContinuousLinearMap.intervalIntegral_comp_comm _ (hU.intervalIntegrable _ _)]
  rfl

/-- A short average of a continuous group with `U 0 = 1` is invertible. -/
theorem exists_unit_average {U : ℝ → 𝔸} (h0 : U 0 = 1) (hU : Continuous U) :
    ∃ ε : ℝ, 0 < ε ∧ IsUnit (ε⁻¹ • groupPrimitive U ε) := by
  have ht := (groupPrimitive_hasDerivAt hU 0).tendsto_slope_zero_right
  rw [h0] at ht
  have hev : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      IsUnit (t⁻¹ • (groupPrimitive U (0 + t) - groupPrimitive U 0)) := ht (Units.nhds 1)
  obtain ⟨ε, hε, hpos⟩ := (hev.and self_mem_nhdsWithin).exists
  refine ⟨ε, hpos, ?_⟩
  rw [zero_add, groupPrimitive_zero, sub_zero] at hε
  exact hε

/-- The group is differentiable, with derivative `U t * A` for an explicit generator `A`. -/
theorem exists_generator_deriv {U : ℝ → 𝔸} (h0 : U 0 = 1) (hadd : ∀ s t, U (s + t) = U s * U t)
    (hU : Continuous U) : ∃ A : 𝔸, ∀ t, HasDerivAt U (U t * A) t := by
  obtain ⟨ε, hε, hunit⟩ := exists_unit_average h0 hU
  obtain ⟨w, hw⟩ := hunit
  have hform : ∀ t, U t = (ε⁻¹ • (groupPrimitive U (t + ε) - groupPrimitive U t)) *
      ((w⁻¹ : 𝔸ˣ) : 𝔸) := by
    intro t
    rw [groupPrimitive_translate hadd hU t ε, ← mul_smul_comm, ← hw, mul_assoc, Units.mul_inv,
      mul_one]
  refine ⟨(ε⁻¹ • (U ε - 1)) * ((w⁻¹ : 𝔸ˣ) : 𝔸), fun t => ?_⟩
  have hG : HasDerivAt (fun u => (ε⁻¹ • (groupPrimitive U (u + ε) - groupPrimitive U u)) *
      ((w⁻¹ : 𝔸ˣ) : 𝔸)) ((ε⁻¹ • (U (t + ε) - U t)) * ((w⁻¹ : 𝔸ˣ) : 𝔸)) t := by
    have h1 : HasDerivAt (fun u => groupPrimitive U (u + ε)) (U (t + ε)) t :=
      HasDerivAt.comp_add_const t ε (groupPrimitive_hasDerivAt hU (t + ε))
    exact (((h1.sub (groupPrimitive_hasDerivAt hU t)).const_smul ε⁻¹).mul_const _)
  have key := hG.congr_of_eventuallyEq (Filter.Eventually.of_forall hform)
  have hval : (ε⁻¹ • (U (t + ε) - U t)) * ((w⁻¹ : 𝔸ˣ) : 𝔸) =
      U t * ((ε⁻¹ • (U ε - 1)) * ((w⁻¹ : 𝔸ˣ) : 𝔸)) := by
    rw [hadd t ε, show U t * U ε - U t = U t * (U ε - 1) by rw [mul_sub, mul_one],
      ← mul_smul_comm, mul_assoc]
  rw [hval] at key
  exact key

/-- A norm-continuous one-parameter group is the exponential of a bounded generator. -/
theorem uniform_group_eq_exp {U : ℝ → 𝔸} (h0 : U 0 = 1) {A : 𝔸}
    (hA : ∀ t, HasDerivAt U (U t * A) t) (t : ℝ) :
    U t = exp ℝ (t • A) := by
  let V : ℝ → 𝔸 := fun u => U u * exp ℝ (u • (-A))
  have hV : ∀ u, HasDerivAt V 0 u := by
    intro u
    have h := (hA u).fun_mul (hasDerivAt_exp_smul_const' (𝕂 := ℝ) (-A) u)
    have hz : U u * A * exp ℝ (u • (-A)) + U u * (-A * exp ℝ (u • (-A))) = 0 := by
      rw [neg_mul, mul_neg, mul_assoc, add_neg_cancel]
    rw [hz] at h
    exact h
  have hconst : V t = V 0 := is_const_of_deriv_eq_zero (fun u => (hV u).differentiableAt)
    (fun u => (hV u).deriv) t 0
  have hV0 : V 0 = 1 := by
    change U 0 * exp ℝ ((0 : ℝ) • (-A)) = 1
    rw [h0, zero_smul, exp_zero, one_mul]
  rw [hV0] at hconst
  have hcomm : Commute (t • (-A)) (t • A) := ((Commute.refl A).neg_left).smul_left t |>.smul_right t
  calc U t = U t * (exp ℝ (t • (-A)) * exp ℝ (t • A)) := by
        rw [← exp_add_of_commute hcomm, smul_neg, neg_add_cancel, exp_zero, mul_one]
    _ = V t * exp ℝ (t • A) := (mul_assoc _ _ _).symm
    _ = exp ℝ (t • A) := by rw [hconst, one_mul]

omit [CompleteSpace 𝔸] in
/-- The generator of a norm-continuous group is unique: it is the derivative at the origin. -/
theorem generator_unique {U : ℝ → 𝔸} (h0 : U 0 = 1) {A B : 𝔸}
    (hA : ∀ t, HasDerivAt U (U t * A) t) (hB : ∀ t, HasDerivAt U (U t * B) t) : A = B := by
  have h := (hA 0).unique (hB 0)
  rw [h0, one_mul, one_mul] at h
  exact h

/-- The generator theorem for norm-continuous one-parameter groups. -/
theorem uniform_generator_theorem {U : ℝ → 𝔸} (h0 : U 0 = 1)
    (hadd : ∀ s t, U (s + t) = U s * U t) (hU : Continuous U) :
    ∃! A : 𝔸, (∀ t, HasDerivAt U (U t * A) t) ∧ ∀ t, U t = exp ℝ (t • A) := by
  obtain ⟨A, hA⟩ := exists_generator_deriv h0 hadd hU
  refine ⟨A, ⟨hA, uniform_group_eq_exp h0 hA⟩, fun B hB => ?_⟩
  exact generator_unique h0 hB.1 hA

end UniformGenerator

section UnitaryGenerator

open NormedSpace

variable {𝔸 : Type*} [CStarAlgebra 𝔸]

/-- A norm-continuous group of unitaries has a bounded self-adjoint Hamiltonian `H`: the group is
`exp (t (i H))` and its orbit satisfies `U' = (i H) U`. -/
theorem unitary_generator_theorem {U : ℝ → 𝔸} (h0 : U 0 = 1)
    (hadd : ∀ s t, U (s + t) = U s * U t) (hU : Continuous U) (hunit : ∀ t, U t ∈ unitary 𝔸) :
    ∃ H : 𝔸, IsSelfAdjoint H ∧ (∀ t, U t = exp ℝ (t • (Complex.I • H))) ∧
      ∀ t, HasDerivAt U ((Complex.I • H) * U t) t := by
  obtain ⟨A, hA, hexp⟩ := (uniform_generator_theorem h0 hadd hU).exists
  have hstar : ∀ t, HasDerivAt (fun u => star (U u)) (star (U t * A)) t :=
    fun t => (hA t).star
  have hprod : HasDerivAt (fun u => star (U u) * U u)
      (star (U 0 * A) * U 0 + star (U 0) * (U 0 * A)) 0 := (hstar 0).fun_mul (hA 0)
  have hone : (fun u => star (U u) * U u) = fun _ => (1 : 𝔸) := by
    funext u
    exact unitary.star_mul_self_of_mem (hunit u)
  rw [hone] at hprod
  have hzero := hprod.unique (hasDerivAt_const (0 : ℝ) (1 : 𝔸))
  rw [h0, one_mul, star_one, one_mul, mul_one] at hzero
  have hskew : star A = -A := eq_neg_of_add_eq_zero_left hzero
  have hcomm : ∀ t, U t * A = A * U t := by
    intro t
    rw [hexp t]
    exact (((Commute.refl A).smul_right t).exp_right ℝ).eq.symm
  refine ⟨(-Complex.I) • A, ?_, ?_, ?_⟩
  · change star ((-Complex.I) • A) = (-Complex.I) • A
    rw [star_smul, hskew, Complex.star_def, map_neg, Complex.conj_I, neg_neg, smul_neg, neg_smul]
  · intro t
    rw [smul_smul, mul_neg, Complex.I_mul_I, neg_neg, one_smul]
    exact hexp t
  · intro t
    rw [smul_smul, mul_neg, Complex.I_mul_I, neg_neg, one_smul, ← hcomm t]
    exact hA t

/-- On a finite-dimensional Hilbert space a strongly continuous unitary group has a bounded
self-adjoint Hamiltonian, and every orbit satisfies the dynamical equation. -/
theorem finite_strong_unitary_generator {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [FiniteDimensional ℂ E] {U : ℝ → E →L[ℂ] E} (h0 : U 0 = 1)
    (hadd : ∀ s t, U (s + t) = U s * U t) (hstrong : ∀ x, Continuous fun t => U t x)
    (hunit : ∀ t, U t ∈ unitary (E →L[ℂ] E)) :
    ∃ H : E →L[ℂ] E, IsSelfAdjoint H ∧
      ∀ t x, HasDerivAt (fun s => U s x) (Complex.I • H (U t x)) t := by
  haveI : CompleteSpace E := FiniteDimensional.complete ℂ E
  have hU : Continuous U := continuous_clm_apply.mpr hstrong
  obtain ⟨H, hH, -, hder⟩ := unitary_generator_theorem h0 hadd hU hunit
  refine ⟨H, hH, fun t x => ?_⟩
  have h := ((ContinuousLinearMap.apply ℂ E x).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t
    (hder t)
  exact h

end UnitaryGenerator

end ReconstructionLimits
end OperatorKO7.Meta.BoundaryObserver
