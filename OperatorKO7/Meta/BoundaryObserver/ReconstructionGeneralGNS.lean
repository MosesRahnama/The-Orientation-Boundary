import OperatorKO7.Meta.BoundaryObserver.ReconstructionLimitCompletion
import Mathlib.Analysis.InnerProductSpace.Completion
import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# General positive-functional GNS construction

The functional is positive and complex-linear; multiplicativity is NOT assumed.
The null quadratic-form space is a left ideal, not necessarily a two-sided ideal.
Its quotient is an inner product space, and the uniform completion is Hilbert.
Left multiplication extends as bounded operators. The adjoint law, cyclic vector,
and state identity are statements about the same positive functional.
-/

set_option autoImplicit false
noncomputable section

open scoped ComplexOrder
open OperatorKO7.Meta.BoundaryObserver.ReconstructionLimitCompletion
open OperatorKO7.Meta.BoundaryObserver.ReconstructionLimitCompletion.PositiveFunctional

namespace OperatorKO7.Meta.BoundaryObserver.ReconstructionGeneralGNS

universe u

variable {A : Type u} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
variable (ω : A →ₚ[ℂ] ℂ)

/-- The quotient identifies exactly the vectors of zero state seminorm. -/
def QSpace : Type u := A ⧸ nullSubmodule ω

instance quotientAddCommGroup : AddCommGroup (QSpace ω) :=
  inferInstanceAs (AddCommGroup (A ⧸ nullSubmodule ω))

instance quotientModule : Module ℂ (QSpace ω) :=
  inferInstanceAs (Module ℂ (A ⧸ nullSubmodule ω))

/-- The quotient map has the sealed state-space type, with its state-induced norm. -/
def classOf (a : A) : QSpace ω := Submodule.Quotient.mk a

@[simp]
theorem classOf_add (a b : A) : classOf ω (a + b) = classOf ω a + classOf ω b := rfl

@[simp]
theorem classOf_smul (c : ℂ) (a : A) : classOf ω (c • a) = c • classOf ω a := rfl

theorem classOf_surjective : Function.Surjective (classOf ω) :=
  Submodule.Quotient.mk_surjective (nullSubmodule ω)

/-- The positive form passes to the quotient in BOTH arguments by Cauchy-Schwarz. -/
def quotientForm (x y : QSpace ω) : ℂ :=
  Quotient.liftOn₂ x y (fun a b : A => form ω a b) (by
    intro a a' b b' ha hb
    exact form_congr ω
      ((Submodule.Quotient.eq (nullSubmodule ω)).mp (Quotient.sound ha))
      ((Submodule.Quotient.eq (nullSubmodule ω)).mp (Quotient.sound hb)))

@[simp]
theorem quotientForm_mk (a b : A) :
    quotientForm ω (classOf ω a) (classOf ω b) =
      form ω a b := rfl

/-- Strict definiteness is restored by removing precisely the null submodule. -/
def quotientInnerCore : InnerProductSpace.Core ℂ (QSpace ω) where
  inner := quotientForm ω
  conj_inner_symm := by
    intro x y
    refine Quotient.inductionOn₂ x y ?_
    intro a b
    exact form_conj_symm ω a b
  re_inner_nonneg := by
    intro x
    refine Quotient.inductionOn x ?_
    intro a
    exact form_re_nonneg ω a
  add_left := by
    intro x y z
    refine Quotient.inductionOn₃ x y z ?_
    intro a b c
    change form ω (a + b) c = form ω a c + form ω b c
    exact form_add_left ω a b c
  smul_left := by
    intro x y c
    refine Quotient.inductionOn₂ x y ?_
    intro a b
    change form ω (c • a) b = star c * form ω a b
    exact form_smul_left ω c a b
  definite := by
    intro x hx
    refine Quotient.inductionOn x ?_ hx
    intro a ha
    change form ω a a = 0 at ha
    exact (Submodule.Quotient.mk_eq_zero (nullSubmodule ω)).mpr
      ((mem_nullSubmodule ω a).mpr ha)

noncomputable instance quotientNormedGroup : NormedAddCommGroup (QSpace ω) :=
  (quotientInnerCore ω).toNormedAddCommGroup

noncomputable instance quotientNormedSpace : NormedSpace ℂ (QSpace ω) :=
  letI : InnerProductSpace.Core ℂ (QSpace ω) := quotientInnerCore ω
  InnerProductSpace.Core.toNormedSpace

noncomputable instance quotientInner : InnerProductSpace ℂ (QSpace ω) :=
  InnerProductSpace.ofCore (quotientInnerCore ω)

@[simp]
theorem norm_quotient_mk (a : A) :
    ‖(classOf ω a : QSpace ω)‖ = seminorm ω a := by
  rfl

/-- The quotient's inner product agrees with the original positive form. -/
theorem inner_quotient_mk (a b : A) :
    inner ℂ (classOf ω a : QSpace ω)
      (classOf ω b : QSpace ω) = form ω a b := rfl

/-- Left multiplication is well-defined because the null space is a LEFT ideal. -/
def leftLinear (a : A) : QSpace ω →ₗ[ℂ] QSpace ω where
  toFun := fun x =>
    Quotient.liftOn x
      (fun b : A => (classOf ω (a * b) : QSpace ω)) (by
        intro b c hbc
        apply (Submodule.Quotient.eq (nullSubmodule ω)).mpr
        change a * b - a * c ∈ nullSubmodule ω
        rw [← mul_sub]
        exact null_left_mul ω a
          ((Submodule.Quotient.eq (nullSubmodule ω)).mp (Quotient.sound hbc)))
  map_add' := by
    intro x y
    refine Quotient.inductionOn₂ x y ?_
    intro b c
    change (classOf ω (a * (b + c)) : QSpace ω) =
      classOf ω (a * b) + classOf ω (a * c)
    rw [mul_add, classOf_add]
  map_smul' := by
    intro c x
    refine Quotient.inductionOn x ?_
    intro b
    change (classOf ω (a * (c • b)) : QSpace ω) =
      c • classOf ω (a * b)
    rw [mul_smul_comm, classOf_smul]

@[simp]
theorem leftLinear_mk (a b : A) :
    leftLinear ω a (classOf ω b) =
      (classOf ω (a * b) : QSpace ω) := rfl

/-- The C-star inequality gives the actual operator bound. -/
theorem leftLinear_bound (a : A) (x : QSpace ω) :
    ‖leftLinear ω a x‖ ≤ ‖a‖ * ‖x‖ := by
  refine Quotient.inductionOn x ?_
  intro b
  simpa only [leftLinear_mk, norm_quotient_mk] using
    (seminorm_left_mul_le ω a b)

/-- Each algebra element acts by a constructed bounded complex-linear map. -/
def leftOperator (a : A) : QSpace ω →L[ℂ] QSpace ω :=
  (leftLinear ω a).mkContinuous ‖a‖ (leftLinear_bound ω a)

@[simp]
theorem leftOperator_mk (a b : A) :
    leftOperator ω a (classOf ω b) =
      (classOf ω (a * b) : QSpace ω) :=
  leftLinear_mk ω a b

theorem leftOperator_bound (a : A) (x : QSpace ω) :
    ‖leftOperator ω a x‖ ≤ ‖a‖ * ‖x‖ :=
  leftLinear_bound ω a x

/-- On the dense quotient, left action of star a is adjoint to left action of a. -/
theorem leftOperator_adjoint (a : A) (x y : QSpace ω) :
    inner ℂ (leftOperator ω a x) y =
      inner ℂ x (leftOperator ω (star a) y) := by
  refine Quotient.inductionOn₂ x y ?_
  intro b c
  change form ω (a * b) c = form ω b (star a * c)
  simp only [form, star_mul, mul_assoc]

/-- The actual Hilbert space is the metric completion of the definite quotient. -/
abbrev Hilbert := UniformSpace.Completion (QSpace ω)

instance hilbertComplete : CompleteSpace (Hilbert ω) := inferInstance
instance hilbertInner : InnerProductSpace ℂ (Hilbert ω) := inferInstance

/-- Extension of left multiplication on the dense quotient, with values in Hilbert space. -/
def actionValue (a : A) : Hilbert ω → Hilbert ω :=
  UniformSpace.Completion.extension
    (fun x : QSpace ω => ((leftOperator ω a x : QSpace ω) : Hilbert ω))

theorem actionValue_continuous (a : A) : Continuous (actionValue ω a) :=
  UniformSpace.Completion.continuous_extension

@[simp]
theorem actionValue_coe (a : A) (x : QSpace ω) :
    actionValue ω a (x : Hilbert ω) =
      ((leftOperator ω a x : QSpace ω) : Hilbert ω) := by
  exact UniformSpace.Completion.extension_coe
    ((UniformSpace.Completion.toComplL.comp (leftOperator ω a)).uniformContinuous) x

/-- The extension is linear as well as continuous. -/
def action (a : A) : Hilbert ω →L[ℂ] Hilbert ω where
  toFun := actionValue ω a
  map_add' := by
    intro x y
    refine UniformSpace.Completion.induction_on₂ x y
      (isClosed_eq
        ((actionValue_continuous ω a).comp (continuous_fst.add continuous_snd))
        (((actionValue_continuous ω a).comp continuous_fst).add
          ((actionValue_continuous ω a).comp continuous_snd))) ?_
    intro b c
    rw [← UniformSpace.Completion.coe_add, actionValue_coe,
      map_add, UniformSpace.Completion.coe_add, actionValue_coe, actionValue_coe]
  map_smul' := by
    intro c x
    refine UniformSpace.Completion.induction_on x
      (isClosed_eq
        ((actionValue_continuous ω a).comp (continuous_id.const_smul c))
        ((actionValue_continuous ω a).const_smul c)) ?_
    intro b
    rw [← UniformSpace.Completion.coe_smul, actionValue_coe,
      map_smul, UniformSpace.Completion.coe_smul, actionValue_coe]
    rfl
  cont := actionValue_continuous ω a

@[simp]
theorem action_mk (a b : A) :
    action ω a ((classOf ω b : QSpace ω) : Hilbert ω) =
      ((classOf ω (a * b) : QSpace ω) : Hilbert ω) := by
  change actionValue ω a ((classOf ω b : QSpace ω) : Hilbert ω) =
    ((classOf ω (a * b) : QSpace ω) : Hilbert ω)
  rw [actionValue_coe, leftOperator_mk]

/-- The bound survives completion with precisely the original algebra norm. -/
theorem action_bound (a : A) (x : Hilbert ω) :
    ‖action ω a x‖ ≤ ‖a‖ * ‖x‖ := by
  refine UniformSpace.Completion.induction_on x
    (isClosed_le (action ω a).continuous.norm (continuous_const.mul continuous_norm)) ?_
  intro q
  refine Quotient.inductionOn q ?_
  intro b
  change ‖action ω a ((classOf ω b : QSpace ω) : Hilbert ω)‖ ≤
    ‖a‖ * ‖((classOf ω b : QSpace ω) : Hilbert ω)‖
  rw [action_mk, UniformSpace.Completion.norm_coe,
    UniformSpace.Completion.norm_coe, norm_quotient_mk, norm_quotient_mk]
  exact seminorm_left_mul_le ω a b

theorem action_one (x : Hilbert ω) : action ω (1 : A) x = x := by
  refine UniformSpace.Completion.induction_on x
    (isClosed_eq (action ω (1 : A)).continuous continuous_id) ?_
  intro q
  refine Quotient.inductionOn q ?_
  intro a
  change action ω (1 : A) ((classOf ω a : QSpace ω) : Hilbert ω) =
    ((classOf ω a : QSpace ω) : Hilbert ω)
  rw [action_mk, one_mul]

theorem action_mul (a b : A) (x : Hilbert ω) :
    action ω (a * b) x = action ω a (action ω b x) := by
  refine UniformSpace.Completion.induction_on x
    (isClosed_eq (action ω (a * b)).continuous
      ((action ω a).continuous.comp (action ω b).continuous)) ?_
  intro q
  refine Quotient.inductionOn q ?_
  intro c
  change action ω (a * b) ((classOf ω c : QSpace ω) : Hilbert ω) =
    action ω a (action ω b ((classOf ω c : QSpace ω) : Hilbert ω))
  rw [action_mk, action_mk, action_mk, mul_assoc]

theorem action_add (a b : A) (x : Hilbert ω) :
    action ω (a + b) x = action ω a x + action ω b x := by
  refine UniformSpace.Completion.induction_on x
    (isClosed_eq (action ω (a + b)).continuous
      ((action ω a).continuous.add (action ω b).continuous)) ?_
  intro q
  refine Quotient.inductionOn q ?_
  intro c
  change action ω (a + b) ((classOf ω c : QSpace ω) : Hilbert ω) =
    action ω a ((classOf ω c : QSpace ω) : Hilbert ω) +
      action ω b ((classOf ω c : QSpace ω) : Hilbert ω)
  rw [action_mk, action_mk, action_mk, add_mul, classOf_add,
    UniformSpace.Completion.coe_add]

theorem action_smul (c : ℂ) (a : A) (x : Hilbert ω) :
    action ω (c • a) x = c • action ω a x := by
  refine UniformSpace.Completion.induction_on x
    (isClosed_eq (action ω (c • a)).continuous
      ((action ω a).continuous.const_smul c)) ?_
  intro q
  refine Quotient.inductionOn q ?_
  intro b
  change action ω (c • a) ((classOf ω b : QSpace ω) : Hilbert ω) =
    c • action ω a ((classOf ω b : QSpace ω) : Hilbert ω)
  rw [action_mk, action_mk, smul_mul_assoc, classOf_smul,
    UniformSpace.Completion.coe_smul]

/-- The general GNS representation is not restricted to characters. -/
def representation : A →ₗ[ℂ] (Hilbert ω →L[ℂ] Hilbert ω) where
  toFun := action ω
  map_add' := by
    intro a b
    ext x
    exact action_add ω a b x
  map_smul' := by
    intro c a
    ext x
    exact action_smul ω c a x

theorem representation_one (x : Hilbert ω) :
    representation ω (1 : A) x = x := action_one ω x

theorem representation_mul (a b : A) (x : Hilbert ω) :
    representation ω (a * b) x =
      representation ω a (representation ω b x) :=
  action_mul ω a b x

/-- This is the star condition, stated as the adjoint identity on Hilbert vectors. -/
theorem representation_adjoint (a : A) (x y : Hilbert ω) :
    inner ℂ (representation ω a x) y =
      inner ℂ x (representation ω (star a) y) := by
  refine UniformSpace.Completion.induction_on₂ x y
    (isClosed_eq (by fun_prop) (by fun_prop)) ?_
  intro q r
  refine Quotient.inductionOn₂ q r ?_
  intro b c
  change inner ℂ (action ω a ((classOf ω b : QSpace ω) : Hilbert ω))
      ((classOf ω c : QSpace ω) : Hilbert ω) =
    inner ℂ ((classOf ω b : QSpace ω) : Hilbert ω)
      (action ω (star a) ((classOf ω c : QSpace ω) : Hilbert ω))
  rw [action_mk, action_mk, UniformSpace.Completion.inner_coe,
    UniformSpace.Completion.inner_coe, inner_quotient_mk, inner_quotient_mk]
  simp only [form, star_mul, mul_assoc]

/-- The class of the unit is the cyclic GNS vector. -/
def cyclicVector : Hilbert ω :=
  ((classOf ω (1 : A) : QSpace ω) : Hilbert ω)

/-- The arbitrary positive normalized functional is exactly the vector state. -/
theorem state_identity (a : A) :
    inner ℂ (cyclicVector ω) (representation ω a (cyclicVector ω)) = ω a := by
  change inner ℂ
    ((classOf ω (1 : A) : QSpace ω) : Hilbert ω)
    (action ω a ((classOf ω (1 : A) : QSpace ω) : Hilbert ω)) = ω a
  rw [action_mk, UniformSpace.Completion.inner_coe, inner_quotient_mk]
  simp only [form, star_one, one_mul, mul_one]

/-- Normalization of the functional gives a unit-length cyclic vector. -/
theorem norm_cyclicVector (hω : ω 1 = 1) : ‖cyclicVector ω‖ = 1 := by
  change ‖((classOf ω (1 : A) : QSpace ω) : Hilbert ω)‖ = 1
  rw [UniformSpace.Completion.norm_coe, norm_quotient_mk]
  simp only [seminorm, form, star_one, one_mul, hω, Complex.one_re, Real.sqrt_one]

/-- The represented unit orbit contains every quotient class, so it is dense. -/
theorem cyclic_dense :
    DenseRange (fun a : A => representation ω a (cyclicVector ω)) := by
  have hrange :
      Set.range (fun a : A => representation ω a (cyclicVector ω)) =
      Set.range (fun q : QSpace ω => (q : Hilbert ω)) := by
    ext x
    constructor
    · rintro ⟨a, rfl⟩
      refine ⟨classOf ω a, ?_⟩
      change ((classOf ω a : QSpace ω) : Hilbert ω) =
        action ω a ((classOf ω (1 : A) : QSpace ω) : Hilbert ω)
      rw [action_mk, mul_one]
    · rintro ⟨q, rfl⟩
      obtain ⟨a, rfl⟩ := classOf_surjective ω q
      refine ⟨a, ?_⟩
      change action ω a ((classOf ω (1 : A) : QSpace ω) : Hilbert ω) =
        ((classOf ω a : QSpace ω) : Hilbert ω)
      rw [action_mk, mul_one]
  change Dense (Set.range (fun a : A => representation ω a (cyclicVector ω)))
  rw [hrange]
  exact UniformSpace.Completion.denseRange_coe

/-- All assertions here hold for a general positive normalized state. -/
def GeneralGNSGoal : Prop :=
    ‖cyclicVector ω‖ = 1 ∧
    (∀ a : A, ∀ x : Hilbert ω, ‖representation ω a x‖ ≤ ‖a‖ * ‖x‖) ∧
    (∀ x : Hilbert ω, representation ω (1 : A) x = x) ∧
    (∀ a b : A, ∀ x : Hilbert ω,
      representation ω (a * b) x = representation ω a (representation ω b x)) ∧
    (∀ a : A, ∀ x y : Hilbert ω,
      inner ℂ (representation ω a x) y =
        inner ℂ x (representation ω (star a) y)) ∧
    (∀ a : A, inner ℂ (cyclicVector ω)
      (representation ω a (cyclicVector ω)) = ω a) ∧
    DenseRange (fun a : A => representation ω a (cyclicVector ω))

theorem generalGNSGoal (hω : ω 1 = 1) : GeneralGNSGoal ω := by
  exact ⟨norm_cyclicVector ω hω, action_bound ω, representation_one ω, representation_mul ω,
    representation_adjoint ω, state_identity ω, cyclic_dense ω⟩

/-! ## Character specialization and a noncharacter matrix control -/

theorem character_null_iff
    (hmul : ∀ a b : A, ω (a * b) = ω a * ω b) (a : A) :
    a ∈ nullSubmodule ω ↔ ω a = 0 := by
  constructor
  · intro ha
    have h : star (ω a) * ω a = 0 := by
      rw [← map_star, ← hmul]
      exact (mem_nullSubmodule ω a).mp ha
    rcases mul_eq_zero.mp h with hs | hs
    · have hz := congrArg star hs
      simpa only [star_star, star_zero] using hz
    · exact hs
  · intro ha
    apply (mem_nullSubmodule ω a).mpr
    change ω (star a * a) = 0
    rw [hmul, ha, mul_zero]

def characterQuotientLinear
    (hmul : ∀ a b : A, ω (a * b) = ω a * ω b) : QSpace ω →ₗ[ℂ] ℂ :=
  (nullSubmodule ω).liftQ ω.toLinearMap (by
    intro a ha
    change ω a = 0
    exact (character_null_iff ω hmul a).mp ha)

@[simp]
theorem characterQuotientLinear_mk
    (hmul : ∀ a b : A, ω (a * b) = ω a * ω b) (a : A) :
    characterQuotientLinear ω hmul (classOf ω a) = ω a := rfl

theorem characterQuotientLinear_bijective (hω : ω 1 = 1)
    (hmul : ∀ a b : A, ω (a * b) = ω a * ω b) :
    Function.Bijective (characterQuotientLinear ω hmul) := by
  constructor
  · intro x y heq
    obtain ⟨a, rfl⟩ := classOf_surjective ω x
    obtain ⟨b, rfl⟩ := classOf_surjective ω y
    apply (Submodule.Quotient.eq (nullSubmodule ω)).mpr
    apply (character_null_iff ω hmul (a - b)).mpr
    have hv : ω a = ω b := by
      simpa only [characterQuotientLinear_mk] using heq
    simp only [map_sub, sub_eq_zero]
    exact hv
  · intro z
    refine ⟨classOf ω (z • (1 : A)), ?_⟩
    rw [characterQuotientLinear_mk, map_smul, hω, smul_eq_mul, mul_one]

def characterQuotientEquiv (hω : ω 1 = 1)
    (hmul : ∀ a b : A, ω (a * b) = ω a * ω b) : QSpace ω ≃ₗ[ℂ] ℂ :=
  LinearEquiv.ofBijective (characterQuotientLinear ω hmul)
    (characterQuotientLinear_bijective ω hω hmul)

/-- The character quotient retains the actual state-induced inner product. -/
theorem characterQuotientLinear_inner
    (hmul : ∀ a b : A, ω (a * b) = ω a * ω b) (x y : QSpace ω) :
    inner ℂ x y = star (characterQuotientLinear ω hmul x) *
      characterQuotientLinear ω hmul y := by
  obtain ⟨a, rfl⟩ := classOf_surjective ω x
  obtain ⟨b, rfl⟩ := classOf_surjective ω y
  rw [inner_quotient_mk, characterQuotientLinear_mk, characterQuotientLinear_mk]
  simp only [form, hmul, map_star]

/-- The diagonal two-by-two complex matrix algebra. -/
abbrev DiagonalTwo := Fin 2 → ℂ

/-- The pointwise order on the diagonal algebra is its star order. -/
instance diagonalTwoStarOrderedRing : StarOrderedRing DiagonalTwo :=
  StarOrderedRing.of_nonneg_iff'
    (fun {a b} hab c i => add_le_add_left (hab i) (c i))
    (fun a => by
      constructor
      · intro ha
        refine ⟨fun i => (Real.sqrt (a i).re : ℂ), ?_⟩
        funext i
        have hi := Complex.nonneg_iff.mp (ha i)
        change a i = star (Real.sqrt (a i).re : ℂ) * (Real.sqrt (a i).re : ℂ)
        apply Complex.ext <;> simp [hi.1, ← hi.2]
      · rintro ⟨b, rfl⟩
        intro i
        exact star_mul_self_nonneg (b i))

noncomputable def diagonalTwoState : DiagonalTwo →ₚ[ℂ] ℂ :=
  PositiveLinearMap.mk₀
    { toFun := fun a => (1 / 2 : ℝ) • (a 0 + a 1)
      map_add' := by
        intro a b
        change (1 / 2 : ℝ) • ((a 0 + b 0) + (a 1 + b 1)) =
          (1 / 2 : ℝ) • (a 0 + a 1) + (1 / 2 : ℝ) • (b 0 + b 1)
        simp only [smul_add]
        abel
      map_smul' := by
        intro c a
        change (1 / 2 : ℝ) • (c • a 0 + c • a 1) =
          c • ((1 / 2 : ℝ) • (a 0 + a 1))
        rw [← smul_add, smul_comm] }
    (by
      intro a ha
      change 0 ≤ (1 / 2 : ℝ) • (a 0 + a 1)
      have h0 : 0 ≤ a 0 := (Pi.le_def.mp ha) 0
      have h1 : 0 ≤ a 1 := (Pi.le_def.mp ha) 1
      exact smul_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) (add_nonneg h0 h1))

theorem diagonalTwoState_one : diagonalTwoState 1 = 1 := by
  change (1 / 2 : ℝ) • ((1 : ℂ) + 1) = 1
  norm_num

def diagonalTwoProjection : DiagonalTwo := fun i => if i = 0 then 1 else 0

def diagonalTwoProjectionMatrix : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.diagonal diagonalTwoProjection

theorem diagonalTwoProjection_idempotent :
    diagonalTwoProjection * diagonalTwoProjection = diagonalTwoProjection := by
  funext i
  fin_cases i <;> norm_num [diagonalTwoProjection]

theorem diagonalTwoProjectionMatrix_idempotent :
    diagonalTwoProjectionMatrix * diagonalTwoProjectionMatrix = diagonalTwoProjectionMatrix := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [diagonalTwoProjectionMatrix, diagonalTwoProjection,
      Matrix.diagonal, Matrix.mul_apply, Fin.sum_univ_two]

theorem diagonalTwoProjection_expectation :
    diagonalTwoState diagonalTwoProjection = (1 / 2 : ℂ) := by
  change (1 / 2 : ℝ) • ((1 : ℂ) + 0) = 1 / 2
  norm_num

theorem diagonalTwoState_not_character :
    ¬ (∀ a b : DiagonalTwo,
      diagonalTwoState (a * b) = diagonalTwoState a * diagonalTwoState b) := by
  intro hm
  have h := hm diagonalTwoProjection diagonalTwoProjection
  rw [diagonalTwoProjection_idempotent, diagonalTwoProjection_expectation] at h
  norm_num at h

theorem diagonalTwoNoncharacterGNS :
    (¬ (∀ a b : DiagonalTwo,
      diagonalTwoState (a * b) = diagonalTwoState a * diagonalTwoState b)) ∧
    GeneralGNSGoal diagonalTwoState :=
  ⟨diagonalTwoState_not_character, generalGNSGoal diagonalTwoState diagonalTwoState_one⟩


/-! ## Compatible stage states recovered by their general GNS representation -/
section CompatibleStageRecovery
universe u₁
variable {ι : Type u₁} [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
variable {S : ReconstructionLimitCompletion.IsometricStarSystem ι}
variable [∀ i, PartialOrder (S.Fiber i)] [∀ i, StarOrderedRing (S.Fiber i)]
variable (Ω : ReconstructionLimitCompletion.CompatibleStateFamily S)

/-- The same completed state recovers every compatible stage expectation. -/
theorem compatibleStageGNSIdentity (i : ι) (a : S.Fiber i) :
    inner ℂ (cyclicVector Ω.completionState)
      (representation Ω.completionState (S.stageMap i a)
        (cyclicVector Ω.completionState)) = Ω.state i a := by
  exact (state_identity Ω.completionState (S.stageMap i a)).trans
    (Ω.completionState_on_stage i a)

/-- Stage expectations determine the continuous completed state uniquely. -/
theorem compatibleGNSStateUnique (f : S.Completion →L[ℂ] ℂ)
    (hf : ∀ i (a : S.Fiber i), f (S.stageMap i a) =
      inner ℂ (cyclicVector Ω.completionState)
        (representation Ω.completionState (S.stageMap i a)
          (cyclicVector Ω.completionState))) :
    f = Ω.completionLinear := by
  apply Ω.completionLinear_unique f
  intro i a
  rw [hf i a, compatibleStageGNSIdentity Ω i a]

/-- Unit norm follows from the actual completed-state normalization. -/
theorem compatibleGNSUnitVector : ‖cyclicVector Ω.completionState‖ = 1 :=
  norm_cyclicVector Ω.completionState Ω.completionState_one

end CompatibleStageRecovery

end OperatorKO7.Meta.BoundaryObserver.ReconstructionGeneralGNS
