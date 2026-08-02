import OperatorKO7.Meta.BoundaryGeneral.VectorOrderRepair
import OperatorKO7.Meta.OperationalInexpressibility.DirectGrammarBoundary
import OperatorKO7.Meta.Recursor.CanonicalExecution
import OperatorKO7.Meta.Recursor.MassProfileIdentity
import OperatorKO7.Meta.UniversalBoundary.BoundaryPrimitive
import OperatorKO7.Meta.WitnessOrder

/-!
# Concrete KO7 observation/verdict boundary

The meta-level observer below is the complete orientability profile over an
explicit fourteen-constructor syntax: Paper A's twelve foundational direct
families and its two tracked-lex continuations.  It is not the Boolean
assertion that some certificate exists.  The two compared systems use actual
relations on the shared `Trace` carrier: the terminating KO7 root relation
`Step`, and `MassProfileIdentity.SelfEmbeddingStep`.

The object-level surface remains separate.  The only fixed-input object
observer claimed here is the named projected-counter theorem exported from
`Recursor.CanonicalExecution`; the input-family mass identity is not used as a
fixed-execution or termination theorem.
-/

set_option autoImplicit false

namespace OperatorKO7.Meta.OperationalInexpressibility.KO7ObservationVerdict

open OperatorKO7
open OperatorKO7.Trace
open OperatorKO7.CompositionalImpossibility
open OperatorKO7.DepthBarrier
open OperatorKO7.PrecedenceBarrier
open OperatorKO7.EscapeTrichotomy
open OperatorKO7.PumpedBarrierClasses
open OperatorKO7.MatrixBarrierLexD
open OperatorKO7.MatrixBarrierLexPermD
open OperatorKO7.StepDuplicating.StepDuplicatingSchema
open OperatorKO7.Meta.BoundaryGeneral.VectorOrderRepair
open OperatorKO7.Meta.OperationalInexpressibility.DirectGrammarBoundary
open OperatorKO7.Meta.Recursor.MassProfileIdentity
open OperatorKO7.Meta.UniversalBoundary.BoundaryPrimitive

/-! ## Declared candidate syntax and relation-relative orientation -/

/-- Codomain/order syntax needed by the twelve foundational direct families
and the two finite tracked-lex continuations. -/
inductive DeclaredDirectOrienter where
  | nat (measure : Trace → Nat)
  | pairComponentwise (measure : Trace → Vec2)
  | pairLex (measure : Trace → Vec2)
  | vecComponentwise (d : Nat) (measure : Trace → Fin d → Nat)
  | vecLex (d : Nat) (measure : Trace → Fin (d + 1) → Nat)
  | vecPermLex (d : Nat) (priority : Equiv.Perm (Fin (d + 1)))
      (measure : Trace → Fin (d + 1) → Nat)

/-- Exact proof-bearing enumerated universe from Paper A: eight scalar base
families, four vector/pair base families, and two tracked-lex continuations.
Nothing outside these fourteen constructors is classified here. -/
inductive DeclaredDirectBarrierRepresentable : DeclaredDirectOrienter → Prop
  | additive (M : AdditiveCompositionalMeasure) :
      DeclaredDirectBarrierRepresentable (.nat M.eval)
  | compositionalTransparent (CM : CompositionalMeasure)
      (htransparent : CM.c_delta CM.c_void = CM.c_void) :
      DeclaredDirectBarrierRepresentable (.nat CM.eval)
  | affineWithPump (M : AffineMeasureWithPump ko7Schema) :
      DeclaredDirectBarrierRepresentable (.nat M.eval)
  | quadraticWithPump (M : QuadraticCounterMeasureWithPump ko7Schema) :
      DeclaredDirectBarrierRepresentable (.nat M.eval)
  | crossQuadraticWithPump (M : CrossTermQuadraticMeasureWithPump ko7Schema) :
      DeclaredDirectBarrierRepresentable (.nat M.eval)
  | multilinearWithPump (M : MultilinearMeasureWithPump ko7Schema) :
      DeclaredDirectBarrierRepresentable (.nat M.eval)
  | polynomialWithPump (M : PolynomialMeasureWithPump ko7Schema) :
      DeclaredDirectBarrierRepresentable (.nat M.eval)
  | maxWithPump (M : MaxMeasureWithPump ko7Schema) :
      DeclaredDirectBarrierRepresentable (.nat M.eval)
  | matrix2ComponentwiseWithPrimaryPump
      (M : MatrixMeasure2WithPrimaryPump ko7Schema) :
      DeclaredDirectBarrierRepresentable (.pairComponentwise M.eval)
  | matrix2LexWithPrimaryPump
      (M : MatrixMeasure2WithPrimaryPump ko7Schema) :
      DeclaredDirectBarrierRepresentable (.pairLex M.eval)
  | matrixMix2WithSumPump (M : MatrixMix2MeasureWithSumPump ko7Schema) :
      DeclaredDirectBarrierRepresentable (.pairComponentwise M.eval)
  | matrixFunctionalWithProjectedAffinePump {d : Nat}
      (M : MatrixFunctionalMeasureWithProjectedAffinePump ko7Schema d) :
      DeclaredDirectBarrierRepresentable (.vecComponentwise d M.eval)
  | matrixLexDWithPrimaryPump {d : Nat}
      (M : MatrixLexMeasureDWithPrimaryPump ko7Schema d) :
      DeclaredDirectBarrierRepresentable (.vecLex d M.eval)
  | matrixLexPermWithPrimaryPump {d : Nat}
      (M : MatrixLexPermMeasureDWithPrimaryPump ko7Schema d) :
      DeclaredDirectBarrierRepresentable
        (.vecPermLex d M.priority M.eval)

/-- One candidate in the exact fourteen-family universe. -/
structure Candidate where
  orienter : DeclaredDirectOrienter
  declared : DeclaredDirectBarrierRepresentable orienter

/-- Sigma presentation of the exact proof-bearing declared universe. -/
def DeclaredDirectUniverse : Type :=
  {orienter : DeclaredDirectOrienter //
    DeclaredDirectBarrierRepresentable orienter}

/-- Canonical map from Paper A's proof-bearing declared universe into the
candidate type observed by the operational-inexpressibility profile. -/
def candidateOfDeclaredDirectUniverse
    (entry : DeclaredDirectUniverse) : Candidate :=
  ⟨entry.1, entry.2⟩

/-- Concrete inhabitant of the declared direct universe, built from the actual
simple-size additive measure rather than from an assumed candidate. -/
def simpleSizeDeclaredDirectUniverse : DeclaredDirectUniverse :=
  ⟨.nat OperatorKO7.CompositionalImpossibility.simpleSize_ACM.eval,
    DeclaredDirectBarrierRepresentable.additive
      OperatorKO7.CompositionalImpossibility.simpleSize_ACM⟩

/-! ## Concrete inhabitance of all fourteen declared families -/

/-- A single constructor-local linear evaluation used to inhabit the affine,
restricted polynomial, tracked-pair, and tracked-vector families. -/
def declaredLinearEval : Trace → Nat
  | void => 0
  | delta t => 1 + declaredLinearEval t
  | integrate t => declaredLinearEval t
  | merge x y => 1 + declaredLinearEval x + declaredLinearEval y
  | app x y => 1 + declaredLinearEval x + declaredLinearEval y
  | recΔ b s n =>
      1 + declaredLinearEval b + declaredLinearEval s + declaredLinearEval n
  | eqW x y => 1 + declaredLinearEval x + declaredLinearEval y

/-- Concrete transparent-successor compositional witness. -/
def declaredTransparentCompositionalMeasure : CompositionalMeasure where
  c_void := 0
  c_delta := fun n => n
  c_integrate := fun n => n
  c_merge := fun x y => x + y + 1
  c_app := fun x y => x + y + 1
  c_recΔ := fun b s n => b + s + n + 1
  c_eqW := fun x y => x + y + 1
  app_subterm1 := by
    intro x y
    omega
  app_subterm2 := by
    intro x y
    omega

/-- The concrete compositional witness has transparent `delta` at its base. -/
theorem declaredTransparentCompositionalMeasure_transparent :
    declaredTransparentCompositionalMeasure.c_delta
        declaredTransparentCompositionalMeasure.c_void =
      declaredTransparentCompositionalMeasure.c_void := by
  rfl

/-- Concrete affine constructor-local witness with positive successor pump. -/
def declaredAffineMeasure : AffineMeasure ko7Schema where
  eval := declaredLinearEval
  c_base := 0
  succ_bias := 1
  succ_scale := 1
  wrap_const := 1
  wrap_left := 1
  wrap_right := 1
  recur_const := 1
  recur_base := 1
  recur_step := 1
  recur_counter := 1
  eval_base := by simp [ko7Schema, declaredLinearEval]
  eval_succ := by
    intro t
    simp [ko7Schema, declaredLinearEval]
  eval_wrap := by
    intro x y
    simp [ko7Schema, declaredLinearEval, Nat.add_assoc]
  eval_recur := by
    intro b s n
    simp [ko7Schema, declaredLinearEval, Nat.add_assoc]
  h_wrap_left_pos := by simp
  h_wrap_right_pos := by simp

def declaredAffineWithPump : AffineMeasureWithPump ko7Schema where
  toAffineMeasure := declaredAffineMeasure
  has_pump := Or.inl ⟨by simp [declaredAffineMeasure], by simp [declaredAffineMeasure]⟩

/-- Concrete restricted-quadratic witness; its quadratic coefficient is zero,
so it is a genuine inhabited member of the declared restricted class. -/
def declaredQuadraticCounterMeasure : QuadraticCounterMeasure ko7Schema where
  eval := declaredLinearEval
  c_base := 0
  succ_bias := 1
  succ_scale := 1
  wrap_const := 1
  wrap_left := 1
  wrap_right := 1
  recur_const := 1
  recur_base := 1
  recur_step := 1
  recur_counter := 1
  recur_quad := 0
  eval_base := by simp [ko7Schema, declaredLinearEval]
  eval_succ := by
    intro t
    simp [ko7Schema, declaredLinearEval]
  eval_wrap := by
    intro x y
    simp [ko7Schema, declaredLinearEval, Nat.add_assoc]
  eval_recur := by
    intro b s n
    simp [ko7Schema, declaredLinearEval, Nat.add_assoc]
  h_wrap_left_pos := by simp
  h_wrap_right_pos := by simp

def declaredQuadraticWithPump : QuadraticCounterMeasureWithPump ko7Schema where
  toQuadraticCounterMeasure := declaredQuadraticCounterMeasure
  has_pump :=
    Or.inl ⟨by simp [declaredQuadraticCounterMeasure],
      by simp [declaredQuadraticCounterMeasure]⟩

/-- Concrete bounded cross-term witness with the optional quadratic and cross
coefficients specialized to zero. -/
def declaredCrossTermQuadraticMeasure : CrossTermQuadraticMeasure ko7Schema where
  eval := declaredLinearEval
  c_base := 0
  succ_bias := 1
  succ_scale := 1
  wrap_const := 1
  wrap_left := 1
  wrap_right := 1
  recur_const := 1
  recur_base := 1
  recur_step := 1
  recur_counter := 1
  recur_quad := 0
  recur_cross := 0
  eval_base := by simp [ko7Schema, declaredLinearEval]
  eval_succ := by
    intro t
    simp [ko7Schema, declaredLinearEval]
  eval_wrap := by
    intro x y
    simp [ko7Schema, declaredLinearEval, Nat.add_assoc]
  eval_recur := by
    intro b s n
    simp [ko7Schema, declaredLinearEval, Nat.add_assoc]
  h_wrap_left_pos := by simp
  h_wrap_right_pos := by simp

def declaredCrossQuadraticWithPump : CrossTermQuadraticMeasureWithPump ko7Schema where
  toCrossTermQuadraticMeasure := declaredCrossTermQuadraticMeasure
  has_pump :=
    Or.inl ⟨by simp [declaredCrossTermQuadraticMeasure],
      by simp [declaredCrossTermQuadraticMeasure]⟩
  h_bounded := by
    norm_num [CrossTermBoundedAtBase, declaredCrossTermQuadraticMeasure]

/-- Empty higher-order table gives a concrete member of the bounded
multilinear family while retaining the positive affine pump. -/
def declaredBoundedMultilinearMeasure : BoundedMultilinearMeasure ko7Schema where
  eval := declaredLinearEval
  c_base := 0
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
  eval_base := by simp [ko7Schema, declaredLinearEval]
  eval_succ := by
    intro t
    simp [ko7Schema, declaredLinearEval]
  eval_wrap := by
    intro x y
    simp [ko7Schema, declaredLinearEval, Nat.add_assoc]
  eval_recur := by
    intro b s n
    simp [ko7Schema, declaredLinearEval, Nat.add_assoc]
  h_wrap_left_pos := by simp
  h_wrap_right_pos := by simp

def declaredMultilinearWithPump : MultilinearMeasureWithPump ko7Schema where
  toBoundedMultilinearMeasure := declaredBoundedMultilinearMeasure
  has_pump :=
    Or.inl ⟨by simp [declaredBoundedMultilinearMeasure],
      by simp [declaredBoundedMultilinearMeasure]⟩
  h_dominated := by
    norm_num [MultilinearDominatedAtBase, declaredBoundedMultilinearMeasure]

/-- Empty nonlinear table gives a concrete member of the generalized bounded
polynomial family. -/
def declaredBoundedPolynomialMeasure : BoundedPolynomialMeasure ko7Schema where
  eval := declaredLinearEval
  c_base := 0
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
  eval_base := by simp [ko7Schema, declaredLinearEval]
  eval_succ := by
    intro t
    simp [ko7Schema, declaredLinearEval]
  eval_wrap := by
    intro x y
    simp [ko7Schema, declaredLinearEval, Nat.add_assoc]
  eval_recur := by
    intro b s n
    simp [ko7Schema, declaredLinearEval, Nat.add_assoc]
  h_wrap_left_pos := by simp
  h_wrap_right_pos := by simp

def declaredPolynomialWithPump : PolynomialMeasureWithPump ko7Schema where
  toBoundedPolynomialMeasure := declaredBoundedPolynomialMeasure
  has_pump :=
    Or.inl ⟨by simp [declaredBoundedPolynomialMeasure],
      by simp [declaredBoundedPolynomialMeasure]⟩
  h_dominated := by
    refine ⟨0, ?_⟩
    intro stepValue _
    simp [declaredBoundedPolynomialMeasure]

/-- Recursive max-plus evaluation matching the concrete max-family
coefficients below. -/
def declaredMaxEval : Trace → Nat
  | void => 0
  | delta t => 1 + declaredMaxEval t
  | integrate t => declaredMaxEval t
  | merge x y => max (declaredMaxEval x) (declaredMaxEval y)
  | app x y => max (declaredMaxEval x) (1 + declaredMaxEval y)
  | recΔ b s n =>
      max (declaredMaxEval b) (max (declaredMaxEval s) (declaredMaxEval n))
  | eqW x y => max (declaredMaxEval x) (declaredMaxEval y)

def declaredMaxMeasure : MaxMeasure ko7Schema where
  eval := declaredMaxEval
  c_base := 0
  succ_const := 1
  wrap_const := 0
  wrap_left := 0
  wrap_right := 1
  recur_const := 0
  recur_base := 0
  recur_step := 0
  recur_counter := 0
  eval_base := by simp [ko7Schema, declaredMaxEval]
  eval_succ := by
    intro t
    simp [ko7Schema, declaredMaxEval]
  eval_wrap := by
    intro x y
    simp [ko7Schema, declaredMaxEval]
  eval_recur := by
    intro b s n
    simp [ko7Schema, declaredMaxEval]
  h_wrap_right_pos := by simp

def declaredMaxWithPump : MaxMeasureWithPump ko7Schema where
  toMaxMeasure := declaredMaxMeasure
  has_pump := Or.inl (by simp [declaredMaxMeasure])

/-- Two identical tracked affine coordinates give a concrete member of both
declared dimension-two order families. -/
def declaredPairEval (t : Trace) : Vec2 :=
  (declaredLinearEval t, declaredLinearEval t)

def declaredMatrixMeasure2 : MatrixMeasure2 ko7Schema where
  eval := declaredPairEval
  c_base1 := 0
  c_base2 := 0
  succ_bias1 := 1
  succ_scale1 := 1
  succ_bias2 := 1
  succ_scale2 := 1
  wrap_const1 := 1
  wrap_left1 := 1
  wrap_right1 := 1
  wrap_const2 := 1
  wrap_left2 := 1
  wrap_right2 := 1
  recur_const1 := 1
  recur_base1 := 1
  recur_step1 := 1
  recur_counter1 := 1
  recur_const2 := 1
  recur_base2 := 1
  recur_step2 := 1
  recur_counter2 := 1
  eval_base := by simp [ko7Schema, declaredPairEval, declaredLinearEval]
  eval_succ1 := by
    intro t
    simp [ko7Schema, declaredPairEval, declaredLinearEval]
  eval_succ2 := by
    intro t
    simp [ko7Schema, declaredPairEval, declaredLinearEval]
  eval_wrap1 := by
    intro x y
    simp [ko7Schema, declaredPairEval, declaredLinearEval, Nat.add_assoc]
  eval_wrap2 := by
    intro x y
    simp [ko7Schema, declaredPairEval, declaredLinearEval, Nat.add_assoc]
  eval_recur1 := by
    intro b s n
    simp [ko7Schema, declaredPairEval, declaredLinearEval, Nat.add_assoc]
  eval_recur2 := by
    intro b s n
    simp [ko7Schema, declaredPairEval, declaredLinearEval, Nat.add_assoc]
  h_wrap_left1_pos := by simp
  h_wrap_right1_pos := by simp

def declaredMatrixMeasure2WithPrimaryPump : MatrixMeasure2WithPrimaryPump ko7Schema where
  toMatrixMeasure2 := declaredMatrixMeasure2
  has_primary_pump :=
    Or.inl ⟨by simp [declaredMatrixMeasure2], by simp [declaredMatrixMeasure2]⟩

/-- Identity coefficient map used by the balanced mixed-coordinate fixture. -/
def declaredIdentityLin2 : Lin2 where
  a11 := 1
  a12 := 0
  a21 := 0
  a22 := 1

/-- Concrete balanced mixed-coordinate base-family witness. -/
def declaredMatrixMix2Measure : MatrixMix2Measure ko7Schema where
  eval := declaredPairEval
  c_base := (0, 0)
  succ_bias := (1, 1)
  succ_mat := declaredIdentityLin2
  wrap_bias := (1, 1)
  wrap_left := declaredIdentityLin2
  wrap_right := declaredIdentityLin2
  recur_bias := (1, 1)
  recur_base := declaredIdentityLin2
  recur_step := declaredIdentityLin2
  recur_counter := declaredIdentityLin2
  eval_base := by
    simp [ko7Schema, declaredPairEval, declaredLinearEval]
  eval_succ := by
    intro t
    simp [ko7Schema, declaredPairEval, declaredLinearEval,
      declaredIdentityLin2, Lin2.act]
  eval_wrap := by
    intro x y
    simp [ko7Schema, declaredPairEval, declaredLinearEval,
      declaredIdentityLin2, Lin2.act, Nat.add_assoc]
  eval_recur := by
    intro b s n
    simp [ko7Schema, declaredPairEval, declaredLinearEval,
      declaredIdentityLin2, Lin2.act, Nat.add_assoc]
  h_succ_balanced := by
    simp [declaredIdentityLin2, Lin2.Balanced]
  h_wrap_left_balanced := by
    simp [declaredIdentityLin2, Lin2.Balanced]
  h_wrap_right_balanced := by
    simp [declaredIdentityLin2, Lin2.Balanced]
  h_recur_base_balanced := by
    simp [declaredIdentityLin2, Lin2.Balanced]
  h_recur_step_balanced := by
    simp [declaredIdentityLin2, Lin2.Balanced]
  h_recur_counter_balanced := by
    simp [declaredIdentityLin2, Lin2.Balanced]
  h_wrap_left_pos := by
    simp [declaredIdentityLin2, Lin2.sumCoeff]
  h_wrap_right_pos := by
    simp [declaredIdentityLin2, Lin2.sumCoeff]

def declaredMatrixMix2WithSumPump : MatrixMix2MeasureWithSumPump ko7Schema where
  toMatrixMix2Measure := declaredMatrixMix2Measure
  has_sum_pump := Or.inl
    ⟨by norm_num [declaredMatrixMix2Measure, vecSum],
      by norm_num [declaredMatrixMix2Measure, declaredIdentityLin2, Lin2.sumCoeff]⟩

/-- One-coordinate vector and unit weight used by the weighted
scalar-projection base-family fixture. -/
def declaredFunctionalEval (t : Trace) (_i : Fin 1) : Nat :=
  declaredLinearEval t

def declaredUnitWeight (_i : Fin 1) : Nat := 1

def declaredMatrixFunctionalMeasure1 : MatrixFunctionalMeasure ko7Schema 1 where
  eval := declaredFunctionalEval
  weight := declaredUnitWeight
  c_base := 0
  succ_bias := 1
  succ_scale := 1
  wrap_const := 1
  wrap_left := 1
  wrap_right := 1
  recur_const := 1
  recur_base := 1
  recur_step := 1
  recur_counter := 1
  eval_base := by
    simp [weightedSum, ko7Schema, declaredFunctionalEval, declaredUnitWeight,
      declaredLinearEval]
  eval_succ := by
    intro t
    simp [weightedSum, ko7Schema, declaredFunctionalEval, declaredUnitWeight,
      declaredLinearEval]
  eval_wrap := by
    intro x y
    simp [weightedSum, ko7Schema, declaredFunctionalEval, declaredUnitWeight,
      declaredLinearEval, Nat.add_assoc]
  eval_recur := by
    intro b s n
    simp [weightedSum, ko7Schema, declaredFunctionalEval, declaredUnitWeight,
      declaredLinearEval, Nat.add_assoc]
  h_weight_support := ⟨0, by simp [declaredUnitWeight]⟩
  h_wrap_left_pos := by simp
  h_wrap_right_pos := by simp

def declaredMatrixFunctionalMeasure1WithProjectedAffinePump :
    MatrixFunctionalMeasureWithProjectedAffinePump ko7Schema 1 where
  toMatrixFunctionalMeasure := declaredMatrixFunctionalMeasure1
  has_pump := Or.inl ⟨by simp [declaredMatrixFunctionalMeasure1],
    by simp [declaredMatrixFunctionalMeasure1]⟩

/-- Coordinate-independent finite vector fixture; the tracked primary
coordinate is the same concrete affine evaluation at every coordinate. -/
def declaredVectorEval (t : Trace) (_i : Fin 2) : Nat :=
  declaredLinearEval t

def declaredMatrixLexMeasure1 : MatrixLexMeasureD ko7Schema 1 where
  eval := declaredVectorEval
  c_base := 0
  succ_bias := 1
  succ_scale := 1
  wrap_const := 1
  wrap_left := 1
  wrap_right := 1
  recur_const := 1
  recur_base := 1
  recur_step := 1
  recur_counter := 1
  eval_base := by simp [ko7Schema, declaredVectorEval, declaredLinearEval]
  eval_succ := by
    intro t
    simp [ko7Schema, declaredVectorEval, declaredLinearEval]
  eval_wrap := by
    intro x y
    simp [ko7Schema, declaredVectorEval, declaredLinearEval, Nat.add_assoc]
  eval_recur := by
    intro b s n
    simp [ko7Schema, declaredVectorEval, declaredLinearEval, Nat.add_assoc]
  h_wrap_left_pos := by simp
  h_wrap_right_pos := by simp

def declaredMatrixLexMeasure1WithPrimaryPump :
    MatrixLexMeasureDWithPrimaryPump ko7Schema 1 where
  toMatrixLexMeasureD := declaredMatrixLexMeasure1
  has_primary_pump :=
    Or.inl ⟨by simp [declaredMatrixLexMeasure1],
      by simp [declaredMatrixLexMeasure1]⟩

def declaredMatrixLexPermMeasure1 : MatrixLexPermMeasureD ko7Schema 1 where
  priority := Equiv.refl _
  eval := declaredVectorEval
  c_base := 0
  succ_bias := 1
  succ_scale := 1
  wrap_const := 1
  wrap_left := 1
  wrap_right := 1
  recur_const := 1
  recur_base := 1
  recur_step := 1
  recur_counter := 1
  eval_base := by simp [ko7Schema, declaredVectorEval, declaredLinearEval]
  eval_succ := by
    intro t
    simp [ko7Schema, declaredVectorEval, declaredLinearEval]
  eval_wrap := by
    intro x y
    simp [ko7Schema, declaredVectorEval, declaredLinearEval, Nat.add_assoc]
  eval_recur := by
    intro b s n
    simp [ko7Schema, declaredVectorEval, declaredLinearEval, Nat.add_assoc]
  h_wrap_left_pos := by simp
  h_wrap_right_pos := by simp

def declaredMatrixLexPermMeasure1WithPrimaryPump :
    MatrixLexPermMeasureDWithPrimaryPump ko7Schema 1 where
  toMatrixLexPermMeasureD := declaredMatrixLexPermMeasure1
  has_primary_pump :=
    Or.inl ⟨by simp [declaredMatrixLexPermMeasure1],
      by simp [declaredMatrixLexPermMeasure1]⟩

/-! ## Exact fourteen-tag declared-family ledger -/

/-- Paper A's exact twelve foundational families in manuscript order, followed
by the finite tracked-primary and permutation-priority lex continuations. -/
inductive DeclaredFamilyTag
  | additive
  | compositionalTransparent
  | affineWithPump
  | quadraticWithPump
  | crossQuadraticWithPump
  | multilinearWithPump
  | polynomialWithPump
  | maxWithPump
  | matrix2ComponentwiseWithPrimaryPump
  | matrix2LexWithPrimaryPump
  | matrixMix2WithSumPump
  | matrixFunctionalWithProjectedAffinePump
  | matrixLexDWithPrimaryPump
  | matrixLexPermWithPrimaryPump
  deriving DecidableEq, Fintype, Repr

/-- Exact proposition-level constructor match between a tag and a
proof-bearing declared-universe witness.  The fourteen constructors mirror
`DeclaredDirectBarrierRepresentable` without eliminating that proposition into
data. -/
inductive DeclaredFamilyMatches :
    DeclaredFamilyTag → DeclaredDirectUniverse → Prop
  | additive (M : AdditiveCompositionalMeasure) :
      DeclaredFamilyMatches .additive
        ⟨.nat M.eval, DeclaredDirectBarrierRepresentable.additive M⟩
  | compositionalTransparent (CM : CompositionalMeasure)
      (htransparent : CM.c_delta CM.c_void = CM.c_void) :
      DeclaredFamilyMatches .compositionalTransparent
        ⟨.nat CM.eval,
          DeclaredDirectBarrierRepresentable.compositionalTransparent CM
            htransparent⟩
  | affineWithPump (M : AffineMeasureWithPump ko7Schema) :
      DeclaredFamilyMatches .affineWithPump
        ⟨.nat M.eval, DeclaredDirectBarrierRepresentable.affineWithPump M⟩
  | quadraticWithPump (M : QuadraticCounterMeasureWithPump ko7Schema) :
      DeclaredFamilyMatches .quadraticWithPump
        ⟨.nat M.eval, DeclaredDirectBarrierRepresentable.quadraticWithPump M⟩
  | crossQuadraticWithPump (M : CrossTermQuadraticMeasureWithPump ko7Schema) :
      DeclaredFamilyMatches .crossQuadraticWithPump
        ⟨.nat M.eval,
          DeclaredDirectBarrierRepresentable.crossQuadraticWithPump M⟩
  | multilinearWithPump (M : MultilinearMeasureWithPump ko7Schema) :
      DeclaredFamilyMatches .multilinearWithPump
        ⟨.nat M.eval, DeclaredDirectBarrierRepresentable.multilinearWithPump M⟩
  | polynomialWithPump (M : PolynomialMeasureWithPump ko7Schema) :
      DeclaredFamilyMatches .polynomialWithPump
        ⟨.nat M.eval, DeclaredDirectBarrierRepresentable.polynomialWithPump M⟩
  | maxWithPump (M : MaxMeasureWithPump ko7Schema) :
      DeclaredFamilyMatches .maxWithPump
        ⟨.nat M.eval, DeclaredDirectBarrierRepresentable.maxWithPump M⟩
  | matrix2ComponentwiseWithPrimaryPump
      (M : MatrixMeasure2WithPrimaryPump ko7Schema) :
      DeclaredFamilyMatches .matrix2ComponentwiseWithPrimaryPump
        ⟨.pairComponentwise M.eval,
          DeclaredDirectBarrierRepresentable.matrix2ComponentwiseWithPrimaryPump M⟩
  | matrix2LexWithPrimaryPump
      (M : MatrixMeasure2WithPrimaryPump ko7Schema) :
      DeclaredFamilyMatches .matrix2LexWithPrimaryPump
        ⟨.pairLex M.eval,
          DeclaredDirectBarrierRepresentable.matrix2LexWithPrimaryPump M⟩
  | matrixMix2WithSumPump (M : MatrixMix2MeasureWithSumPump ko7Schema) :
      DeclaredFamilyMatches .matrixMix2WithSumPump
        ⟨.pairComponentwise M.eval,
          DeclaredDirectBarrierRepresentable.matrixMix2WithSumPump M⟩
  | matrixFunctionalWithProjectedAffinePump {d : Nat}
      (M : MatrixFunctionalMeasureWithProjectedAffinePump ko7Schema d) :
      DeclaredFamilyMatches .matrixFunctionalWithProjectedAffinePump
        ⟨.vecComponentwise d M.eval,
          DeclaredDirectBarrierRepresentable.matrixFunctionalWithProjectedAffinePump M⟩
  | matrixLexDWithPrimaryPump {d : Nat}
      (M : MatrixLexMeasureDWithPrimaryPump ko7Schema d) :
      DeclaredFamilyMatches .matrixLexDWithPrimaryPump
        ⟨.vecLex d M.eval,
          DeclaredDirectBarrierRepresentable.matrixLexDWithPrimaryPump M⟩
  | matrixLexPermWithPrimaryPump {d : Nat}
      (M : MatrixLexPermMeasureDWithPrimaryPump ko7Schema d) :
      DeclaredFamilyMatches .matrixLexPermWithPrimaryPump
        ⟨.vecPermLex d M.priority M.eval,
          DeclaredDirectBarrierRepresentable.matrixLexPermWithPrimaryPump M⟩

/-- A concrete candidate and genuine family witness for every declared tag. -/
def declaredFamilyCandidate : DeclaredFamilyTag → DeclaredDirectUniverse
  | .additive => simpleSizeDeclaredDirectUniverse
  | .compositionalTransparent =>
      ⟨.nat declaredTransparentCompositionalMeasure.eval,
        .compositionalTransparent declaredTransparentCompositionalMeasure
          declaredTransparentCompositionalMeasure_transparent⟩
  | .affineWithPump =>
      ⟨.nat declaredAffineWithPump.eval,
        .affineWithPump declaredAffineWithPump⟩
  | .quadraticWithPump =>
      ⟨.nat declaredQuadraticWithPump.eval,
        .quadraticWithPump declaredQuadraticWithPump⟩
  | .crossQuadraticWithPump =>
      ⟨.nat declaredCrossQuadraticWithPump.eval,
        .crossQuadraticWithPump declaredCrossQuadraticWithPump⟩
  | .multilinearWithPump =>
      ⟨.nat declaredMultilinearWithPump.eval,
        .multilinearWithPump declaredMultilinearWithPump⟩
  | .polynomialWithPump =>
      ⟨.nat declaredPolynomialWithPump.eval,
        .polynomialWithPump declaredPolynomialWithPump⟩
  | .maxWithPump =>
      ⟨.nat declaredMaxWithPump.eval,
        .maxWithPump declaredMaxWithPump⟩
  | .matrix2ComponentwiseWithPrimaryPump =>
      ⟨.pairComponentwise declaredMatrixMeasure2WithPrimaryPump.eval,
        .matrix2ComponentwiseWithPrimaryPump
          declaredMatrixMeasure2WithPrimaryPump⟩
  | .matrix2LexWithPrimaryPump =>
      ⟨.pairLex declaredMatrixMeasure2WithPrimaryPump.eval,
        .matrix2LexWithPrimaryPump declaredMatrixMeasure2WithPrimaryPump⟩
  | .matrixMix2WithSumPump =>
      ⟨.pairComponentwise declaredMatrixMix2WithSumPump.eval,
        .matrixMix2WithSumPump declaredMatrixMix2WithSumPump⟩
  | .matrixFunctionalWithProjectedAffinePump =>
      ⟨.vecComponentwise 1
          declaredMatrixFunctionalMeasure1WithProjectedAffinePump.eval,
        .matrixFunctionalWithProjectedAffinePump
          declaredMatrixFunctionalMeasure1WithProjectedAffinePump⟩
  | .matrixLexDWithPrimaryPump =>
      ⟨.vecLex 1 declaredMatrixLexMeasure1WithPrimaryPump.eval,
        .matrixLexDWithPrimaryPump declaredMatrixLexMeasure1WithPrimaryPump⟩
  | .matrixLexPermWithPrimaryPump =>
      ⟨.vecPermLex 1 declaredMatrixLexPermMeasure1WithPrimaryPump.priority
          declaredMatrixLexPermMeasure1WithPrimaryPump.eval,
        .matrixLexPermWithPrimaryPump
          declaredMatrixLexPermMeasure1WithPrimaryPump⟩

/-- Exact twelve-row foundational ledger in manuscript order. -/
def declaredBaseFamilyLedger : List DeclaredFamilyTag :=
  [.additive,
    .compositionalTransparent,
    .affineWithPump,
    .quadraticWithPump,
    .crossQuadraticWithPump,
    .multilinearWithPump,
    .polynomialWithPump,
    .maxWithPump,
    .matrix2ComponentwiseWithPrimaryPump,
    .matrix2LexWithPrimaryPump,
    .matrixMix2WithSumPump,
    .matrixFunctionalWithProjectedAffinePump]

/-- The two tracked-lex continuations, kept outside the foundational twelve. -/
def declaredContinuationFamilyLedger : List DeclaredFamilyTag :=
  [.matrixLexDWithPrimaryPump, .matrixLexPermWithPrimaryPump]

/-- Complete enumerated ledger: twelve base rows followed by two
continuations. -/
def declaredFamilyLedger : List DeclaredFamilyTag :=
  declaredBaseFamilyLedger ++ declaredContinuationFamilyLedger

theorem declaredBaseFamilyLedger_length :
    declaredBaseFamilyLedger.length = 12 := by
  decide

theorem declaredContinuationFamilyLedger_length :
    declaredContinuationFamilyLedger.length = 2 := by
  decide

theorem declaredBaseFamilyLedger_nodup :
    declaredBaseFamilyLedger.Nodup := by
  decide

theorem declaredContinuationFamilyLedger_nodup :
    declaredContinuationFamilyLedger.Nodup := by
  decide

/-- No continuation tag is miscounted as one of the foundational twelve. -/
theorem declaredBaseContinuationFamilyLedgers_disjoint :
    ∀ tag : DeclaredFamilyTag,
      tag ∈ declaredBaseFamilyLedger →
      tag ∈ declaredContinuationFamilyLedger → False := by
  intro tag hbase hcontinuation
  cases tag <;> simp [declaredBaseFamilyLedger,
    declaredContinuationFamilyLedger] at hbase hcontinuation

theorem declaredFamilyLedger_length : declaredFamilyLedger.length = 14 := by
  decide

theorem declaredFamilyLedger_nonempty : declaredFamilyLedger ≠ [] := by
  decide

theorem declaredFamilyLedger_nodup : declaredFamilyLedger.Nodup := by
  decide

theorem declaredFamilyLedger_complete (tag : DeclaredFamilyTag) :
    tag ∈ declaredFamilyLedger := by
  cases tag <;> decide

/-- The concrete ledger candidate really is carried by the constructor named
by its tag. -/
theorem declaredFamilyCandidate_matches_tag (tag : DeclaredFamilyTag) :
    DeclaredFamilyMatches tag (declaredFamilyCandidate tag) := by
  cases tag with
  | additive =>
      exact DeclaredFamilyMatches.additive
        OperatorKO7.CompositionalImpossibility.simpleSize_ACM
  | compositionalTransparent =>
      exact DeclaredFamilyMatches.compositionalTransparent
        declaredTransparentCompositionalMeasure
        declaredTransparentCompositionalMeasure_transparent
  | affineWithPump =>
      exact DeclaredFamilyMatches.affineWithPump declaredAffineWithPump
  | quadraticWithPump =>
      exact DeclaredFamilyMatches.quadraticWithPump declaredQuadraticWithPump
  | crossQuadraticWithPump =>
      exact DeclaredFamilyMatches.crossQuadraticWithPump
        declaredCrossQuadraticWithPump
  | multilinearWithPump =>
      exact DeclaredFamilyMatches.multilinearWithPump declaredMultilinearWithPump
  | polynomialWithPump =>
      exact DeclaredFamilyMatches.polynomialWithPump declaredPolynomialWithPump
  | maxWithPump =>
      exact DeclaredFamilyMatches.maxWithPump declaredMaxWithPump
  | matrix2ComponentwiseWithPrimaryPump =>
      exact DeclaredFamilyMatches.matrix2ComponentwiseWithPrimaryPump
        declaredMatrixMeasure2WithPrimaryPump
  | matrix2LexWithPrimaryPump =>
      exact DeclaredFamilyMatches.matrix2LexWithPrimaryPump
        declaredMatrixMeasure2WithPrimaryPump
  | matrixMix2WithSumPump =>
      exact DeclaredFamilyMatches.matrixMix2WithSumPump
        declaredMatrixMix2WithSumPump
  | matrixFunctionalWithProjectedAffinePump =>
      exact DeclaredFamilyMatches.matrixFunctionalWithProjectedAffinePump
        declaredMatrixFunctionalMeasure1WithProjectedAffinePump
  | matrixLexDWithPrimaryPump =>
      exact DeclaredFamilyMatches.matrixLexDWithPrimaryPump
        declaredMatrixLexMeasure1WithPrimaryPump
  | matrixLexPermWithPrimaryPump =>
      exact DeclaredFamilyMatches.matrixLexPermWithPrimaryPump
        declaredMatrixLexPermMeasure1WithPrimaryPump

/-- Every tag has an explicit proof-bearing candidate witness. -/
theorem declaredFamilyCandidate_witness (tag : DeclaredFamilyTag) :
    ∃ entry : DeclaredDirectUniverse, DeclaredFamilyMatches tag entry :=
  ⟨declaredFamilyCandidate tag, declaredFamilyCandidate_matches_tag tag⟩

/-- The proof-bearing declared universe is nonempty. -/
theorem declaredDirectUniverse_nonempty : Nonempty DeclaredDirectUniverse :=
  ⟨simpleSizeDeclaredDirectUniverse⟩

/-- A candidate orients a supplied relation when its own codomain order
strictly decreases on every edge of that relation. -/
def Orients (candidate : Candidate) (R : Trace -> Trace -> Prop) : Prop :=
  match candidate.orienter with
  | .nat measure =>
      forall {a b : Trace}, R a b -> measure b < measure a
  | .pairComponentwise measure =>
      forall {a b : Trace}, R a b -> PairLt (measure b) (measure a)
  | .pairLex measure =>
      forall {a b : Trace}, R a b -> PairLexLt (measure b) (measure a)
  | .vecComponentwise _ measure =>
      forall {a b : Trace}, R a b -> VecLt (measure b) (measure a)
  | .vecLex _ measure =>
      forall {a b : Trace}, R a b -> VecLexLt (measure b) (measure a)
  | .vecPermLex _ priority measure =>
      forall {a b : Trace}, R a b ->
        VecPermLexLt priority (measure b) (measure a)

/-- Root-step orientation predicate attached directly to the local enumerated
orienter syntax. -/
def DeclaredDirectOrienter.Orients : DeclaredDirectOrienter → Prop
  | .nat measure =>
      ∀ {a b : Trace}, Step a b → measure b < measure a
  | .pairComponentwise measure =>
      ∀ {a b : Trace}, Step a b → PairLt (measure b) (measure a)
  | .pairLex measure =>
      ∀ {a b : Trace}, Step a b → PairLexLt (measure b) (measure a)
  | .vecComponentwise _ measure =>
      ∀ {a b : Trace}, Step a b → VecLt (measure b) (measure a)
  | .vecLex _ measure =>
      ∀ {a b : Trace}, Step a b → VecLexLt (measure b) (measure a)
  | .vecPermLex _ priority measure =>
      ∀ {a b : Trace}, Step a b →
        VecPermLexLt priority (measure b) (measure a)

/-- On the actual KO7 root relation, the relation-relative definition is
definitionally the existing candidate orientation predicate. -/
theorem orients_ko7_iff (candidate : Candidate) :
    Orients candidate Step <-> candidate.orienter.Orients := by
  rcases candidate with ⟨orienter, declared⟩
  cases orienter <;> rfl

/-- Every candidate in the declared profile is blocked on the actual KO7
relation by its existing family-specific barrier theorem. -/
theorem declaredCandidate_not_orients_ko7 (candidate : Candidate) :
    Not (Orients candidate Step) := by
  intro horients
  rcases candidate with ⟨orienter, declared⟩
  cases declared with
  | additive M =>
      exact (no_global_step_orientation_additive_compositional M) horients
  | compositionalTransparent CM htransparent =>
      exact
        (no_global_step_orientation_compositional_transparent_delta
          CM htransparent) horients
  | affineWithPump M =>
      exact (no_global_step_orientation_affine_with_pump M) horients
  | quadraticWithPump M =>
      exact (no_global_step_orientation_quadratic_with_pump M) horients
  | crossQuadraticWithPump M =>
      exact (no_global_step_orientation_cross_quadratic_with_pump M) horients
  | multilinearWithPump M =>
      exact (no_global_step_orientation_multilinear_with_pump M) horients
  | polynomialWithPump M =>
      exact (no_global_step_orientation_polynomial_with_pump M) horients
  | maxWithPump M =>
      exact (no_global_step_orientation_max_with_pump M) horients
  | matrix2ComponentwiseWithPrimaryPump M =>
      exact (no_global_step_orientation_matrix2_with_primary_pump M) horients
  | matrix2LexWithPrimaryPump M =>
      exact (no_global_step_orientation_matrix2_lex_with_primary_pump M) horients
  | matrixMix2WithSumPump M =>
      exact (no_global_step_orientation_matrixMix2_with_sum_pump M) horients
  | matrixFunctionalWithProjectedAffinePump M =>
      exact
        (no_global_step_orientation_matrixFunctional_with_projected_affine_pump M)
          horients
  | matrixLexDWithPrimaryPump M =>
      exact (no_global_step_orientation_matrixLexD_with_primary_pump M) horients
  | matrixLexPermWithPrimaryPump M =>
      exact (no_global_step_orientation_matrixLexPermD_with_primary_pump M) horients

/-! ## The self-embedding relation has no well-founded orientation -/

/-- Strong normalization for a forward relation is well-foundedness of its
reverse relation. -/
def StronglyNormalizing (R : Trace -> Trace -> Prop) : Prop :=
  WellFounded (fun a b => R b a)

/-- The explicit self-embedding chain prevents accessibility at every term. -/
theorem selfEmbeddingStep_not_stronglyNormalizing :
    Not (StronglyNormalizing SelfEmbeddingStep) := by
  intro hwf
  have noAcc : forall t : Trace,
      Not (Acc (fun a b : Trace => SelfEmbeddingStep b a) t) := by
    intro t hacc
    induction hacc with
    | intro t predecessors ih =>
        exact ih (delta t) (SelfEmbeddingStep.fire t)
  exact noAcc void (hwf.apply void)

/-- A well-founded codomain order cannot orient the self-embedding relation. -/
theorem selfEmbeddingStep_not_orients_of_wellFounded
    {Codomain : Type} (measure : Trace -> Codomain)
    (order : Codomain -> Codomain -> Prop) (horder : WellFounded order) :
    Not (forall {a b : Trace}, SelfEmbeddingStep a b ->
      order (measure b) (measure a)) := by
  intro horients
  apply selfEmbeddingStep_not_stronglyNormalizing
  refine Subrelation.wf ?_ (InvImage.wf (f := measure) horder)
  intro a b hab
  exact horients hab

/-- Strict componentwise order on pairs is well-founded because every edge
strictly decreases the first coordinate. -/
theorem pairLt_wellFounded : WellFounded PairLt := by
  refine Subrelation.wf ?_
    (InvImage.wf (f := fun p : Nat × Nat => p.1) Nat.lt_wfRel.wf)
  intro a b hab
  exact hab.1

/-- The declared pair lexicographic order is the standard well-founded product
lexicographic order on naturals. -/
theorem pairLexLt_wellFounded : WellFounded PairLexLt := by
  have hnat : WellFounded (fun a b : Nat => a < b) := Nat.lt_wfRel.wf
  refine Subrelation.wf ?_ (WellFounded.prod_lex hnat hnat)
  rintro ⟨a₁, a₂⟩ ⟨b₁, b₂⟩ h
  rcases h with hleft | ⟨heq, hright⟩
  · exact Prod.Lex.left a₂ b₂ hleft
  · change a₁ = b₁ at heq
    change a₂ < b₂ at hright
    subst b₁
    exact Prod.Lex.right a₁ hright

/-- A strict componentwise vector order is well-founded whenever a concrete
coordinate is available. -/
theorem vecLt_wellFounded_at {d : Nat} (tracked : Fin d) :
    WellFounded (@VecLt d) := by
  refine Subrelation.wf ?_
    (InvImage.wf (f := fun v : Fin d → Nat => v tracked) Nat.lt_wfRel.wf)
  intro a b hab
  exact hab tracked

/-- Permuted vector lexicographic order is the inverse image of the genuine
finite lexicographic order under coordinate permutation. -/
theorem vecPermLexLt_wellFounded (d : Nat)
    (priority : Equiv.Perm (Fin (d + 1))) :
    WellFounded (VecPermLexLt priority) := by
  have hwf := InvImage.wf
    (f := fun u : Fin (d + 1) -> Nat => fun i => u (priority i))
    (vecLexLt_wellFounded d)
  simpa [VecPermLexLt, VecLexLt, InvImage] using hwf

/-- Every declared candidate is also blocked on the self-embedding relation,
now by the independent infinite-chain/well-founded-order argument. -/
theorem declaredCandidate_not_orients_selfEmbedding
    (candidate : Candidate) :
    Not (Orients candidate SelfEmbeddingStep) := by
  rcases candidate with ⟨orienter, declared⟩
  cases declared with
  | additive M =>
      exact selfEmbeddingStep_not_orients_of_wellFounded
        M.eval (fun x y : Nat => x < y) Nat.lt_wfRel.wf
  | compositionalTransparent CM _ =>
      exact selfEmbeddingStep_not_orients_of_wellFounded
        CM.eval (fun x y : Nat => x < y) Nat.lt_wfRel.wf
  | affineWithPump M =>
      exact selfEmbeddingStep_not_orients_of_wellFounded
        M.eval (fun x y : Nat => x < y) Nat.lt_wfRel.wf
  | quadraticWithPump M =>
      exact selfEmbeddingStep_not_orients_of_wellFounded
        M.eval (fun x y : Nat => x < y) Nat.lt_wfRel.wf
  | crossQuadraticWithPump M =>
      exact selfEmbeddingStep_not_orients_of_wellFounded
        M.eval (fun x y : Nat => x < y) Nat.lt_wfRel.wf
  | multilinearWithPump M =>
      exact selfEmbeddingStep_not_orients_of_wellFounded
        M.eval (fun x y : Nat => x < y) Nat.lt_wfRel.wf
  | polynomialWithPump M =>
      exact selfEmbeddingStep_not_orients_of_wellFounded
        M.eval (fun x y : Nat => x < y) Nat.lt_wfRel.wf
  | maxWithPump M =>
      exact selfEmbeddingStep_not_orients_of_wellFounded
        M.eval (fun x y : Nat => x < y) Nat.lt_wfRel.wf
  | matrix2ComponentwiseWithPrimaryPump M =>
      exact selfEmbeddingStep_not_orients_of_wellFounded
        M.eval PairLt pairLt_wellFounded
  | matrix2LexWithPrimaryPump M =>
      exact selfEmbeddingStep_not_orients_of_wellFounded
        M.eval PairLexLt pairLexLt_wellFounded
  | matrixMix2WithSumPump M =>
      exact selfEmbeddingStep_not_orients_of_wellFounded
        M.eval PairLt pairLt_wellFounded
  | matrixFunctionalWithProjectedAffinePump M =>
      rcases M.h_weight_support with ⟨tracked, _⟩
      exact selfEmbeddingStep_not_orients_of_wellFounded
        M.eval VecLt (vecLt_wellFounded_at tracked)
  | matrixLexDWithPrimaryPump M =>
      exact selfEmbeddingStep_not_orients_of_wellFounded
        M.eval VecLexLt (vecLexLt_wellFounded _)
  | matrixLexPermWithPrimaryPump M =>
      exact selfEmbeddingStep_not_orients_of_wellFounded
        M.eval (VecPermLexLt M.priority)
          (vecPermLexLt_wellFounded _ M.priority)

/-! ## Full profile collision and independent verdict split -/

/-- The complete two-system carrier used by downstream finite adapters. -/
inductive RelationSystem
  | recursor
  | selfEmbedding
  deriving DecidableEq, Fintype, Repr

/-- Actual relation carried by each system. -/
def RelationSystem.relation : RelationSystem -> Trace -> Trace -> Prop
  | .recursor => Step
  | .selfEmbedding => SelfEmbeddingStep

/-- The full candidate-by-candidate orientability profile. -/
def directProfile (system : RelationSystem) : Candidate -> Prop :=
  fun candidate => Orients candidate system.relation

/-- The candidate profile covers Paper A's exact proof-bearing declared
direct universe. Every declared entry maps to a candidate with the same
orienter, and the profile records non-orientation on both actual relations.

Relation: KO7 root `Step` and `SelfEmbeddingStep`, separately.
Property: relation-relative non-orientation for every member of the declared
universe.
Does not prove: coverage outside `DeclaredDirectBarrierRepresentable`.
-/
theorem candidateProfile_covers_declared_direct_universe
    (entry : DeclaredDirectUniverse) :
    (candidateOfDeclaredDirectUniverse entry).orienter = entry.1 ∧
      ¬ directProfile .recursor
        (candidateOfDeclaredDirectUniverse entry) ∧
      ¬ directProfile .selfEmbedding
        (candidateOfDeclaredDirectUniverse entry) := by
  constructor
  · rfl
  constructor
  · exact declaredCandidate_not_orients_ko7 _
  · exact declaredCandidate_not_orients_selfEmbedding _

/-- Every one of the fourteen exact family tags is realized by a candidate
that is blocked on both actual relations by the existing profile theorem. -/
theorem declaredFamilyCandidate_profile_coverage (tag : DeclaredFamilyTag) :
    DeclaredFamilyMatches tag (declaredFamilyCandidate tag) ∧
      ¬ directProfile .recursor
        (candidateOfDeclaredDirectUniverse (declaredFamilyCandidate tag)) ∧
      ¬ directProfile .selfEmbedding
        (candidateOfDeclaredDirectUniverse (declaredFamilyCandidate tag)) := by
  exact ⟨declaredFamilyCandidate_matches_tag tag,
    (candidateProfile_covers_declared_direct_universe
      (declaredFamilyCandidate tag)).2⟩

/-- Ledger-level closure: every listed row carries its exact family witness
and both relation-specific nonorientation facts. -/
theorem declaredFamilyLedger_profile_coverage :
    ∀ tag ∈ declaredFamilyLedger,
      DeclaredFamilyMatches tag (declaredFamilyCandidate tag) ∧
        ¬ directProfile .recursor
          (candidateOfDeclaredDirectUniverse (declaredFamilyCandidate tag)) ∧
        ¬ directProfile .selfEmbedding
          (candidateOfDeclaredDirectUniverse (declaredFamilyCandidate tag)) := by
  intro tag _
  exact declaredFamilyCandidate_profile_coverage tag

/-- The coverage theorem has a concrete simple-size instance on both actual
relations, so its universal statement is not vacuous. -/
theorem simpleSize_candidateProfile_blocked_on_both_relations :
    ¬ directProfile .recursor
        (candidateOfDeclaredDirectUniverse simpleSizeDeclaredDirectUniverse) ∧
      ¬ directProfile .selfEmbedding
        (candidateOfDeclaredDirectUniverse simpleSizeDeclaredDirectUniverse) :=
  ⟨(candidateProfile_covers_declared_direct_universe
      simpleSizeDeclaredDirectUniverse).2.1,
    (candidateProfile_covers_declared_direct_universe
      simpleSizeDeclaredDirectUniverse).2.2⟩

/-- Compatibility name emphasizing that the profile is the meta observer. -/
abbrev metaObserve := directProfile

/-- The relation-level mathematical verdict, distinct from both the
fixed-input execution surface and its finite encoding below. -/
def StrongNormalizationVerdict (system : RelationSystem) : Prop :=
  StronglyNormalizing system.relation

/-- The entire declared candidate profile agrees on the two systems.  This is
strictly stronger than equality of a single existential Boolean. -/
theorem directProfile_recursor_eq_selfEmbedding :
    directProfile .recursor = directProfile .selfEmbedding := by
  funext candidate
  apply propext
  constructor
  · intro h
    exact (declaredCandidate_not_orients_ko7 candidate h).elim
  · intro h
    exact (declaredCandidate_not_orients_selfEmbedding candidate h).elim

/-- KO7 has the positive relation-level verdict by the existing full-root
well-foundedness theorem. -/
theorem recursor_strongNormalizationVerdict :
    StrongNormalizationVerdict .recursor := by
  exact OperatorKO7.PolyInterpretation.wf_StepRev_poly

/-- The self-embedding system has the negative relation-level verdict. -/
theorem selfEmbedding_not_strongNormalizationVerdict :
    Not (StrongNormalizationVerdict .selfEmbedding) :=
  selfEmbeddingStep_not_stronglyNormalizing

/-- Finite encoding of the relation-level verdict on the complete two-system
carrier.  Correctness is proved below from the actual relation facts. -/
def terminationVerdict : RelationSystem -> Bool
  | .recursor => true
  | .selfEmbedding => false

/-- The finite verdict is correct on both systems with respect to actual
strong normalization. -/
theorem terminationVerdict_eq_true_iff (system : RelationSystem) :
    terminationVerdict system = true <-> StrongNormalizationVerdict system := by
  cases system with
  | recursor =>
      constructor
      · intro _
        exact recursor_strongNormalizationVerdict
      · intro _
        rfl
  | selfEmbedding =>
      constructor
      · intro h
        cases h
      · intro h
        exact (selfEmbedding_not_strongNormalizationVerdict h).elim

/-- The finite verdicts differ, derived through their independently proved
relation-level meanings. -/
theorem terminationVerdict_recursor_ne_selfEmbedding :
    terminationVerdict .recursor ≠ terminationVerdict .selfEmbedding := by
  intro heq
  have hrecursor : terminationVerdict .recursor = true :=
    (terminationVerdict_eq_true_iff .recursor).2
      recursor_strongNormalizationVerdict
  have hself : terminationVerdict .selfEmbedding ≠ true := by
    intro htrue
    exact selfEmbedding_not_strongNormalizationVerdict
      ((terminationVerdict_eq_true_iff .selfEmbedding).1 htrue)
  apply hself
  exact heq.symm.trans hrecursor

/-- Concrete observer collision on actual relations and the full declared
candidate profile. -/
theorem ko7_profile_operationallyInexpressible :
    OperationallyInexpressibleAt directProfile terminationVerdict
      .recursor .selfEmbedding :=
  ⟨directProfile_recursor_eq_selfEmbedding,
    terminationVerdict_recursor_ne_selfEmbedding⟩

/-- The concrete non-synthetic `TypedBoundary` instance. -/
def ko7ProfileTypedBoundary : TypedBoundary where
  State := RelationSystem
  Obs := Candidate -> Prop
  Verdict := Bool
  observe := directProfile
  verdict := terminationVerdict
  s₁ := .recursor
  s₂ := .selfEmbedding
  obs_eq := directProfile_recursor_eq_selfEmbedding
  verdict_ne := terminationVerdict_recursor_ne_selfEmbedding

/-- No decoder from the full declared candidate profile recovers the finite
encoding of the relation-level verdict on both actual systems. -/
theorem ko7_verdict_not_candidateProfile_function :
    Not (exists decide : (Candidate -> Prop) -> Bool,
      forall system : RelationSystem,
        terminationVerdict system = decide (directProfile system)) :=
  TypedBoundary.verdict_not_observation_function ko7ProfileTypedBoundary

/-- Quotient-form no-decoder statement for the same concrete collision. -/
theorem ko7_profile_not_quotientFactorization :
    Not (QuotientFactorization directProfile terminationVerdict) := by
  exact (quotient_factorization_failure_iff_collision
    directProfile terminationVerdict).2
      ⟨RelationSystem.recursor, RelationSystem.selfEmbedding,
        ko7_profile_operationallyInexpressible⟩

end OperatorKO7.Meta.OperationalInexpressibility.KO7ObservationVerdict
