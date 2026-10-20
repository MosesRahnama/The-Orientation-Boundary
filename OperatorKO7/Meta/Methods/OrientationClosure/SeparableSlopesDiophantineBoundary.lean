/-
The exact signed-bivariate content of the unresolved successor-orientation branch.

Relation: root successor orientation for the constructor-local polynomial interpretation.
Property: an executable embedding whose residual inequality is exactly signed-bivariate
positivity over Nat x Nat.
-/
import OperatorKO7.Meta.Methods.OrientationClosure.SeparableSlopes

set_option autoImplicit false

namespace OperatorKO7.Methods.OrientationClosure.SeparableSlopesDiophantineBoundary

open PolynomialOrientationDecision
open SeparableSlopes

/-- A natural-coefficient monomial in the base and payload variables. -/
structure BiMono where
  coeff : Nat
  bDeg : Nat
  sDeg : Nat
  deriving DecidableEq, Repr

/-- Evaluation of a finite natural-coefficient bivariate polynomial. -/
def biEvalNat : List BiMono → Nat → Nat → Nat
  | [], _, _ => 0
  | m :: P, b, s => m.coeff * b ^ m.bDeg * s ^ m.sDeg + biEvalNat P b s

/-- A signed bivariate polynomial represented as a difference of natural polynomials. -/
structure SignedBiPoly where
  pos : List BiMono
  neg : List BiMono
  deriving DecidableEq, Repr

/-- Integer evaluation of a signed bivariate polynomial. -/
def SignedBiPoly.eval (P : SignedBiPoly) (b s : Nat) : Int :=
  (biEvalNat P.pos b s : Int) - (biEvalNat P.neg b s : Int)

/-- Product of two natural bivariate monomials. -/
def biMulMono (m n : BiMono) : BiMono :=
  { coeff := m.coeff * n.coeff
    bDeg := m.bDeg + n.bDeg
    sDeg := m.sDeg + n.sDeg }

/-- Distributive product of two finite natural bivariate polynomials. -/
def biMul : List BiMono → List BiMono → List BiMono
  | [], _ => []
  | p :: P, Q => Q.map (biMulMono p) ++ biMul P Q

/-- Multiplication of every coefficient by a natural scalar. -/
def biScale (k : Nat) : List BiMono → List BiMono
  | [] => []
  | m :: P => { m with coeff := k * m.coeff } :: biScale k P

/-- The signed polynomial square, expanded into positive and negative lists. -/
def SignedBiPoly.square (P : SignedBiPoly) : SignedBiPoly :=
  { pos := biMul P.pos P.pos ++ biMul P.neg P.neg
    neg := biScale 2 (biMul P.pos P.neg) }

theorem biEvalNat_append (P Q : List BiMono) (b s : Nat) :
    biEvalNat (P ++ Q) b s = biEvalNat P b s + biEvalNat Q b s := by
  induction P with
  | nil => simp [biEvalNat]
  | cons m P ih => simp [biEvalNat, ih, Nat.add_assoc]

theorem biEvalNat_biScale (k : Nat) (P : List BiMono) (b s : Nat) :
    biEvalNat (biScale k P) b s = k * biEvalNat P b s := by
  induction P with
  | nil => simp [biScale, biEvalNat]
  | cons m P ih =>
      simp [biScale, biEvalNat, ih]
      ring

theorem biEvalNat_map_biMulMono (m : BiMono) (P : List BiMono) (b s : Nat) :
    biEvalNat (P.map (biMulMono m)) b s =
      (m.coeff * b ^ m.bDeg * s ^ m.sDeg) * biEvalNat P b s := by
  induction P with
  | nil => simp [biEvalNat]
  | cons n P ih =>
      simp [biEvalNat, biMulMono, ih, pow_add]
      ring

theorem biEvalNat_biMul (P Q : List BiMono) (b s : Nat) :
    biEvalNat (biMul P Q) b s = biEvalNat P b s * biEvalNat Q b s := by
  induction P with
  | nil => simp [biMul, biEvalNat]
  | cons m P ih =>
      simp [biMul, biEvalNat_append, biEvalNat_map_biMulMono, biEvalNat, ih]
      ring

theorem SignedBiPoly.eval_square (P : SignedBiPoly) (b s : Nat) :
    P.square.eval b s = P.eval b s * P.eval b s := by
  simp [SignedBiPoly.square, SignedBiPoly.eval, biEvalNat_append,
    biEvalNat_biMul, biEvalNat_biScale]
  ring

/-- A monomial whose coefficient may be any integer. -/
structure IntBiMono where
  coeff : Int
  bDeg : Nat
  sDeg : Nat
  deriving DecidableEq, Repr

/-- Evaluation of a finite integer-coefficient bivariate polynomial. -/
def intBiEval : List IntBiMono → Nat → Nat → Int
  | [], _, _ => 0
  | m :: P, b, s => m.coeff * (b ^ m.bDeg : Nat) * (s ^ m.sDeg : Nat) + intBiEval P b s

/-- The nonnegative part of an integer coefficient. -/
def intPositivePart : Int → Nat
  | .ofNat n => n
  | .negSucc _ => 0

/-- The magnitude of the negative part of an integer coefficient. -/
def intNegativePart : Int → Nat
  | .ofNat _ => 0
  | .negSucc n => n + 1

theorem int_parts_sub (z : Int) :
    (intPositivePart z : Int) - (intNegativePart z : Int) = z := by
  cases z with
  | ofNat n => simp [intPositivePart, intNegativePart]
  | negSucc n =>
      simp [intPositivePart, intNegativePart]
      omega

/-- Positive monomial list obtained by splitting every integer coefficient. -/
def positivePart : List IntBiMono → List BiMono
  | [] => []
  | m :: P => ⟨intPositivePart m.coeff, m.bDeg, m.sDeg⟩ :: positivePart P

/-- Negative monomial list obtained by splitting every integer coefficient. -/
def negativePart : List IntBiMono → List BiMono
  | [] => []
  | m :: P => ⟨intNegativePart m.coeff, m.bDeg, m.sDeg⟩ :: negativePart P

/-- Executable positive-minus-negative representation of any integer polynomial syntax. -/
def signedOfIntPoly (P : List IntBiMono) : SignedBiPoly :=
  ⟨positivePart P, negativePart P⟩

theorem positive_negative_eval_sub (P : List IntBiMono) (b s : Nat) :
    (biEvalNat (positivePart P) b s : Int) -
        (biEvalNat (negativePart P) b s : Int) = intBiEval P b s := by
  induction P with
  | nil => simp [positivePart, negativePart, biEvalNat, intBiEval]
  | cons m P ih =>
      simp only [positivePart, negativePart, biEvalNat, intBiEval]
      calc
        (intPositivePart m.coeff * b ^ m.bDeg * s ^ m.sDeg : Nat) +
              biEvalNat (positivePart P) b s -
            ((intNegativePart m.coeff * b ^ m.bDeg * s ^ m.sDeg : Nat) +
              biEvalNat (negativePart P) b s) =
            ((intPositivePart m.coeff : Int) - intNegativePart m.coeff) *
                (b ^ m.bDeg : Nat) * (s ^ m.sDeg : Nat) +
              ((biEvalNat (positivePart P) b s : Int) -
                biEvalNat (negativePart P) b s) := by
                  push_cast
                  ring
        _ = m.coeff * (b ^ m.bDeg : Nat) * (s ^ m.sDeg : Nat) + intBiEval P b s := by
              rw [int_parts_sub, ih]

theorem signedOfIntPoly_eval (P : List IntBiMono) (b s : Nat) :
    (signedOfIntPoly P).eval b s = intBiEval P b s := by
  exact positive_negative_eval_sub P b s

/-! ## Exact residual embedding -/

/-- The wrapper `2*y` used by the exact residual embedding. -/
def residualWrapper : List WMono := [⟨2, 0, 1⟩]

/-- Positive coefficients receive counter degree one and contribute with sign `+1`. -/
def liftPositive (m : BiMono) : RMono := ⟨m.coeff, m.bDeg, m.sDeg, 1⟩

/-- Negative coefficients receive counter degree zero and contribute with sign `-1`. -/
def liftNegative (m : BiMono) : RMono := ⟨m.coeff, m.bDeg, m.sDeg, 0⟩

/-- Degree-one half of the cancelling sentinel pair. -/
def residualSentinelHigh : RMono := ⟨1, 0, 0, 1⟩

/-- Degree-zero half of the cancelling sentinel pair. -/
def residualSentinelLow : RMono := ⟨1, 0, 0, 0⟩

/-- Embedding of a signed bivariate polynomial into a recursor interpretation. -/
def encodeResidual (P : SignedBiPoly) : List RMono :=
  residualSentinelHigh :: residualSentinelLow ::
    (P.pos.map liftPositive ++ P.neg.map liftNegative)

theorem monomialCounterPoly_two_one_two_zero (n : Nat) :
    monomialCounterPoly 2 1 2 0 n = -1 := by
  simp [monomialCounterPoly]

theorem monomialCounterPoly_two_one_two_one (n : Nat) :
    monomialCounterPoly 2 1 2 1 n = 1 := by
  simp [monomialCounterPoly]

theorem residualWrapper_wLin : wLin residualWrapper 0 = 2 := by
  decide

theorem residualWrapper_no_ySquare : ¬ HasYSquare residualWrapper := by
  decide

theorem residualWrapper_no_yPayload : ¬ HasYPayload residualWrapper := by
  decide

theorem rEval_append (R S : List RMono) (b s n : Nat) :
    rEval (R ++ S) b s n = rEval R b s n + rEval S b s n := by
  induction R with
  | nil => simp [rEval]
  | cons m R ih => simp [rEval, ih, Nat.add_assoc]

theorem rEval_map_liftPositive (P : List BiMono) (b s n : Nat) :
    rEval (P.map liftPositive) b s n = biEvalNat P b s * n := by
  induction P with
  | nil => simp [rEval, biEvalNat]
  | cons m P ih =>
      simp [rEval, biEvalNat, liftPositive, ih]
      ring

theorem rEval_map_liftNegative (P : List BiMono) (b s n : Nat) :
    rEval (P.map liftNegative) b s n = biEvalNat P b s := by
  induction P with
  | nil => simp [rEval, biEvalNat]
  | cons m P ih =>
      simp [rEval, biEvalNat, liftNegative, ih]

theorem rEval_encodeResidual (P : SignedBiPoly) (b s n : Nat) :
    rEval (encodeResidual P) b s n =
      n + 1 + biEvalNat P.pos b s * n + biEvalNat P.neg b s := by
  simp [encodeResidual, residualSentinelHigh, residualSentinelLow, rEval,
    rEval_append, rEval_map_liftPositive, rEval_map_liftNegative]
  ring

theorem nDegMax_append (R S : List RMono) :
    nDegMax (R ++ S) = max (nDegMax R) (nDegMax S) := by
  induction R with
  | nil => simp [nDegMax]
  | cons m R ih =>
      simp only [List.cons_append, nDegMax]
      split_ifs <;> simp [ih, max_left_comm, max_comm]

theorem nDegMax_liftPositive_le_one (P : List BiMono) :
    nDegMax (P.map liftPositive) ≤ 1 := by
  induction P with
  | nil => simp [nDegMax]
  | cons m P ih =>
      simp only [List.map_cons, nDegMax, liftPositive]
      split_ifs <;> omega

theorem nDegMax_liftNegative (P : List BiMono) :
    nDegMax (P.map liftNegative) = 0 := by
  induction P with
  | nil => simp [nDegMax]
  | cons m P ih =>
      simp only [List.map_cons, nDegMax, liftNegative]
      split_ifs <;> simp [ih]

theorem encodeResidual_nDegMax (P : SignedBiPoly) : nDegMax (encodeResidual P) = 1 := by
  have h := nDegMax_liftPositive_le_one P.pos
  simp [encodeResidual, nDegMax, residualSentinelHigh, residualSentinelLow,
    nDegMax_append, nDegMax_liftNegative, Nat.max_eq_left h]

theorem encodeResidual_not_allHigh (P : SignedBiPoly) :
    ¬ AllHigh (encodeResidual P) 2 2 := by
  intro h
  have hlow := h residualSentinelLow (by simp [encodeResidual]) (by decide)
  simp [residualSentinelLow] at hlow

/-- The embedded residual is exactly the source signed polynomial at every counter. -/
theorem encodeResidual_sepDiff (P : SignedBiPoly) (b s n : Nat) :
    sepDiff residualWrapper (encodeResidual P) 2 1 b s n = P.eval b s := by
  rw [sepDiff]
  rw [rEval_encodeResidual, rEval_encodeResidual]
  simp only [residualWrapper_wLin]
  simp [residualWrapper, wEval, SignedBiPoly.eval]
  ring

/-- Every encoded instance lies in the branch left open by `decideSuccAff`. -/
theorem encodeResidual_decision_is_open (P : SignedBiPoly) :
    decideSuccAff residualWrapper (encodeResidual P) 2 1 = none := by
  rw [decideSuccAff_eq_none_iff]
  refine ⟨residualWrapper_no_ySquare, residualWrapper_no_yPayload, ?_, ?_,
    encodeResidual_not_allHigh P⟩
  · rw [residualWrapper_wLin]
  · rw [residualWrapper_wLin, encodeResidual_nDegMax]
    norm_num

theorem residualGoal_encode_iff (P : SignedBiPoly) :
    ResidualGoal residualWrapper (encodeResidual P) 2 1 ↔
      ∀ b s, 0 < P.eval b s := by
  unfold ResidualGoal
  simp only [encodeResidual_sepDiff]
  constructor
  · intro h b s
    exact h b s 0
  · intro h b s n
    exact h b s

theorem encoded_orients_iff (P : SignedBiPoly) :
    OrientsSucc residualWrapper (encodeResidual P) 2 1 ↔
      ∀ b s, 0 < P.eval b s := by
  rw [← residualGoal_iff_orientsSucc residualWrapper (encodeResidual P) 2 1
    residualWrapper_no_ySquare residualWrapper_no_yPayload]
  exact residualGoal_encode_iff P

theorem int_square_pos_iff_ne_zero (x : Int) : 0 < x * x ↔ x ≠ 0 := by
  constructor
  · intro h hx
    subst x
    norm_num at h
  · intro hx
    exact mul_self_pos.mpr hx

theorem residualGoal_square_iff_noZero (P : SignedBiPoly) :
    ResidualGoal residualWrapper (encodeResidual P.square) 2 1 ↔
      ∀ b s, P.eval b s ≠ 0 := by
  rw [residualGoal_encode_iff]
  simp only [SignedBiPoly.eval_square, int_square_pos_iff_ne_zero]

theorem residual_open_class_contains_signed_bivariate_positivity :
    ∀ P : SignedBiPoly,
      decideSuccAff residualWrapper (encodeResidual P) 2 1 = none ∧
      (ResidualGoal residualWrapper (encodeResidual P) 2 1 ↔
        ∀ b s, 0 < P.eval b s) := by
  intro P
  exact ⟨encodeResidual_decision_is_open P, residualGoal_encode_iff P⟩

/-! ## Evaluation controls -/

def mixedControl : List IntBiMono :=
  [⟨3, 2, 1⟩, ⟨-5, 1, 0⟩, ⟨7, 0, 0⟩]

theorem signed_empty_control : (signedOfIntPoly []).eval 4 9 = 0 := by decide

theorem signed_positive_constant_control :
    (signedOfIntPoly [⟨5, 0, 0⟩]).eval 7 11 = 5 := by decide

theorem signed_negative_constant_control :
    (signedOfIntPoly [⟨-5, 0, 0⟩]).eval 7 11 = -5 := by decide

theorem signed_cancellation_control :
    SignedBiPoly.eval ⟨[⟨4, 2, 3⟩], [⟨4, 2, 3⟩]⟩ 5 6 = 0 := by decide

theorem mixedControl_eval : intBiEval mixedControl 2 3 = 33 := by decide

theorem mixedControl_signed_eval : (signedOfIntPoly mixedControl).eval 2 3 = 33 := by decide

theorem square_control_zero :
    (signedOfIntPoly [⟨-1, 0, 0⟩, ⟨1, 1, 0⟩]).square.eval 1 8 = 0 := by decide

theorem square_control_nonzero :
    (signedOfIntPoly [⟨-1, 0, 0⟩, ⟨1, 1, 0⟩]).square.eval 3 8 = 4 := by decide

def positiveControl : SignedBiPoly := ⟨[⟨1, 0, 0⟩], []⟩

def zeroControl : SignedBiPoly :=
  signedOfIntPoly [⟨-1, 0, 0⟩, ⟨1, 1, 0⟩]

theorem positiveControl_orients :
    OrientsSucc residualWrapper (encodeResidual positiveControl) 2 1 := by
  rw [encoded_orients_iff]
  intro b s
  norm_num [positiveControl, SignedBiPoly.eval, biEvalNat]

theorem zeroControl_fails_at_one (n : Nat) :
    sepDiff residualWrapper (encodeResidual zeroControl) 2 1 1 0 n = 0 := by
  rw [encodeResidual_sepDiff]
  decide

theorem zeroControl_is_open :
    decideSuccAff residualWrapper (encodeResidual zeroControl) 2 1 = none :=
  encodeResidual_decision_is_open zeroControl

theorem encodeResidual_counter_independent (P : SignedBiPoly) (b s n m : Nat) :
    sepDiff residualWrapper (encodeResidual P) 2 1 b s n =
      sepDiff residualWrapper (encodeResidual P) 2 1 b s m := by
  rw [encodeResidual_sepDiff, encodeResidual_sepDiff]

end OperatorKO7.Methods.OrientationClosure.SeparableSlopesDiophantineBoundary
