/-
Complete executable positivity decisions for signed bivariate polynomials of degree at most one in
one variable, with extracted failing pairs and the residual adapter.

Relation: root successor orientation for constructor-local polynomial interpretations.
Property: sound and complete Boolean decisions on two strata of the P3.6 open branch.
-/
import OperatorKO7.Meta.Methods.OrientationClosure.SeparableSlopesDecision

set_option autoImplicit false

namespace OperatorKO7.Methods.OrientationClosure.SeparableSlopesAffineStrata

open PolynomialOrientationDecision
open SeparableSlopes
open SeparableSlopesDiophantineBoundary
open SeparableSlopesDecision

/-! ## Slices by base degree -/

/-- The payload polynomial formed by the monomials of base degree `k`. -/
def baseSlice (k : Nat) : List BiMono → List UMono
  | [] => []
  | m :: P => if m.bDeg = k then ⟨m.coeff, m.sDeg⟩ :: baseSlice k P else baseSlice k P

theorem uEval_unit_cons (Q : List UMono) (s : Nat) :
    uEval (⟨1, 0⟩ :: Q) s = 1 + uEval Q s := by
  simp [uEval]

/-- A monomial list of base degree at most one evaluates as constant slice plus base times slope. -/
theorem biEvalNat_eq_baseSlices {P : List BiMono} (h : ∀ m ∈ P, m.bDeg ≤ 1) (b s : Nat) :
    biEvalNat P b s = uEval (baseSlice 0 P) s + b * uEval (baseSlice 1 P) s := by
  induction P with
  | nil => simp [biEvalNat, baseSlice, uEval]
  | cons m P ih =>
      have hm : m.bDeg ≤ 1 := h m (by simp)
      have ht : ∀ q ∈ P, q.bDeg ≤ 1 := fun q hq => h q (by simp [hq])
      have hcases : m.bDeg = 0 ∨ m.bDeg = 1 := by omega
      rcases hcases with h0 | h1
      · have e0 : baseSlice 0 (m :: P) = ⟨m.coeff, m.sDeg⟩ :: baseSlice 0 P := by
          simp [baseSlice, h0]
        have e1 : baseSlice 1 (m :: P) = baseSlice 1 P := by
          simp [baseSlice, h0]
        rw [e0, e1, biEvalNat, ih ht, h0]
        simp only [uEval, pow_zero, mul_one]
        ring
      · have e0 : baseSlice 0 (m :: P) = baseSlice 0 P := by
          simp [baseSlice, h1]
        have e1 : baseSlice 1 (m :: P) = ⟨m.coeff, m.sDeg⟩ :: baseSlice 1 P := by
          simp [baseSlice, h1]
        rw [e0, e1, biEvalNat, ih ht, h1]
        simp only [uEval, pow_one]
        ring

/-! ## The base-affine stratum -/

/-- Executable recognition of signed polynomials of base degree at most one. -/
def baseAffineB (P : SignedBiPoly) : Bool :=
  P.pos.all (fun m => decide (m.bDeg ≤ 1)) && P.neg.all (fun m => decide (m.bDeg ≤ 1))

/-- Propositional meaning of the executable base-affine test. -/
def BaseAffine (P : SignedBiPoly) : Prop := baseAffineB P = true

instance baseAffineDecidable (P : SignedBiPoly) : Decidable (BaseAffine P) := by
  unfold BaseAffine
  infer_instance

theorem baseAffine_pos {P : SignedBiPoly} (h : BaseAffine P) : ∀ m ∈ P.pos, m.bDeg ≤ 1 := by
  intro m hm
  unfold BaseAffine baseAffineB at h
  rw [Bool.and_eq_true] at h
  have hm' := (List.all_eq_true.mp h.1) m hm
  simpa using hm'

theorem baseAffine_neg {P : SignedBiPoly} (h : BaseAffine P) : ∀ m ∈ P.neg, m.bDeg ≤ 1 := by
  intro m hm
  unfold BaseAffine baseAffineB at h
  rw [Bool.and_eq_true] at h
  have hm' := (List.all_eq_true.mp h.2) m hm
  simpa using hm'

/-- On the base-affine stratum the value is the constant slice difference plus the base times the
slope slice difference. -/
theorem baseAffine_eval {P : SignedBiPoly} (h : BaseAffine P) (b s : Nat) :
    P.eval b s =
      ((uEval (baseSlice 0 P.pos) s : Int) - (uEval (baseSlice 0 P.neg) s : Int)) +
        (b : Int) * ((uEval (baseSlice 1 P.pos) s : Int) - (uEval (baseSlice 1 P.neg) s : Int)) := by
  rw [SignedBiPoly.eval, biEvalNat_eq_baseSlices (baseAffine_pos h),
    biEvalNat_eq_baseSlices (baseAffine_neg h)]
  push_cast
  ring

/-- Complete executable positivity decision on the base-affine stratum: the constant slice is
positive and the slope slice is nonnegative at every payload. -/
def decideBaseAffinePositive (P : SignedBiPoly) : Bool :=
  ltAllB (baseSlice 0 P.neg) (baseSlice 0 P.pos) &&
    ltAllB (baseSlice 1 P.neg) (⟨1, 0⟩ :: baseSlice 1 P.pos)

theorem decideBaseAffinePositive_iff (P : SignedBiPoly) (h : BaseAffine P) :
    decideBaseAffinePositive P = true ↔ ∀ b s, 0 < P.eval b s := by
  rw [decideBaseAffinePositive, Bool.and_eq_true, ltAllB_iff, ltAllB_iff]
  constructor
  · rintro ⟨hA, hB⟩ b s
    rw [baseAffine_eval h]
    have ha : (uEval (baseSlice 0 P.neg) s : Int) < (uEval (baseSlice 0 P.pos) s : Int) := by
      exact_mod_cast hA s
    have hb' := hB s
    rw [uEval_unit_cons] at hb'
    have hbn : uEval (baseSlice 1 P.neg) s ≤ uEval (baseSlice 1 P.pos) s := by omega
    have hb : (uEval (baseSlice 1 P.neg) s : Int) ≤ (uEval (baseSlice 1 P.pos) s : Int) := by
      exact_mod_cast hbn
    have hbnn : (0 : Int) ≤ (b : Int) := by positivity
    nlinarith [mul_nonneg hbnn (sub_nonneg.mpr hb)]
  · intro hall
    refine ⟨fun s => ?_, fun s => ?_⟩
    · have h0 := hall 0 s
      rw [baseAffine_eval h] at h0
      simp only [Nat.cast_zero, zero_mul, add_zero] at h0
      have hlt : (uEval (baseSlice 0 P.neg) s : Int) < (uEval (baseSlice 0 P.pos) s : Int) := by
        linarith
      exact_mod_cast hlt
    · rw [uEval_unit_cons]
      by_contra hnot
      have hle : 1 + uEval (baseSlice 1 P.pos) s ≤ uEval (baseSlice 1 P.neg) s := by omega
      have hb := hall (uEval (baseSlice 0 P.pos) s) s
      rw [baseAffine_eval h] at hb
      have hcast : (1 : Int) + (uEval (baseSlice 1 P.pos) s : Int) ≤
          (uEval (baseSlice 1 P.neg) s : Int) := by exact_mod_cast hle
      have hA0 : (0 : Int) ≤ (uEval (baseSlice 0 P.neg) s : Int) := by positivity
      have hApos : (0 : Int) ≤ (uEval (baseSlice 0 P.pos) s : Int) := by positivity
      nlinarith [mul_nonneg hApos (sub_nonneg.mpr hcast)]

/-- Failing pair `(b, s)` returned when the base-affine decision rejects. -/
def failBaseAffine (P : SignedBiPoly) : Nat × Nat :=
  if ltAllB (baseSlice 0 P.neg) (baseSlice 0 P.pos) then
    (uEval (baseSlice 0 P.pos) (firstFail (baseSlice 1 P.neg) (⟨1, 0⟩ :: baseSlice 1 P.pos)),
      firstFail (baseSlice 1 P.neg) (⟨1, 0⟩ :: baseSlice 1 P.pos))
  else
    (0, firstFail (baseSlice 0 P.neg) (baseSlice 0 P.pos))

theorem failBaseAffine_spec (P : SignedBiPoly) (h : BaseAffine P)
    (hfalse : decideBaseAffinePositive P = false) :
    P.eval (failBaseAffine P).1 (failBaseAffine P).2 ≤ 0 := by
  unfold failBaseAffine
  by_cases hA : ltAllB (baseSlice 0 P.neg) (baseSlice 0 P.pos) = true
  · rw [if_pos hA]
    have hB : ltAllB (baseSlice 1 P.neg) (⟨1, 0⟩ :: baseSlice 1 P.pos) = false := by
      simpa [decideBaseAffinePositive, hA] using hfalse
    have hf := firstFail_spec hB
    rw [uEval_unit_cons] at hf
    rw [baseAffine_eval h]
    have hcast : (1 : Int) +
        (uEval (baseSlice 1 P.pos) (firstFail (baseSlice 1 P.neg) (⟨1, 0⟩ :: baseSlice 1 P.pos)) :
          Int) ≤
        (uEval (baseSlice 1 P.neg) (firstFail (baseSlice 1 P.neg) (⟨1, 0⟩ :: baseSlice 1 P.pos)) :
          Int) := by exact_mod_cast hf
    have hA0 : (0 : Int) ≤ (uEval (baseSlice 0 P.neg)
        (firstFail (baseSlice 1 P.neg) (⟨1, 0⟩ :: baseSlice 1 P.pos)) : Int) := by positivity
    have hApos : (0 : Int) ≤ (uEval (baseSlice 0 P.pos)
        (firstFail (baseSlice 1 P.neg) (⟨1, 0⟩ :: baseSlice 1 P.pos)) : Int) := by positivity
    nlinarith [mul_nonneg hApos (sub_nonneg.mpr hcast)]
  · rw [if_neg hA]
    have hA' : ltAllB (baseSlice 0 P.neg) (baseSlice 0 P.pos) = false := by simpa using hA
    have hf := firstFail_spec hA'
    rw [baseAffine_eval h]
    simp only [Nat.cast_zero, zero_mul, add_zero]
    have hcast : (uEval (baseSlice 0 P.pos) (firstFail (baseSlice 0 P.neg) (baseSlice 0 P.pos)) :
        Int) ≤ (uEval (baseSlice 0 P.neg) (firstFail (baseSlice 0 P.neg) (baseSlice 0 P.pos)) :
        Int) := by exact_mod_cast hf
    linarith

/-- The base-affine decision decides residual orientation of the encoded instance. -/
theorem decideBaseAffinePositive_residual_iff (P : SignedBiPoly) (h : BaseAffine P) :
    decideBaseAffinePositive P = true ↔ ResidualGoal residualWrapper (encodeResidual P) 2 1 := by
  rw [decideBaseAffinePositive_iff P h, residualGoal_encode_iff]

theorem failBaseAffine_residual_spec (P : SignedBiPoly) (h : BaseAffine P)
    (hfalse : decideBaseAffinePositive P = false) :
    sepDiff residualWrapper (encodeResidual P) 2 1 (failBaseAffine P).1 (failBaseAffine P).2 0 ≤ 0 := by
  rw [encodeResidual_sepDiff]
  exact failBaseAffine_spec P h hfalse

/-! ## The payload-affine stratum through the variable swap -/

/-- Exchange of the base and payload exponents of a monomial. -/
def biMonoSwap (m : BiMono) : BiMono := ⟨m.coeff, m.sDeg, m.bDeg⟩

/-- Exchange of the base and payload exponents of a monomial list. -/
def biSwap : List BiMono → List BiMono
  | [] => []
  | m :: P => biMonoSwap m :: biSwap P

theorem biEvalNat_biSwap (P : List BiMono) (b s : Nat) :
    biEvalNat (biSwap P) b s = biEvalNat P s b := by
  induction P with
  | nil => simp [biSwap, biEvalNat]
  | cons m P ih =>
      rw [biSwap, biEvalNat, biEvalNat, ih]
      simp only [biMonoSwap]
      ring

theorem mem_biSwap {P : List BiMono} {m : BiMono} (hm : m ∈ biSwap P) : ∃ q ∈ P, m = biMonoSwap q := by
  induction P with
  | nil => simp [biSwap] at hm
  | cons q P ih =>
      rw [biSwap, List.mem_cons] at hm
      rcases hm with hq | hrest
      · exact ⟨q, by simp, hq⟩
      · obtain ⟨r, hr, hmr⟩ := ih hrest
        exact ⟨r, by simp [hr], hmr⟩

/-- Exchange of the two variables of a signed bivariate polynomial. -/
def signedSwap (P : SignedBiPoly) : SignedBiPoly := ⟨biSwap P.pos, biSwap P.neg⟩

theorem signedSwap_eval (P : SignedBiPoly) (b s : Nat) : (signedSwap P).eval b s = P.eval s b := by
  simp [signedSwap, SignedBiPoly.eval, biEvalNat_biSwap]

/-- Signed polynomials of payload degree at most one. -/
def PayloadAffine (P : SignedBiPoly) : Prop := BaseAffine (signedSwap P)

instance payloadAffineDecidable (P : SignedBiPoly) : Decidable (PayloadAffine P) := by
  unfold PayloadAffine
  infer_instance

/-- Complete executable positivity decision on the payload-affine stratum. -/
def decidePayloadAffinePositive (P : SignedBiPoly) : Bool := decideBaseAffinePositive (signedSwap P)

theorem decidePayloadAffinePositive_iff (P : SignedBiPoly) (h : PayloadAffine P) :
    decidePayloadAffinePositive P = true ↔ ∀ b s, 0 < P.eval b s := by
  rw [decidePayloadAffinePositive, decideBaseAffinePositive_iff _ h]
  constructor
  · intro hall b s
    have hsb := hall s b
    rwa [signedSwap_eval] at hsb
  · intro hall b s
    rw [signedSwap_eval]
    exact hall s b

/-- Failing pair `(b, s)` returned when the payload-affine decision rejects. -/
def failPayloadAffine (P : SignedBiPoly) : Nat × Nat :=
  ((failBaseAffine (signedSwap P)).2, (failBaseAffine (signedSwap P)).1)

theorem failPayloadAffine_spec (P : SignedBiPoly) (h : PayloadAffine P)
    (hfalse : decidePayloadAffinePositive P = false) :
    P.eval (failPayloadAffine P).1 (failPayloadAffine P).2 ≤ 0 := by
  have hs := failBaseAffine_spec (signedSwap P) h hfalse
  rw [signedSwap_eval] at hs
  simpa [failPayloadAffine] using hs

theorem decidePayloadAffinePositive_residual_iff (P : SignedBiPoly) (h : PayloadAffine P) :
    decidePayloadAffinePositive P = true ↔
      ResidualGoal residualWrapper (encodeResidual P) 2 1 := by
  rw [decidePayloadAffinePositive_iff P h, residualGoal_encode_iff]

theorem failPayloadAffine_residual_spec (P : SignedBiPoly) (h : PayloadAffine P)
    (hfalse : decidePayloadAffinePositive P = false) :
    sepDiff residualWrapper (encodeResidual P) 2 1
      (failPayloadAffine P).1 (failPayloadAffine P).2 0 ≤ 0 := by
  rw [encodeResidual_sepDiff]
  exact failPayloadAffine_spec P h hfalse

/-! ## Inclusions and controls -/

/-- The payload-only stratum lies inside the base-affine stratum. -/
theorem baseAffine_of_payloadOnly {P : SignedBiPoly} (h : PayloadOnly P) : BaseAffine P := by
  unfold BaseAffine baseAffineB
  rw [Bool.and_eq_true, List.all_eq_true, List.all_eq_true]
  exact ⟨fun m hm => by simp [payloadOnly_pos h hm], fun m hm => by simp [payloadOnly_neg h hm]⟩

/-- The base-only stratum lies inside the payload-affine stratum. -/
theorem payloadAffine_of_baseOnly {P : SignedBiPoly} (h : BaseOnly P) : PayloadAffine P := by
  unfold PayloadAffine BaseAffine baseAffineB
  rw [Bool.and_eq_true, List.all_eq_true, List.all_eq_true]
  refine ⟨fun m hm => ?_, fun m hm => ?_⟩
  · obtain ⟨q, hq, rfl⟩ := mem_biSwap hm
    simp [biMonoSwap, baseOnly_pos h hq]
  · obtain ⟨q, hq, rfl⟩ := mem_biSwap hm
    simp [biMonoSwap, baseOnly_neg h hq]

/-- `b * s + 1`: base-affine, outside both univariate strata, and positive. -/
def bilinearPositiveControl : SignedBiPoly := ⟨[⟨1, 1, 1⟩, ⟨1, 0, 0⟩], []⟩

theorem bilinearPositiveControl_strata :
    BaseAffine bilinearPositiveControl ∧ PayloadAffine bilinearPositiveControl ∧
      ¬ PayloadOnly bilinearPositiveControl ∧ ¬ BaseOnly bilinearPositiveControl := by
  decide

theorem bilinearPositiveControl_decided :
    decideBaseAffinePositive bilinearPositiveControl = true := by
  decide

/-- `s + 1 - b`: base-affine and rejected, with its computed failing pair. -/
def baseAffineFailControl : SignedBiPoly := ⟨[⟨1, 0, 1⟩, ⟨1, 0, 0⟩], [⟨1, 1, 0⟩]⟩

theorem baseAffineFailControl_rejected :
    BaseAffine baseAffineFailControl ∧ decideBaseAffinePositive baseAffineFailControl = false ∧
      baseAffineFailControl.eval (failBaseAffine baseAffineFailControl).1
        (failBaseAffine baseAffineFailControl).2 ≤ 0 := by
  decide

/-- The mixed fixture `3*b^2*s - 5*b + 7` lies outside both univariate strata and inside the
payload-affine stratum, where the decision rejects it. -/
theorem mixedControl_payloadAffine_rejected :
    PayloadAffine (signedOfIntPoly mixedControl) ∧ ¬ BaseAffine (signedOfIntPoly mixedControl) ∧
      decidePayloadAffinePositive (signedOfIntPoly mixedControl) = false := by
  decide

/-- `b^2 * s^2` lies outside both affine strata. -/
def biquadraticControl : SignedBiPoly := ⟨[⟨1, 2, 2⟩], []⟩

theorem biquadraticControl_outside_affine_strata :
    ¬ BaseAffine biquadraticControl ∧ ¬ PayloadAffine biquadraticControl := by
  decide

end OperatorKO7.Methods.OrientationClosure.SeparableSlopesAffineStrata
