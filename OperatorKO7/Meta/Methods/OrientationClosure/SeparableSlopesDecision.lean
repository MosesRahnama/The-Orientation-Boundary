/-
Executable interfaces and decidable subclasses for the P3.6 residual problem.

Relation: root successor orientation for constructor-local polynomial interpretations.
Property: exact reductions, executable subclass decisions, and extracted counterexamples.
-/
import OperatorKO7.Meta.Methods.OrientationClosure.SeparableSlopesDiophantineBoundary

set_option autoImplicit false

namespace OperatorKO7.Methods.OrientationClosure.SeparableSlopesDecision

open PolynomialOrientationDecision
open SeparableSlopes
open SeparableSlopesDiophantineBoundary

/-- Data for an instance in the slope-at-least-two branch left open by `decideSuccAff`. -/
structure OpenResidualInstance where
  W : List WMono
  R : List RMono
  β : Nat
  a : Nat
  slope : 2 ≤ β
  openBranch : decideSuccAff W R β a = none

/-- An executable total decision interface, including an explicit witness on rejection. -/
structure ResidualDecisionProcedure where
  decide : OpenResidualInstance → Bool
  fail : OpenResidualInstance → Nat × Nat × Nat
  true_iff : ∀ I, decide I = true ↔ ResidualGoal I.W I.R I.β I.a
  false_spec : ∀ I, decide I = false →
    let p := fail I
    sepDiff I.W I.R I.β I.a p.1 p.2.1 p.2.2 ≤ 0

/-- Every signed bivariate polynomial yields a concrete open residual instance. -/
def encodedOpenInstance (P : SignedBiPoly) : OpenResidualInstance :=
  { W := residualWrapper
    R := encodeResidual P
    β := 2
    a := 1
    slope := by omega
    openBranch := encodeResidual_decision_is_open P }

abbrev BivariateNoZeroDecider := SignedBiPoly → Bool

/-- Correctness specification for an executable no-zero decider. -/
def BivariateNoZeroDeciderCorrect (D : BivariateNoZeroDecider) : Prop :=
  ∀ P, D P = true ↔ ∀ b s, P.eval b s ≠ 0

/-- A residual decision procedure decides absence of zeros by encoding the square. -/
def noZeroDeciderOfResidual (D : ResidualDecisionProcedure) : BivariateNoZeroDecider :=
  fun P => D.decide (encodedOpenInstance P.square)

theorem noZeroDeciderOfResidual_correct (D : ResidualDecisionProcedure) :
    BivariateNoZeroDeciderCorrect (noZeroDeciderOfResidual D) := by
  intro P
  rw [noZeroDeciderOfResidual, D.true_iff]
  exact residualGoal_square_iff_noZero P

/-- Correctness specification for an executable zero-existence decider. -/
def BivariateZeroDeciderCorrect (D : SignedBiPoly → Bool) : Prop :=
  ∀ P, D P = true ↔ ∃ b s, P.eval b s = 0

/-- Boolean complement of the no-zero decision induced by a residual decider. -/
def zeroDeciderOfResidual (D : ResidualDecisionProcedure) : SignedBiPoly → Bool :=
  fun P => !(noZeroDeciderOfResidual D P)

/-- Any executable total residual decision yields an executable decision for zeros of arbitrary
signed bivariate polynomials over `Nat × Nat`. -/
theorem residual_decider_implies_bivariate_zero_decider (D : ResidualDecisionProcedure) :
    BivariateZeroDeciderCorrect (zeroDeciderOfResidual D) := by
  classical
  intro P
  rw [zeroDeciderOfResidual, Bool.not_eq_true_eq_eq_false]
  have h := noZeroDeciderOfResidual_correct D P
  rw [Bool.eq_false_iff]
  constructor
  · intro hn
    have hnall : ¬ ∀ b s, P.eval b s ≠ 0 := fun hall => hn (h.mpr hall)
    push_neg at hnall
    exact hnall
  · rintro ⟨b, s, hz⟩ htrue
    exact (h.mp htrue b s) hz

/-! ## A complete decision on the monotone base-counter stratum -/

/-- The residual is nondecreasing in the base and counter coordinates. -/
def NondecreasingBN (W : List WMono) (R : List RMono) (β a : Nat) : Prop :=
  (∀ b b' s n, b ≤ b' →
    sepDiff W R β a b s n ≤ sepDiff W R β a b' s n) ∧
  (∀ b s n n', n ≤ n' →
    sepDiff W R β a b s n ≤ sepDiff W R β a b s n')

theorem residualGoal_iff_payload_axis {W : List WMono} {R : List RMono} {β a : Nat}
    (hmono : NondecreasingBN W R β a) :
    ResidualGoal W R β a ↔ ∀ s, 0 < sepDiff W R β a 0 s 0 := by
  constructor
  · intro h s
    exact h 0 s 0
  · intro h b s n
    have hb := hmono.1 0 b s 0 (Nat.zero_le b)
    have hn := hmono.2 b s 0 n (Nat.zero_le n)
    have h0 := h s
    omega

/-- Coefficient scaling for the univariate polynomial syntax. -/
def scaleUPoly (k : Nat) : List UMono → List UMono
  | [] => []
  | m :: P => ⟨k * m.coeff, m.deg⟩ :: scaleUPoly k P

theorem uEval_scaleUPoly (k : Nat) (P : List UMono) (s : Nat) :
    uEval (scaleUPoly k P) s = k * uEval P s := by
  induction P with
  | nil => simp [scaleUPoly, uEval]
  | cons m P ih =>
      simp [scaleUPoly, uEval, ih]
      ring

/-- Lower side of the residual inequality at base and counter zero. -/
def residualLowerAtZero (W : List WMono) (R : List RMono) : List UMono :=
  scaleUPoly (wLin W 0) (rAtBN R 0 0) ++ wAtY0 W

/-- Upper side of the residual inequality at base and counter zero. -/
def residualUpperAtZero (R : List RMono) (a : Nat) : List UMono :=
  rAtBN R 0 a

theorem uEval_residualLowerAtZero (W : List WMono) (R : List RMono) (s : Nat) :
    uEval (residualLowerAtZero W R) s =
      wLin W 0 * rEval R 0 s 0 + wEval W s 0 := by
  simp [residualLowerAtZero, uEval_append, uEval_scaleUPoly, uEval_rAtBN, uEval_wAtY0]

theorem uEval_residualUpperAtZero (R : List RMono) (a s : Nat) :
    uEval (residualUpperAtZero R a) s = rEval R 0 s a := by
  simp [residualUpperAtZero, uEval_rAtBN]

theorem payload_axis_iff_ltAllB (W : List WMono) (R : List RMono) (β a : Nat) :
    (∀ s, 0 < sepDiff W R β a 0 s 0) ↔
      ltAllB (residualLowerAtZero W R) (residualUpperAtZero R a) = true := by
  rw [ltAllB_iff]
  constructor
  · intro h s
    have hs := h s
    rw [sepDiff, Nat.mul_zero, Nat.zero_add] at hs
    rw [uEval_residualLowerAtZero, uEval_residualUpperAtZero]
    have hs' :
        0 < (rEval R 0 s a : Int) -
          ((wLin W 0 * rEval R 0 s 0 + wEval W s 0 : Nat) : Int) := by
      convert hs using 1
      all_goals
        push_cast
        ring
    have hlt :
        ((wLin W 0 * rEval R 0 s 0 + wEval W s 0 : Nat) : Int) <
          (rEval R 0 s a : Int) := sub_pos.mp hs'
    exact_mod_cast hlt
  · intro h s
    have hs := h s
    rw [uEval_residualLowerAtZero, uEval_residualUpperAtZero] at hs
    unfold sepDiff
    simp only [Nat.mul_zero, Nat.zero_add]
    have hcast :
        ((wLin W 0 * rEval R 0 s 0 + wEval W s 0 : Nat) : Int) <
          (rEval R 0 s a : Int) := by exact_mod_cast hs
    have hpos := sub_pos.mpr hcast
    convert hpos using 1
    all_goals
      push_cast
      ring

/-- Executable decision for a residual known to be nondecreasing in base and counter. -/
def decideResidualMonotone (W : List WMono) (R : List RMono) (_β a : Nat) : Bool :=
  ltAllB (residualLowerAtZero W R) (residualUpperAtZero R a)

theorem decideResidualMonotone_iff {W : List WMono} {R : List RMono} {β a : Nat}
    (hmono : NondecreasingBN W R β a) :
    decideResidualMonotone W R β a = true ↔ ResidualGoal W R β a := by
  rw [residualGoal_iff_payload_axis hmono, payload_axis_iff_ltAllB]
  rfl

/-- The payload counterexample returned when the monotone decision rejects. -/
def failResidualMonotone (W : List WMono) (R : List RMono) (a : Nat) : Nat × Nat × Nat :=
  (0, firstFail (residualLowerAtZero W R) (residualUpperAtZero R a), 0)

theorem failResidualMonotone_spec (W : List WMono) (R : List RMono) (β a : Nat)
    (hfalse : decideResidualMonotone W R β a = false) :
    let p := failResidualMonotone W R a
    sepDiff W R β a p.1 p.2.1 p.2.2 ≤ 0 := by
  have hf := firstFail_spec hfalse
  simp only [failResidualMonotone]
  rw [uEval_residualLowerAtZero, uEval_residualUpperAtZero] at hf
  unfold sepDiff
  simp only [Nat.mul_zero, Nat.zero_add]
  have hcast : (rEval R 0 (firstFail (residualLowerAtZero W R)
      (residualUpperAtZero R a)) a : Int) ≤
      ((wLin W 0 * rEval R 0 (firstFail (residualLowerAtZero W R)
          (residualUpperAtZero R a)) 0 +
        wEval W (firstFail (residualLowerAtZero W R)
          (residualUpperAtZero R a)) 0 : Nat) : Int) := by
    exact_mod_cast hf
  have hnonpos := sub_nonpos.mpr hcast
  convert hnonpos using 1
  all_goals
    push_cast
    ring

/-! ## A finite coefficient certificate for the monotone stratum -/

/-- Boolean coefficient test for one recursor monomial in the monotone stratum. -/
def residualMonomialCertificateB (m : RMono) : Bool :=
  decide (m.coeff = 0 ∨ ((m.nDeg = 0 ∧ m.bDeg = 0) ∨ m.nDeg = 1))

/-- Every live recursor monomial is either a base-independent degree-zero term or a
degree-one term whose counter gain is nondecreasing. Membership is computed from the list. -/
def ResidualMonotoneCertificate (W : List WMono) (R : List RMono) (β : Nat) : Prop :=
  wLin W 0 ≤ β ∧
    R.all residualMonomialCertificateB = true

instance residualMonotoneCertificateDecidable (W : List WMono) (R : List RMono) (β : Nat) :
    Decidable (ResidualMonotoneCertificate W R β) := by
  unfold ResidualMonotoneCertificate
  infer_instance

theorem monomialCounterPoly_degree_zero (β a w n : Nat) :
    monomialCounterPoly β a w 0 n = 1 - (w : Int) := by
  simp [monomialCounterPoly]

theorem monomialCounterPoly_degree_one (β a w n : Nat) :
    monomialCounterPoly β a w 1 n =
      ((β : Int) - w) * n + a := by
  simp [monomialCounterPoly]
  ring

theorem monomialCounterPoly_degree_one_nonneg {β w a n : Nat} (hw : w ≤ β) :
    0 ≤ monomialCounterPoly β a w 1 n := by
  rw [monomialCounterPoly_degree_one]
  have hbw : (w : Int) ≤ β := by exact_mod_cast hw
  have h : (0 : Int) ≤ (β : Int) - w := sub_nonneg.mpr hbw
  positivity

theorem monomialCounterPoly_degree_one_mono {β w a n n' : Nat}
    (hw : w ≤ β) (hn : n ≤ n') :
    monomialCounterPoly β a w 1 n ≤ monomialCounterPoly β a w 1 n' := by
  rw [monomialCounterPoly_degree_one, monomialCounterPoly_degree_one]
  have hbw : (w : Int) ≤ β := by exact_mod_cast hw
  have hcoef : (0 : Int) ≤ (β : Int) - w := sub_nonneg.mpr hbw
  have hcast : (n : Int) ≤ n' := by exact_mod_cast hn
  nlinarith

theorem residualMonomialCertificate_of_mem {W : List WMono} {R : List RMono} {β : Nat}
    (hc : ResidualMonotoneCertificate W R β) {m : RMono} (hm : m ∈ R) :
    m.coeff = 0 ∨ ((m.nDeg = 0 ∧ m.bDeg = 0) ∨ m.nDeg = 1) := by
  have hb := (List.all_eq_true.mp hc.2) m hm
  simpa [residualMonomialCertificateB] using hb

theorem certified_monomial_base_mono {W : List WMono} {R : List RMono} {β a : Nat}
    (hc : ResidualMonotoneCertificate W R β) {m : RMono} (hm : m ∈ R)
    (b b' s n : Nat) (hbb : b ≤ b') :
    (m.coeff : Int) * (b ^ m.bDeg : Int) * (s ^ m.sDeg : Int) *
        monomialCounterPoly β a (wLin W 0) m.nDeg n ≤
      (m.coeff : Int) * (b' ^ m.bDeg : Int) * (s ^ m.sDeg : Int) *
        monomialCounterPoly β a (wLin W 0) m.nDeg n := by
  rcases residualMonomialCertificate_of_mem hc hm with hz | hshape
  · simp [hz]
  · rcases hshape with ⟨hk, hb0⟩ | hk
    · rw [hk, hb0]
      simp [monomialCounterPoly_degree_zero]
    · rw [hk]
      have hpow : b ^ m.bDeg ≤ b' ^ m.bDeg := Nat.pow_le_pow_left hbb m.bDeg
      have hq := monomialCounterPoly_degree_one_nonneg (a := a) (n := n) hc.1
      have hcoef : (0 : Int) ≤ m.coeff := by positivity
      have hs : (0 : Int) ≤ s ^ m.sDeg := by positivity
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (by exact_mod_cast hpow) hcoef) hs) hq

theorem certified_monomial_counter_mono {W : List WMono} {R : List RMono} {β a : Nat}
    (hc : ResidualMonotoneCertificate W R β) {m : RMono} (hm : m ∈ R)
    (b s n n' : Nat) (hn : n ≤ n') :
    (m.coeff : Int) * (b ^ m.bDeg : Int) * (s ^ m.sDeg : Int) *
        monomialCounterPoly β a (wLin W 0) m.nDeg n ≤
      (m.coeff : Int) * (b ^ m.bDeg : Int) * (s ^ m.sDeg : Int) *
        monomialCounterPoly β a (wLin W 0) m.nDeg n' := by
  rcases residualMonomialCertificate_of_mem hc hm with hz | hshape
  · simp [hz]
  · rcases hshape with ⟨hk, -⟩ | hk
    · rw [hk]
      simp [monomialCounterPoly_degree_zero]
    · rw [hk]
      have hq := monomialCounterPoly_degree_one_mono (a := a) hc.1 hn
      have hnonneg : (0 : Int) ≤ (m.coeff : Int) * b ^ m.bDeg * s ^ m.sDeg := by positivity
      exact mul_le_mul_of_nonneg_left hq hnonneg

/-- Sum of the residual monomial contributions before subtracting the wrapper cost. -/
def residualTermSum (W : List WMono) (R : List RMono) (β a b s n : Nat) : Int :=
  (R.map (fun m => (m.coeff : Int) * (b ^ m.bDeg : Int) * (s ^ m.sDeg : Int) *
    monomialCounterPoly β a (wLin W 0) m.nDeg n)).sum

theorem residualTermSum_base_mono {W : List WMono} {R : List RMono} {β a : Nat}
    (hc : ResidualMonotoneCertificate W R β) (b b' s n : Nat) (hbb : b ≤ b') :
    residualTermSum W R β a b s n ≤ residualTermSum W R β a b' s n := by
  induction R with
  | nil => simp [residualTermSum]
  | cons m R ih =>
      have hhead := certified_monomial_base_mono (a := a) hc (m := m) (by simp) b b' s n hbb
      have htailAll : R.all residualMonomialCertificateB = true := by
        rw [List.all_eq_true]
        intro q hq
        exact (List.all_eq_true.mp hc.2) q (by simp [hq])
      have htail : ResidualMonotoneCertificate W R β := ⟨hc.1, htailAll⟩
      have hrest := ih htail
      simp only [residualTermSum, List.map_cons, List.sum_cons]
      exact add_le_add hhead hrest

theorem residualTermSum_counter_mono {W : List WMono} {R : List RMono} {β a : Nat}
    (hc : ResidualMonotoneCertificate W R β) (b s n n' : Nat) (hn : n ≤ n') :
    residualTermSum W R β a b s n ≤ residualTermSum W R β a b s n' := by
  induction R with
  | nil => simp [residualTermSum]
  | cons m R ih =>
      have hhead := certified_monomial_counter_mono (a := a) hc (m := m) (by simp) b s n n' hn
      have htailAll : R.all residualMonomialCertificateB = true := by
        rw [List.all_eq_true]
        intro q hq
        exact (List.all_eq_true.mp hc.2) q (by simp [hq])
      have htail : ResidualMonotoneCertificate W R β := ⟨hc.1, htailAll⟩
      have hrest := ih htail
      simp only [residualTermSum, List.map_cons, List.sum_cons]
      exact add_le_add hhead hrest

theorem residualMonotoneCertificate_sound {W : List WMono} {R : List RMono} {β a : Nat}
    (hc : ResidualMonotoneCertificate W R β) : NondecreasingBN W R β a := by
  unfold NondecreasingBN
  constructor
  · intro b b' s n hbb
    rw [← separableSum_eq_sepDiff W R β a,
      ← separableSum_eq_sepDiff W R β a]
    unfold separableSum
    exact sub_le_sub_right (residualTermSum_base_mono hc b b' s n hbb) _
  · intro b s n n' hnn
    rw [← separableSum_eq_sepDiff W R β a,
      ← separableSum_eq_sepDiff W R β a]
    unfold separableSum
    exact sub_le_sub_right (residualTermSum_counter_mono hc b s n n' hnn) _

/-- A certified residual receives a complete executable decision and an explicit failing triple. -/
theorem certifiedResidualDecision_iff {W : List WMono} {R : List RMono} {β a : Nat}
    (hc : ResidualMonotoneCertificate W R β) :
    decideResidualMonotone W R β a = true ↔ ResidualGoal W R β a :=
  decideResidualMonotone_iff (residualMonotoneCertificate_sound hc)

/-- The positive embedding fixture satisfies the coefficient certificate. -/
theorem positiveControl_certificate :
    ResidualMonotoneCertificate residualWrapper (encodeResidual positiveControl) 2 := by
  decide

def cancelBControl : SignedBiPoly :=
  ⟨[⟨1, 1, 0⟩], [⟨1, 1, 0⟩]⟩

/-- The coefficient certificate is sufficient but not necessary for base-counter monotonicity. -/
theorem cancelBControl_monotone_outside_certificate :
    NondecreasingBN residualWrapper (encodeResidual cancelBControl) 2 1 ∧
      ¬ ResidualMonotoneCertificate residualWrapper (encodeResidual cancelBControl) 2 := by
  constructor
  · constructor
    · intro b b' s n hbb
      rw [encodeResidual_sepDiff, encodeResidual_sepDiff]
      simp [cancelBControl, SignedBiPoly.eval, biEvalNat]
    · intro b s n n' hnn
      rw [encodeResidual_sepDiff, encodeResidual_sepDiff]
  · decide

/-! ## Exact univariate strata inside the signed-bivariate embedding -/

/-- Erases the zero base exponent from a bivariate monomial list. -/
def biToPayload (P : List BiMono) : List UMono :=
  P.map fun m => ⟨m.coeff, m.sDeg⟩

/-- Executable recognition of signed polynomials that depend only on payload. -/
def payloadOnlyB (P : SignedBiPoly) : Bool :=
  P.pos.all (fun m => decide (m.bDeg = 0)) &&
    P.neg.all (fun m => decide (m.bDeg = 0))

/-- Propositional meaning of the executable payload-only test. -/
def PayloadOnly (P : SignedBiPoly) : Prop := payloadOnlyB P = true

instance payloadOnlyDecidable (P : SignedBiPoly) : Decidable (PayloadOnly P) := by
  unfold PayloadOnly
  infer_instance

theorem payloadOnly_pos {P : SignedBiPoly} (h : PayloadOnly P) {m : BiMono}
    (hm : m ∈ P.pos) : m.bDeg = 0 := by
  unfold PayloadOnly payloadOnlyB at h
  rw [Bool.and_eq_true] at h
  have hp := h.1
  have hm' := (List.all_eq_true.mp hp) m hm
  simpa using hm'

theorem payloadOnly_neg {P : SignedBiPoly} (h : PayloadOnly P) {m : BiMono}
    (hm : m ∈ P.neg) : m.bDeg = 0 := by
  unfold PayloadOnly payloadOnlyB at h
  rw [Bool.and_eq_true] at h
  have hn := h.2
  have hm' := (List.all_eq_true.mp hn) m hm
  simpa using hm'

theorem biEvalNat_biToPayload {P : List BiMono}
    (h : ∀ m ∈ P, m.bDeg = 0) (b s : Nat) :
    biEvalNat P b s = uEval (biToPayload P) s := by
  induction P with
  | nil => simp [biEvalNat, biToPayload, uEval]
  | cons m P ih =>
      have hm : m.bDeg = 0 := h m (by simp)
      have htail : ∀ q ∈ P, q.bDeg = 0 := by
        intro q hq
        exact h q (by simp [hq])
      simp [biEvalNat, biToPayload, uEval, hm, ih htail]

theorem payloadOnly_eval (P : SignedBiPoly) (h : PayloadOnly P) (b s : Nat) :
    P.eval b s =
      (uEval (biToPayload P.pos) s : Int) - (uEval (biToPayload P.neg) s : Int) := by
  rw [SignedBiPoly.eval,
    biEvalNat_biToPayload (fun m hm => payloadOnly_pos h hm) b s,
    biEvalNat_biToPayload (fun m hm => payloadOnly_neg h hm) b s]

/-- Complete executable positivity decision on the payload-only stratum. -/
def decidePayloadOnlyPositive (P : SignedBiPoly) : Bool :=
  ltAllB (biToPayload P.neg) (biToPayload P.pos)

theorem decidePayloadOnlyPositive_iff (P : SignedBiPoly) (h : PayloadOnly P) :
    decidePayloadOnlyPositive P = true ↔ ∀ b s, 0 < P.eval b s := by
  rw [decidePayloadOnlyPositive, ltAllB_iff]
  constructor
  · intro hall b s
    rw [payloadOnly_eval P h b s]
    have hcast : (uEval (biToPayload P.neg) s : Int) <
        (uEval (biToPayload P.pos) s : Int) := by exact_mod_cast hall s
    exact sub_pos.mpr hcast
  · intro hall s
    have hs := hall 0 s
    rw [payloadOnly_eval P h 0 s] at hs
    have hcast : (uEval (biToPayload P.neg) s : Int) <
        (uEval (biToPayload P.pos) s : Int) := sub_pos.mp hs
    exact_mod_cast hcast

/-- Payload coordinate returned when the payload-only positivity decision rejects. -/
def failPayloadOnly (P : SignedBiPoly) : Nat :=
  firstFail (biToPayload P.neg) (biToPayload P.pos)

theorem failPayloadOnly_spec (P : SignedBiPoly) (h : PayloadOnly P)
    (hfalse : decidePayloadOnlyPositive P = false) :
    P.eval 0 (failPayloadOnly P) ≤ 0 := by
  have hf := firstFail_spec hfalse
  rw [payloadOnly_eval P h]
  have hcast : (uEval (biToPayload P.pos) (failPayloadOnly P) : Int) ≤
      (uEval (biToPayload P.neg) (failPayloadOnly P) : Int) := by exact_mod_cast hf
  exact sub_nonpos.mpr hcast

theorem failPayloadOnly_residual_spec (P : SignedBiPoly) (h : PayloadOnly P)
    (hfalse : decidePayloadOnlyPositive P = false) :
    sepDiff residualWrapper (encodeResidual P) 2 1 0 (failPayloadOnly P) 0 ≤ 0 := by
  rw [encodeResidual_sepDiff]
  exact failPayloadOnly_spec P h hfalse

/-- Erases the zero payload exponent from a bivariate monomial list. -/
def biToBase (P : List BiMono) : List UMono :=
  P.map fun m => ⟨m.coeff, m.bDeg⟩

/-- Executable recognition of signed polynomials that depend only on the base. -/
def baseOnlyB (P : SignedBiPoly) : Bool :=
  P.pos.all (fun m => decide (m.sDeg = 0)) &&
    P.neg.all (fun m => decide (m.sDeg = 0))

/-- Propositional meaning of the executable base-only test. -/
def BaseOnly (P : SignedBiPoly) : Prop := baseOnlyB P = true

instance baseOnlyDecidable (P : SignedBiPoly) : Decidable (BaseOnly P) := by
  unfold BaseOnly
  infer_instance

theorem baseOnly_pos {P : SignedBiPoly} (h : BaseOnly P) {m : BiMono}
    (hm : m ∈ P.pos) : m.sDeg = 0 := by
  unfold BaseOnly baseOnlyB at h
  rw [Bool.and_eq_true] at h
  have hp := h.1
  have hm' := (List.all_eq_true.mp hp) m hm
  simpa using hm'

theorem baseOnly_neg {P : SignedBiPoly} (h : BaseOnly P) {m : BiMono}
    (hm : m ∈ P.neg) : m.sDeg = 0 := by
  unfold BaseOnly baseOnlyB at h
  rw [Bool.and_eq_true] at h
  have hn := h.2
  have hm' := (List.all_eq_true.mp hn) m hm
  simpa using hm'

theorem biEvalNat_biToBase {P : List BiMono}
    (h : ∀ m ∈ P, m.sDeg = 0) (b s : Nat) :
    biEvalNat P b s = uEval (biToBase P) b := by
  induction P with
  | nil => simp [biEvalNat, biToBase, uEval]
  | cons m P ih =>
      have hm : m.sDeg = 0 := h m (by simp)
      have htail : ∀ q ∈ P, q.sDeg = 0 := by
        intro q hq
        exact h q (by simp [hq])
      simp [biEvalNat, biToBase, uEval, hm, ih htail]

theorem baseOnly_eval (P : SignedBiPoly) (h : BaseOnly P) (b s : Nat) :
    P.eval b s =
      (uEval (biToBase P.pos) b : Int) - (uEval (biToBase P.neg) b : Int) := by
  rw [SignedBiPoly.eval,
    biEvalNat_biToBase (fun m hm => baseOnly_pos h hm) b s,
    biEvalNat_biToBase (fun m hm => baseOnly_neg h hm) b s]

/-- Complete executable positivity decision on the base-only stratum. -/
def decideBaseOnlyPositive (P : SignedBiPoly) : Bool :=
  ltAllB (biToBase P.neg) (biToBase P.pos)

theorem decideBaseOnlyPositive_iff (P : SignedBiPoly) (h : BaseOnly P) :
    decideBaseOnlyPositive P = true ↔ ∀ b s, 0 < P.eval b s := by
  rw [decideBaseOnlyPositive, ltAllB_iff]
  constructor
  · intro hall b s
    rw [baseOnly_eval P h b s]
    have hcast : (uEval (biToBase P.neg) b : Int) <
        (uEval (biToBase P.pos) b : Int) := by exact_mod_cast hall b
    exact sub_pos.mpr hcast
  · intro hall b
    have hb := hall b 0
    rw [baseOnly_eval P h b 0] at hb
    have hcast : (uEval (biToBase P.neg) b : Int) <
        (uEval (biToBase P.pos) b : Int) := sub_pos.mp hb
    exact_mod_cast hcast

/-- Base coordinate returned when the base-only positivity decision rejects. -/
def failBaseOnly (P : SignedBiPoly) : Nat :=
  firstFail (biToBase P.neg) (biToBase P.pos)

theorem failBaseOnly_spec (P : SignedBiPoly) (h : BaseOnly P)
    (hfalse : decideBaseOnlyPositive P = false) :
    P.eval (failBaseOnly P) 0 ≤ 0 := by
  have hf := firstFail_spec hfalse
  rw [baseOnly_eval P h]
  have hcast : (uEval (biToBase P.pos) (failBaseOnly P) : Int) ≤
      (uEval (biToBase P.neg) (failBaseOnly P) : Int) := by exact_mod_cast hf
  exact sub_nonpos.mpr hcast

theorem failBaseOnly_residual_spec (P : SignedBiPoly) (h : BaseOnly P)
    (hfalse : decideBaseOnlyPositive P = false) :
    sepDiff residualWrapper (encodeResidual P) 2 1 (failBaseOnly P) 0 0 ≤ 0 := by
  rw [encodeResidual_sepDiff]
  exact failBaseOnly_spec P h hfalse

/-- The mixed fixture depends genuinely on both variables and lies outside both univariate strata. -/
theorem mixedControl_outside_univariate_strata :
    ¬ PayloadOnly (signedOfIntPoly mixedControl) ∧
      ¬ BaseOnly (signedOfIntPoly mixedControl) := by
  decide

end OperatorKO7.Methods.OrientationClosure.SeparableSlopesDecision
