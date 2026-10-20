/-
Complete executable positivity decision for signed bivariate polynomials given by exactly one
positive and one negative monomial, with extracted failing pairs and the residual adapter.

Relation: root successor orientation for constructor-local polynomial interpretations.
Property: sound and complete Boolean decision on the monomial-difference stratum of the
P3.6 open branch, with controls lying outside the monotone, base-affine, and payload-affine
families.
-/
import OperatorKO7.Meta.Methods.OrientationClosure.SeparableSlopesAffineStrata

set_option autoImplicit false

namespace OperatorKO7.Methods.OrientationClosure.SeparableSlopesMonomialStratum

open PolynomialOrientationDecision
open SeparableSlopes
open SeparableSlopesDiophantineBoundary
open SeparableSlopesDecision
open SeparableSlopesAffineStrata

/-- A signed bivariate polynomial given by exactly one positive and one negative monomial. -/
def MonomialDifference (P : SignedBiPoly) : Prop :=
  ∃ p q : BiMono, P.pos = [p] ∧ P.neg = [q]

/-- Boolean recognizer for the monomial-difference stratum. -/
def monomialDifferenceB (P : SignedBiPoly) : Bool :=
  decide (P.pos.length = 1 ∧ P.neg.length = 1)

theorem exists_of_length_one {α : Type} {l : List α} (h : l.length = 1) :
    ∃ a, l = [a] := by
  cases l with
  | nil => simp at h
  | cons a t =>
      cases t with
      | nil => exact ⟨a, rfl⟩
      | cons b u =>
          simp only [List.length_cons] at h
          omega

theorem monomialDifference_iff (P : SignedBiPoly) :
    monomialDifferenceB P = true ↔ MonomialDifference P := by
  unfold monomialDifferenceB MonomialDifference
  rw [decide_eq_true_eq]
  constructor
  · rintro ⟨hp, hn⟩
    obtain ⟨p, hp'⟩ := exists_of_length_one hp
    obtain ⟨q, hq'⟩ := exists_of_length_one hn
    exact ⟨p, q, hp', hq'⟩
  · rintro ⟨p, q, hp, hq⟩
    rw [hp, hq]
    exact ⟨rfl, rfl⟩

/-- Exact positivity decision for one positive monomial against one negative monomial:
the positive monomial must be a nonzero constant, and the negative monomial must either
vanish (zero coefficient) or be a strictly smaller constant. -/
def decideMonoPairPositive (p q : BiMono) : Bool :=
  decide (p.bDeg = 0 ∧ p.sDeg = 0 ∧ 1 ≤ p.coeff ∧
    (q.coeff = 0 ∨ (q.bDeg = 0 ∧ q.sDeg = 0 ∧ q.coeff < p.coeff)))

/-- Stratum-level decision; off-stratum instances reject. -/
def decideMonomialDifferencePositive (P : SignedBiPoly) : Bool :=
  match P.pos, P.neg with
  | [p], [q] => decideMonoPairPositive p q
  | _, _ => false

theorem decideMonomialDifferencePositive_pair (p q : BiMono) :
    decideMonomialDifferencePositive ⟨[p], [q]⟩ = decideMonoPairPositive p q := rfl

/-- Evaluation of a one-positive one-negative monomial polynomial. -/
theorem monoPair_eval (p q : BiMono) (b s : Nat) :
    (⟨[p], [q]⟩ : SignedBiPoly).eval b s =
      ((p.coeff * b ^ p.bDeg * s ^ p.sDeg : Nat) : Int) -
        ((q.coeff * b ^ q.bDeg * s ^ q.sDeg : Nat) : Int) := by
  simp [SignedBiPoly.eval, biEvalNat]

theorem nat_zero_pow_of_ne_zero {k : Nat} (h : k ≠ 0) : (0 : Nat) ^ k = 0 := by
  cases k with
  | zero => exact absurd rfl h
  | succ _ => rfl

/-- When the positive monomial is not a nonzero constant, the origin is a failing pair. -/
theorem mono_eval_origin_nonpos (p q : BiMono)
    (h : ¬ (p.bDeg = 0 ∧ p.sDeg = 0 ∧ 1 ≤ p.coeff)) :
    (⟨[p], [q]⟩ : SignedBiPoly).eval 0 0 ≤ 0 := by
  rw [monoPair_eval]
  have hpos0 : p.coeff * (0 : Nat) ^ p.bDeg * (0 : Nat) ^ p.sDeg = 0 := by
    by_cases hb : p.bDeg = 0
    · by_cases hs : p.sDeg = 0
      · have hc : p.coeff = 0 := by
          by_contra hcne
          exact h ⟨hb, hs, Nat.one_le_iff_ne_zero.mpr hcne⟩
        simp [hb, hs, hc]
      · rw [nat_zero_pow_of_ne_zero hs]; simp
    · rw [nat_zero_pow_of_ne_zero hb]; simp
  rw [hpos0]
  simp only [Nat.cast_zero, zero_sub]
  omega

/-- A negative monomial growing in `b` is caught at `(p.coeff + 1, 1)`. -/
theorem monoPair_eval_nonpos_of_bDeg_ne_zero (p q : BiMono)
    (hpb : p.bDeg = 0) (hps : p.sDeg = 0) (hq1 : 1 ≤ q.coeff) (hqb : q.bDeg ≠ 0) :
    (⟨[p], [q]⟩ : SignedBiPoly).eval (p.coeff + 1) 1 ≤ 0 := by
  rw [monoPair_eval, hpb, hps]
  simp only [pow_zero, mul_one, one_pow]
  have hle : p.coeff + 1 ≤ q.coeff * (p.coeff + 1) ^ q.bDeg := by
    calc p.coeff + 1 = 1 * (p.coeff + 1) := (one_mul _).symm
      _ ≤ q.coeff * (p.coeff + 1) ^ q.bDeg :=
          Nat.mul_le_mul hq1 (Nat.le_self_pow hqb _)
  have hle' : (p.coeff : Int) + 1 ≤ (q.coeff * (p.coeff + 1) ^ q.bDeg : Nat) := by
    exact_mod_cast hle
  omega

/-- A negative monomial growing in `s` is caught at `(1, p.coeff + 1)`. -/
theorem monoPair_eval_nonpos_of_sDeg_ne_zero (p q : BiMono)
    (hpb : p.bDeg = 0) (hps : p.sDeg = 0) (hq1 : 1 ≤ q.coeff) (hqs : q.sDeg ≠ 0) :
    (⟨[p], [q]⟩ : SignedBiPoly).eval 1 (p.coeff + 1) ≤ 0 := by
  rw [monoPair_eval, hpb, hps]
  simp only [pow_zero, mul_one, one_pow]
  have hle : p.coeff + 1 ≤ q.coeff * (p.coeff + 1) ^ q.sDeg := by
    calc p.coeff + 1 = 1 * (p.coeff + 1) := (one_mul _).symm
      _ ≤ q.coeff * (p.coeff + 1) ^ q.sDeg :=
          Nat.mul_le_mul hq1 (Nat.le_self_pow hqs _)
  have hle' : (p.coeff : Int) + 1 ≤ (q.coeff * (p.coeff + 1) ^ q.sDeg : Nat) := by
    exact_mod_cast hle
  omega

/-- At the origin, two constant monomials compare by coefficient. -/
theorem monoPair_eval_origin_of_const (p q : BiMono)
    (hpb : p.bDeg = 0) (hps : p.sDeg = 0) (hqb : q.bDeg = 0) (hqs : q.sDeg = 0) :
    (⟨[p], [q]⟩ : SignedBiPoly).eval 0 0 = (p.coeff : Int) - q.coeff := by
  rw [monoPair_eval, hpb, hps, hqb, hqs]
  simp

/-- The monomial-pair decision is sound and complete. -/
theorem decideMonoPairPositive_iff (p q : BiMono) :
    decideMonoPairPositive p q = true ↔
      ∀ b s : Nat, 0 < (⟨[p], [q]⟩ : SignedBiPoly).eval b s := by
  unfold decideMonoPairPositive
  rw [decide_eq_true_eq]
  constructor
  · rintro ⟨hpb, hps, hpc, hq⟩
    intro b s
    rcases hq with hq0 | ⟨hqb, hqs, hqlt⟩
    · rw [monoPair_eval, hpb, hps, hq0]
      simp only [pow_zero, mul_one, zero_mul, Nat.cast_zero, sub_zero]
      have h1 : (1 : Int) ≤ p.coeff := by exact_mod_cast hpc
      omega
    · rw [monoPair_eval, hpb, hps, hqb, hqs]
      simp only [pow_zero, mul_one]
      have hlt : (q.coeff : Int) < p.coeff := by exact_mod_cast hqlt
      omega
  · intro h
    have hpb : p.bDeg = 0 := by
      by_contra hne
      have h0 := mono_eval_origin_nonpos p q (fun hc => hne hc.1)
      have hpos := h 0 0
      omega
    have hps : p.sDeg = 0 := by
      by_contra hne
      have h0 := mono_eval_origin_nonpos p q (fun hc => hne hc.2.1)
      have hpos := h 0 0
      omega
    have hpc : 1 ≤ p.coeff := by
      have hpos := h 0 0
      rw [monoPair_eval, hpb, hps] at hpos
      simp only [pow_zero, mul_one] at hpos
      omega
    refine ⟨hpb, hps, hpc, ?_⟩
    by_cases hq0 : q.coeff = 0
    · exact Or.inl hq0
    · right
      have hq1 : 1 ≤ q.coeff := Nat.one_le_iff_ne_zero.mpr hq0
      have hqb : q.bDeg = 0 := by
        by_contra hne
        have h0 := monoPair_eval_nonpos_of_bDeg_ne_zero p q hpb hps hq1 hne
        have hpos := h (p.coeff + 1) 1
        omega
      have hqs : q.sDeg = 0 := by
        by_contra hne
        have h0 := monoPair_eval_nonpos_of_sDeg_ne_zero p q hpb hps hq1 hne
        have hpos := h 1 (p.coeff + 1)
        omega
      refine ⟨hqb, hqs, ?_⟩
      have hpos := h 0 0
      rw [monoPair_eval_origin_of_const p q hpb hps hqb hqs] at hpos
      omega

/-- Failing pair extracted when the monomial-pair decision rejects. -/
def failMonoPair (p q : BiMono) : Nat × Nat :=
  if p.bDeg = 0 ∧ p.sDeg = 0 ∧ 1 ≤ p.coeff then
    if q.bDeg = 0 then
      if q.sDeg = 0 then (0, 0) else (1, p.coeff + 1)
    else (p.coeff + 1, 1)
  else (0, 0)

/-- The extracted pair witnesses nonpositivity. -/
theorem failMonoPair_spec (p q : BiMono)
    (hfalse : decideMonoPairPositive p q = false) :
    (⟨[p], [q]⟩ : SignedBiPoly).eval (failMonoPair p q).1 (failMonoPair p q).2 ≤ 0 := by
  unfold decideMonoPairPositive at hfalse
  have hnot := of_decide_eq_false hfalse
  unfold failMonoPair
  by_cases hp : p.bDeg = 0 ∧ p.sDeg = 0 ∧ 1 ≤ p.coeff
  · rw [if_pos hp]
    obtain ⟨hpb, hps, hpc⟩ := hp
    have hq0 : q.coeff ≠ 0 := by
      intro hz
      exact hnot ⟨hpb, hps, hpc, Or.inl hz⟩
    have hq1 : 1 ≤ q.coeff := Nat.one_le_iff_ne_zero.mpr hq0
    by_cases hqb : q.bDeg = 0
    · rw [if_pos hqb]
      by_cases hqs : q.sDeg = 0
      · rw [if_pos hqs]
        have hle : p.coeff ≤ q.coeff := by
          by_contra hlt
          exact hnot ⟨hpb, hps, hpc, Or.inr ⟨hqb, hqs, lt_of_not_ge hlt⟩⟩
        show (⟨[p], [q]⟩ : SignedBiPoly).eval 0 0 ≤ 0
        rw [monoPair_eval_origin_of_const p q hpb hps hqb hqs]
        have hle' : (p.coeff : Int) ≤ q.coeff := by exact_mod_cast hle
        omega
      · rw [if_neg hqs]
        exact monoPair_eval_nonpos_of_sDeg_ne_zero p q hpb hps hq1 hqs
    · rw [if_neg hqb]
      exact monoPair_eval_nonpos_of_bDeg_ne_zero p q hpb hps hq1 hqb
  · rw [if_neg hp]
    exact mono_eval_origin_nonpos p q hp

/-- Stratum-level failing-pair extraction; off-stratum instances return the origin. -/
def failMonomialDifference (P : SignedBiPoly) : Nat × Nat :=
  match P.pos, P.neg with
  | [p], [q] => failMonoPair p q
  | _, _ => (0, 0)

theorem failMonomialDifference_pair (p q : BiMono) :
    failMonomialDifference ⟨[p], [q]⟩ = failMonoPair p q := rfl

/-- The stratum-level decision is sound and complete on the stratum. -/
theorem decideMonomialDifferencePositive_iff (P : SignedBiPoly) (h : MonomialDifference P) :
    decideMonomialDifferencePositive P = true ↔ ∀ b s : Nat, 0 < P.eval b s := by
  cases P with
  | mk pos neg =>
    obtain ⟨p, q, hp, hq⟩ := h
    change pos = [p] at hp
    change neg = [q] at hq
    subst hp hq
    rw [decideMonomialDifferencePositive_pair]
    exact decideMonoPairPositive_iff p q

/-- Residual adapter for the decision. -/
theorem decideMonomialDifferencePositive_residual_iff (P : SignedBiPoly)
    (h : MonomialDifference P) :
    decideMonomialDifferencePositive P = true ↔
      ResidualGoal residualWrapper (encodeResidual P) 2 1 := by
  rw [decideMonomialDifferencePositive_iff P h, residualGoal_encode_iff]

/-- The extracted pair witnesses nonpositivity on the stratum. -/
theorem failMonomialDifference_spec (P : SignedBiPoly) (h : MonomialDifference P)
    (hfalse : decideMonomialDifferencePositive P = false) :
    P.eval (failMonomialDifference P).1 (failMonomialDifference P).2 ≤ 0 := by
  cases P with
  | mk pos neg =>
    obtain ⟨p, q, hp, hq⟩ := h
    change pos = [p] at hp
    change neg = [q] at hq
    subst hp hq
    rw [decideMonomialDifferencePositive_pair] at hfalse
    rw [failMonomialDifference_pair]
    exact failMonoPair_spec p q hfalse

/-- Residual adapter for the extracted failing pair. -/
theorem failMonomialDifference_residual_spec (P : SignedBiPoly) (h : MonomialDifference P)
    (hfalse : decideMonomialDifferencePositive P = false) :
    sepDiff residualWrapper (encodeResidual P) 2 1
      (failMonomialDifference P).1 (failMonomialDifference P).2 0 ≤ 0 := by
  rw [encodeResidual_sepDiff]
  exact failMonomialDifference_spec P h hfalse

/-- `b^2 s^2 - 5 b`: one monomial against one monomial, outside the monotone family and both
affine strata, rejected with failing pair `(0, 0)`. -/
def monoPairRejectControl : SignedBiPoly := ⟨[⟨1, 2, 2⟩], [⟨5, 1, 0⟩]⟩

theorem monoPairRejectControl_strata :
    MonomialDifference monoPairRejectControl ∧
      ¬ BaseAffine monoPairRejectControl ∧
      ¬ PayloadAffine monoPairRejectControl ∧
      ¬ NondecreasingBN residualWrapper (encodeResidual monoPairRejectControl) 2 1 := by
  refine ⟨⟨⟨1, 2, 2⟩, ⟨5, 1, 0⟩, rfl, rfl⟩, by decide, by decide, ?_⟩
  intro hmono
  have h := hmono.1 0 1 0 0 (Nat.zero_le 1)
  rw [encodeResidual_sepDiff, encodeResidual_sepDiff] at h
  exact absurd h (by decide)

theorem monoPairRejectControl_decided :
    decideMonomialDifferencePositive monoPairRejectControl = false ∧
      monoPairRejectControl.eval (failMonomialDifference monoPairRejectControl).1
        (failMonomialDifference monoPairRejectControl).2 ≤ 0 := by
  exact ⟨by decide, by decide⟩

/-- `1 - 0 * b^5 s^5`: accepted, and outside both affine strata. -/
def monoPairAcceptControl : SignedBiPoly := ⟨[⟨1, 0, 0⟩], [⟨0, 5, 5⟩]⟩

theorem monoPairAcceptControl_decided :
    decideMonomialDifferencePositive monoPairAcceptControl = true := by
  decide

theorem monoPairAcceptControl_strata :
    MonomialDifference monoPairAcceptControl ∧
      ¬ BaseAffine monoPairAcceptControl ∧ ¬ PayloadAffine monoPairAcceptControl :=
  ⟨⟨⟨1, 0, 0⟩, ⟨0, 5, 5⟩, rfl, rfl⟩, by decide, by decide⟩

theorem monoPairAcceptControl_residual :
    ResidualGoal residualWrapper (encodeResidual monoPairAcceptControl) 2 1 := by
  rw [residualGoal_encode_iff]
  intro b s
  simp [monoPairAcceptControl, SignedBiPoly.eval, biEvalNat]

/-- `2 - b`: rejected, failing pair `(3, 1)`. -/
theorem monoPairRejectGrowing_decided :
    decideMonomialDifferencePositive (⟨[⟨2, 0, 0⟩], [⟨1, 1, 0⟩]⟩ : SignedBiPoly) = false ∧
      (⟨[⟨2, 0, 0⟩], [⟨1, 1, 0⟩]⟩ : SignedBiPoly).eval
        (failMonomialDifference ⟨[⟨2, 0, 0⟩], [⟨1, 1, 0⟩]⟩).1
        (failMonomialDifference ⟨[⟨2, 0, 0⟩], [⟨1, 1, 0⟩]⟩).2 ≤ 0 := by
  decide

/-- Decision table across the accept and reject branches. -/
theorem monoPair_decision_table :
    decideMonomialDifferencePositive ⟨[⟨3, 0, 0⟩], [⟨2, 0, 0⟩]⟩ = true ∧
    decideMonomialDifferencePositive ⟨[⟨2, 0, 0⟩], [⟨3, 0, 0⟩]⟩ = false ∧
    decideMonomialDifferencePositive ⟨[⟨2, 0, 0⟩], [⟨1, 1, 0⟩]⟩ = false ∧
    decideMonomialDifferencePositive ⟨[⟨2, 0, 0⟩], [⟨1, 0, 1⟩]⟩ = false ∧
    decideMonomialDifferencePositive ⟨[⟨0, 0, 0⟩], [⟨0, 0, 0⟩]⟩ = false ∧
    decideMonomialDifferencePositive ⟨[⟨1, 2, 0⟩], [⟨0, 0, 0⟩]⟩ = false := by
  decide

end OperatorKO7.Methods.OrientationClosure.SeparableSlopesMonomialStratum
