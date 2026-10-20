import OperatorKO7.Meta.DistinctionBoundary.GodelPrimitiveRecursive

set_option autoImplicit false

/-!
# Q-axiom arithmetic checker: syntax, coding, proof objects, Nat soundness

This module contains the seven Robinson-Q arithmetic axiom formulas inside a
custom Hilbert-style checker with named variables, closed-term specialization,
injective Gödel coding via polynomial `ccons`, and a standard Nat soundness
proof. It is not yet an identification with a standard recursively axiomatized
first-order Q calculus with the full usual equality/first-order logical
apparatus. The collapsing Unit structure refutes Q1, so the arithmetic axiom
fragment forces successor inequalities and is not the IsSet-relativized
`rca0Basic` fragment. This module does not prove incompleteness.
-/

namespace OperatorKO7.Meta.DistinctionBoundary.GodelArith

inductive Term : Type
  | zero : Term
  | succ : Term → Term
  | add : Term → Term → Term
  | mul : Term → Term → Term
  | var : Nat → Term
  deriving DecidableEq, Repr

inductive Formula : Type
  | eq : Term → Term → Formula
  | not : Formula → Formula
  | imp : Formula → Formula → Formula
  | all : Nat → Formula → Formula
  deriving DecidableEq, Repr

open Term

def numeral : Nat → Term
  | 0 => zero
  | n + 1 => succ (numeral n)

theorem numeral_zero : numeral 0 = zero := rfl

theorem numeral_succ (n : Nat) : numeral (n + 1) = succ (numeral n) := rfl

theorem zero_ne_succ (t : Term) : zero ≠ succ t := by
  intro h
  cases h

theorem succ_injective {s t : Term} (h : succ s = succ t) : s = t := by
  cases h
  rfl

theorem numeral_injective : ∀ a b : Nat, numeral a = numeral b → a = b
  | 0, 0, _ => rfl
  | 0, b + 1, h => (zero_ne_succ (numeral b) h).elim
  | a + 1, 0, h => (zero_ne_succ (numeral a) h.symm).elim
  | a + 1, b + 1, h =>
      congrArg Nat.succ (numeral_injective a b (succ_injective h))

def existsF (x : Nat) (φ : Formula) : Formula :=
  Formula.not (Formula.all x (Formula.not φ))

def orF (φ ψ : Formula) : Formula :=
  Formula.imp (Formula.not φ) ψ

def andF (φ ψ : Formula) : Formula :=
  Formula.not (Formula.imp φ (Formula.not ψ))

def falsum : Formula :=
  Formula.not (Formula.eq zero zero)

def termHasVar (x : Nat) : Term → Bool
  | zero => false
  | succ t => termHasVar x t
  | add s t => termHasVar x s || termHasVar x t
  | mul s t => termHasVar x s || termHasVar x t
  | var y => decide (y = x)

def formHasVar (x : Nat) : Formula → Bool
  | .eq s t => termHasVar x s || termHasVar x t
  | .not φ => formHasVar x φ
  | .imp φ ψ => formHasVar x φ || formHasVar x ψ
  | .all y φ => if y = x then false else formHasVar x φ

def ClosedTerm (t : Term) : Prop := ∀ x : Nat, termHasVar x t = false

def isClosedTerm : Term → Bool
  | zero => true
  | succ t => isClosedTerm t
  | add s t => isClosedTerm s && isClosedTerm t
  | mul s t => isClosedTerm s && isClosedTerm t
  | var _ => false

def IsSentence (φ : Formula) : Prop := ∀ x : Nat, formHasVar x φ = false

theorem numeral_closed : ∀ n x : Nat, termHasVar x (numeral n) = false
  | 0, _ => rfl
  | n + 1, x => numeral_closed n x

theorem numeral_is_closed (n : Nat) : ClosedTerm (numeral n) :=
  fun x => numeral_closed n x

def substTerm (x : Nat) (u : Term) : Term → Term
  | zero => zero
  | succ t => succ (substTerm x u t)
  | add s t => add (substTerm x u s) (substTerm x u t)
  | mul s t => mul (substTerm x u s) (substTerm x u t)
  | var y => if y = x then u else var y

def substForm (x : Nat) (u : Term) : Formula → Formula
  | .eq s t => .eq (substTerm x u s) (substTerm x u t)
  | .not φ => .not (substForm x u φ)
  | .imp φ ψ => .imp (substForm x u φ) (substForm x u ψ)
  | .all y φ => if y = x then .all y φ else .all y (substForm x u φ)

def substNum (φ : Formula) (n : Nat) : Formula :=
  substForm 0 (numeral n) φ

/-- Diagonal substitution uses numerals of codes. Large codes stay behind
`formulaCode` and are never unfolded inside `encodeFormula`. -/
def substQuote (φ : Formula) (n : Nat) : Formula :=
  substNum φ n

theorem substQuote_eq (φ : Formula) (n : Nat) :
    substQuote φ n = substNum φ n :=
  rfl

theorem substTerm_zero (x : Nat) (u : Term) : substTerm x u zero = zero := rfl

theorem substTerm_var_hit (x : Nat) (u : Term) : substTerm x u (var x) = u := by
  simp [substTerm]

theorem substTerm_var_miss (x y : Nat) (u : Term) (h : y ≠ x) :
    substTerm x u (var y) = var y := by
  simp [substTerm, h]

theorem substTerm_numeral (x n : Nat) (u : Term) :
    substTerm x u (numeral n) = numeral n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [numeral, substTerm, ih]

def substWitnessOpen : Term := add (var 0) zero

def substWitnessResult : Term := add (numeral 3) zero

theorem substWitness_eval :
    substTerm 0 (numeral 3) substWitnessOpen = substWitnessResult :=
  rfl

theorem substNum_eq_var0 (n : Nat) :
    substNum (.eq (var 0) (var 0)) n = .eq (numeral n) (numeral n) := by
  rfl

/-! ## Gödel coding (polynomial `ccons`, object-language representable) -/

def encodeTerm : Term → Nat
  | zero => ccons 0 0
  | succ t => ccons 1 (encodeTerm t)
  | add s t => ccons 2 (ccons (encodeTerm s) (encodeTerm t))
  | mul s t => ccons 3 (ccons (encodeTerm s) (encodeTerm t))
  | var n => ccons 4 n

def encodeFormula : Formula → Nat
  | .eq s t => ccons 0 (ccons (encodeTerm s) (encodeTerm t))
  | .not φ => ccons 1 (encodeFormula φ)
  | .imp φ ψ => ccons 2 (ccons (encodeFormula φ) (encodeFormula ψ))
  | .all x φ => ccons 3 (ccons x (encodeFormula φ))

theorem encodeTerm_ne_zero (t : Term) : encodeTerm t ≠ 0 := by
  cases t <;> simp [encodeTerm, ccons_ne_zero]

theorem encodeFormula_ne_zero (φ : Formula) : encodeFormula φ ≠ 0 := by
  cases φ <;> simp [encodeFormula, ccons_ne_zero]

private theorem tag_ne {a b c d : Nat} (h : ccons a b = ccons c d) (hne : a ≠ c) : False :=
  hne (ccons_injective h).1

theorem encodeTerm_injective {s t : Term} (h : encodeTerm s = encodeTerm t) : s = t := by
  induction s generalizing t with
  | zero =>
    cases t with
    | zero => rfl
    | succ t => exact (tag_ne (by simpa [encodeTerm] using h) (by decide)).elim
    | add _ _ => exact (tag_ne (by simpa [encodeTerm] using h) (by decide)).elim
    | mul _ _ => exact (tag_ne (by simpa [encodeTerm] using h) (by decide)).elim
    | var _ => exact (tag_ne (by simpa [encodeTerm] using h) (by decide)).elim
  | succ s ih =>
    cases t with
    | zero => exact (tag_ne (by simpa [encodeTerm] using h) (by decide)).elim
    | succ t =>
      exact congrArg succ (ih (ccons_injective (by simpa [encodeTerm] using h)).2)
    | add _ _ => exact (tag_ne (by simpa [encodeTerm] using h) (by decide)).elim
    | mul _ _ => exact (tag_ne (by simpa [encodeTerm] using h) (by decide)).elim
    | var _ => exact (tag_ne (by simpa [encodeTerm] using h) (by decide)).elim
  | add s1 s2 ih1 ih2 =>
    cases t with
    | zero => exact (tag_ne (by simpa [encodeTerm] using h) (by decide)).elim
    | succ _ => exact (tag_ne (by simpa [encodeTerm] using h) (by decide)).elim
    | add t1 t2 =>
      have hp := ccons_injective (by simpa [encodeTerm] using h)
      have hq := ccons_injective hp.2
      rw [ih1 hq.1, ih2 hq.2]
    | mul _ _ => exact (tag_ne (by simpa [encodeTerm] using h) (by decide)).elim
    | var _ => exact (tag_ne (by simpa [encodeTerm] using h) (by decide)).elim
  | mul s1 s2 ih1 ih2 =>
    cases t with
    | zero => exact (tag_ne (by simpa [encodeTerm] using h) (by decide)).elim
    | succ _ => exact (tag_ne (by simpa [encodeTerm] using h) (by decide)).elim
    | add _ _ => exact (tag_ne (by simpa [encodeTerm] using h) (by decide)).elim
    | mul t1 t2 =>
      have hp := ccons_injective (by simpa [encodeTerm] using h)
      have hq := ccons_injective hp.2
      rw [ih1 hq.1, ih2 hq.2]
    | var _ => exact (tag_ne (by simpa [encodeTerm] using h) (by decide)).elim
  | var n =>
    cases t with
    | zero => exact (tag_ne (by simpa [encodeTerm] using h) (by decide)).elim
    | succ _ => exact (tag_ne (by simpa [encodeTerm] using h) (by decide)).elim
    | add _ _ => exact (tag_ne (by simpa [encodeTerm] using h) (by decide)).elim
    | mul _ _ => exact (tag_ne (by simpa [encodeTerm] using h) (by decide)).elim
    | var m =>
      exact congrArg var (ccons_injective (by simpa [encodeTerm] using h)).2

theorem encodeFormula_injective {φ ψ : Formula} (h : encodeFormula φ = encodeFormula ψ) :
    φ = ψ := by
  induction φ generalizing ψ with
  | eq s t =>
    cases ψ with
    | eq u v =>
      have hp := ccons_injective (by simpa [encodeFormula] using h)
      have hq := ccons_injective hp.2
      rw [encodeTerm_injective hq.1, encodeTerm_injective hq.2]
    | not _ => exact (tag_ne (by simpa [encodeFormula] using h) (by decide)).elim
    | imp _ _ => exact (tag_ne (by simpa [encodeFormula] using h) (by decide)).elim
    | all _ _ => exact (tag_ne (by simpa [encodeFormula] using h) (by decide)).elim
  | not φ ih =>
    cases ψ with
    | eq _ _ => exact (tag_ne (by simpa [encodeFormula] using h) (by decide)).elim
    | not ψ => exact congrArg Formula.not (ih (ccons_injective (by simpa [encodeFormula] using h)).2)
    | imp _ _ => exact (tag_ne (by simpa [encodeFormula] using h) (by decide)).elim
    | all _ _ => exact (tag_ne (by simpa [encodeFormula] using h) (by decide)).elim
  | imp a b iha ihb =>
    cases ψ with
    | eq _ _ => exact (tag_ne (by simpa [encodeFormula] using h) (by decide)).elim
    | not _ => exact (tag_ne (by simpa [encodeFormula] using h) (by decide)).elim
    | imp c d =>
      have hp := ccons_injective (by simpa [encodeFormula] using h)
      have hq := ccons_injective hp.2
      rw [iha hq.1, ihb hq.2]
    | all _ _ => exact (tag_ne (by simpa [encodeFormula] using h) (by decide)).elim
  | all x φ ih =>
    cases ψ with
    | eq _ _ => exact (tag_ne (by simpa [encodeFormula] using h) (by decide)).elim
    | not _ => exact (tag_ne (by simpa [encodeFormula] using h) (by decide)).elim
    | imp _ _ => exact (tag_ne (by simpa [encodeFormula] using h) (by decide)).elim
    | all y ψ =>
      have hp := ccons_injective (by simpa [encodeFormula] using h)
      have hq := ccons_injective hp.2
      cases hq.1
      exact congrArg (Formula.all x) (ih hq.2)

/-- Opaque wrapper so unification does not compute Gödel numbers of large formulas. -/
@[irreducible] def formulaCode (φ : Formula) : Nat :=
  encodeFormula φ

theorem formulaCode_eq (φ : Formula) : formulaCode φ = encodeFormula φ := by
  unfold formulaCode
  rfl

theorem formulaCode_injective {φ ψ : Formula}
    (h : formulaCode φ = formulaCode ψ) : φ = ψ :=
  encodeFormula_injective (formulaCode_eq φ ▸ formulaCode_eq ψ ▸ h)

theorem formulaCode_ne_zero (φ : Formula) : formulaCode φ ≠ 0 := by
  rw [formulaCode_eq]
  exact encodeFormula_ne_zero φ

/-- Substitution on codes: the code of a numeral instance. -/
def codeSubst (φ : Formula) (n : Nat) : Nat :=
  formulaCode (substQuote φ n)

theorem subst_on_codes (φ : Formula) (n : Nat) :
    codeSubst φ n = formulaCode (substQuote φ n) :=
  rfl

def distinctCodeLeft : Formula := Formula.eq zero zero

def distinctCodeRight : Formula := Formula.eq (succ zero) zero

theorem distinct_syntax_distinct_codes :
    encodeFormula distinctCodeLeft ≠ encodeFormula distinctCodeRight := by
  intro h
  have := encodeFormula_injective h
  cases this

/-- Fuelled decoder for term codes. Zero and unknown tags fail. -/
def decodeTerm : Nat → Nat → Option Term
  | 0, _ => none
  | fuel + 1, n =>
      if n = 0 then none
      else
        let p := uncpair (n - 1)
        match p.1 with
        | 0 => if p.2 = 0 then some zero else none
        | 1 => (decodeTerm fuel p.2).map succ
        | 2 =>
          if p.2 = 0 then none
          else
            let q := uncpair (p.2 - 1)
            match decodeTerm fuel q.1, decodeTerm fuel q.2 with
            | some s, some t => some (add s t)
            | _, _ => none
        | 3 =>
          if p.2 = 0 then none
          else
            let q := uncpair (p.2 - 1)
            match decodeTerm fuel q.1, decodeTerm fuel q.2 with
            | some s, some t => some (mul s t)
            | _, _ => none
        | 4 => some (var p.2)
        | _ => none

def decodeFormula : Nat → Nat → Option Formula
  | 0, _ => none
  | fuel + 1, n =>
      if n = 0 then none
      else
        let p := uncpair (n - 1)
        match p.1 with
        | 0 =>
          if p.2 = 0 then none
          else
            let q := uncpair (p.2 - 1)
            match decodeTerm fuel q.1, decodeTerm fuel q.2 with
            | some s, some t => some (Formula.eq s t)
            | _, _ => none
        | 1 => (decodeFormula fuel p.2).map Formula.not
        | 2 =>
          if p.2 = 0 then none
          else
            let q := uncpair (p.2 - 1)
            match decodeFormula fuel q.1, decodeFormula fuel q.2 with
            | some a, some b => some (Formula.imp a b)
            | _, _ => none
        | 3 =>
          if p.2 = 0 then none
          else
            let q := uncpair (p.2 - 1)
            match decodeFormula fuel q.2 with
            | some φ => some (Formula.all q.1 φ)
            | none => none
        | _ => none

def decodeTerm? (n : Nat) : Option Term :=
  decodeTerm (n + 1) n

def decodeFormula? (n : Nat) : Option Formula :=
  decodeFormula (n + 1) n

private theorem fuel_tail {tag payload fuel : Nat}
    (hfuel : ccons tag payload < fuel + 1) : payload < fuel :=
  Nat.lt_of_lt_of_le (ccons_gt_tail tag payload) (Nat.lt_succ.mp hfuel)

theorem decodeTerm_encode :
    ∀ t : Term, ∀ fuel, encodeTerm t < fuel → decodeTerm fuel (encodeTerm t) = some t
  | zero, fuel, hfuel => by
    have hne : ccons 0 0 ≠ 0 := ccons_ne_zero 0 0
    cases fuel with
    | zero => exact (Nat.not_lt_zero _ hfuel).elim
    | succ fuel =>
      simp [decodeTerm, encodeTerm, hne, uncpair_pred_ccons]
  | succ t, fuel, hfuel => by
    cases fuel with
    | zero => exact (Nat.not_lt_zero _ hfuel).elim
    | succ fuel =>
      have hne : ccons 1 (encodeTerm t) ≠ 0 := ccons_ne_zero 1 (encodeTerm t)
      have hrest : encodeTerm t < fuel := fuel_tail (by simpa [encodeTerm] using hfuel)
      simp [decodeTerm, encodeTerm, hne, uncpair_pred_ccons,
        decodeTerm_encode t fuel hrest]
  | add s t, fuel, hfuel => by
    cases fuel with
    | zero => exact (Nat.not_lt_zero _ hfuel).elim
    | succ fuel =>
      have hne : ccons 2 (ccons (encodeTerm s) (encodeTerm t)) ≠ 0 :=
        ccons_ne_zero _ _
      have hne2 : ccons (encodeTerm s) (encodeTerm t) ≠ 0 :=
        ccons_ne_zero _ _
      have hpair : ccons (encodeTerm s) (encodeTerm t) < fuel :=
        fuel_tail (by simpa [encodeTerm] using hfuel)
      have hs : encodeTerm s < fuel :=
        Nat.lt_trans (ccons_gt_head (encodeTerm s) (encodeTerm t)) hpair
      have ht : encodeTerm t < fuel :=
        Nat.lt_trans (ccons_gt_tail (encodeTerm s) (encodeTerm t)) hpair
      simp [decodeTerm, encodeTerm, hne, hne2, uncpair_pred_ccons,
        decodeTerm_encode s fuel hs, decodeTerm_encode t fuel ht]
  | mul s t, fuel, hfuel => by
    cases fuel with
    | zero => exact (Nat.not_lt_zero _ hfuel).elim
    | succ fuel =>
      have hne : ccons 3 (ccons (encodeTerm s) (encodeTerm t)) ≠ 0 :=
        ccons_ne_zero _ _
      have hne2 : ccons (encodeTerm s) (encodeTerm t) ≠ 0 :=
        ccons_ne_zero _ _
      have hpair : ccons (encodeTerm s) (encodeTerm t) < fuel :=
        fuel_tail (by simpa [encodeTerm] using hfuel)
      have hs : encodeTerm s < fuel :=
        Nat.lt_trans (ccons_gt_head (encodeTerm s) (encodeTerm t)) hpair
      have ht : encodeTerm t < fuel :=
        Nat.lt_trans (ccons_gt_tail (encodeTerm s) (encodeTerm t)) hpair
      simp [decodeTerm, encodeTerm, hne, hne2, uncpair_pred_ccons,
        decodeTerm_encode s fuel hs, decodeTerm_encode t fuel ht]
  | var k, fuel, hfuel => by
    cases fuel with
    | zero => exact (Nat.not_lt_zero _ hfuel).elim
    | succ fuel =>
      have hne : ccons 4 k ≠ 0 := ccons_ne_zero 4 k
      simp [decodeTerm, encodeTerm, hne, uncpair_pred_ccons]

theorem decodeTerm?_encode (t : Term) : decodeTerm? (encodeTerm t) = some t :=
  decodeTerm_encode t (encodeTerm t + 1) (Nat.lt_succ_self _)

theorem decode_zero_term : decodeTerm? 0 = none :=
  rfl

theorem decodeFormula_encode :
    ∀ φ : Formula, ∀ fuel, encodeFormula φ < fuel →
      decodeFormula fuel (encodeFormula φ) = some φ
  | Formula.eq s t, fuel, hfuel => by
    cases fuel with
    | zero => exact (Nat.not_lt_zero _ hfuel).elim
    | succ fuel =>
      have hne : ccons 0 (ccons (encodeTerm s) (encodeTerm t)) ≠ 0 :=
        ccons_ne_zero _ _
      have hne2 : ccons (encodeTerm s) (encodeTerm t) ≠ 0 :=
        ccons_ne_zero _ _
      have hpair : ccons (encodeTerm s) (encodeTerm t) < fuel :=
        fuel_tail (by simpa [encodeFormula] using hfuel)
      have hs : encodeTerm s < fuel :=
        Nat.lt_trans (ccons_gt_head (encodeTerm s) (encodeTerm t)) hpair
      have ht : encodeTerm t < fuel :=
        Nat.lt_trans (ccons_gt_tail (encodeTerm s) (encodeTerm t)) hpair
      simp [decodeFormula, encodeFormula, hne, hne2, uncpair_pred_ccons,
        decodeTerm_encode s fuel hs, decodeTerm_encode t fuel ht]
  | Formula.not φ, fuel, hfuel => by
    cases fuel with
    | zero => exact (Nat.not_lt_zero _ hfuel).elim
    | succ fuel =>
      have hne : ccons 1 (encodeFormula φ) ≠ 0 := ccons_ne_zero _ _
      have hφ : encodeFormula φ < fuel := fuel_tail (by simpa [encodeFormula] using hfuel)
      simp [decodeFormula, encodeFormula, hne, uncpair_pred_ccons,
        decodeFormula_encode φ fuel hφ]
  | Formula.imp a b, fuel, hfuel => by
    cases fuel with
    | zero => exact (Nat.not_lt_zero _ hfuel).elim
    | succ fuel =>
      have hne : ccons 2 (ccons (encodeFormula a) (encodeFormula b)) ≠ 0 :=
        ccons_ne_zero _ _
      have hne2 : ccons (encodeFormula a) (encodeFormula b) ≠ 0 :=
        ccons_ne_zero _ _
      have hpair : ccons (encodeFormula a) (encodeFormula b) < fuel :=
        fuel_tail (by simpa [encodeFormula] using hfuel)
      have ha : encodeFormula a < fuel :=
        Nat.lt_trans (ccons_gt_head (encodeFormula a) (encodeFormula b)) hpair
      have hb : encodeFormula b < fuel :=
        Nat.lt_trans (ccons_gt_tail (encodeFormula a) (encodeFormula b)) hpair
      simp [decodeFormula, encodeFormula, hne, hne2, uncpair_pred_ccons,
        decodeFormula_encode a fuel ha, decodeFormula_encode b fuel hb]
  | Formula.all x φ, fuel, hfuel => by
    cases fuel with
    | zero => exact (Nat.not_lt_zero _ hfuel).elim
    | succ fuel =>
      have hne : ccons 3 (ccons x (encodeFormula φ)) ≠ 0 := ccons_ne_zero _ _
      have hne2 : ccons x (encodeFormula φ) ≠ 0 := ccons_ne_zero _ _
      have hpair : ccons x (encodeFormula φ) < fuel :=
        fuel_tail (by simpa [encodeFormula] using hfuel)
      have hφ : encodeFormula φ < fuel :=
        Nat.lt_trans (ccons_gt_tail x (encodeFormula φ)) hpair
      simp [decodeFormula, encodeFormula, hne, hne2, uncpair_pred_ccons,
        decodeFormula_encode φ fuel hφ]

theorem decodeFormula?_encode (φ : Formula) :
    decodeFormula? (encodeFormula φ) = some φ :=
  decodeFormula_encode φ (encodeFormula φ + 1) (Nat.lt_succ_self _)

theorem decode_zero_formula : decodeFormula? 0 = none :=
  rfl

theorem decodeFormula?_formulaCode (φ : Formula) :
    decodeFormula? (formulaCode φ) = some φ := by
  rw [formulaCode_eq]
  exact decodeFormula?_encode φ

/-- Quantifier-free formulas. -/
def isBounded : Formula → Bool
  | Formula.eq _ _ => true
  | Formula.not φ => isBounded φ
  | Formula.imp φ ψ => isBounded φ && isBounded ψ
  | Formula.all _ _ => false

theorem qf_eq_bounded (s t : Term) : isBounded (Formula.eq s t) = true := rfl

theorem all_not_bounded (x : Nat) (φ : Formula) :
    isBounded (Formula.all x φ) = false :=
  rfl

/-! ## Robinson Q axioms -/

def q1 : Formula :=
  Formula.all 0 (Formula.not (Formula.eq (succ (var 0)) zero))

def q2 : Formula :=
  Formula.all 0 (Formula.all 1 (Formula.imp (Formula.eq (succ (var 0)) (succ (var 1)))
    (Formula.eq (var 0) (var 1))))

def q3 : Formula :=
  Formula.all 0 (Formula.eq (add (var 0) zero) (var 0))

def q4 : Formula :=
  Formula.all 0 (Formula.all 1 (Formula.eq (add (var 0) (succ (var 1)))
    (succ (add (var 0) (var 1)))))

def q5 : Formula :=
  Formula.all 0 (Formula.eq (mul (var 0) zero) zero)

def q6 : Formula :=
  Formula.all 0 (Formula.all 1 (Formula.eq (mul (var 0) (succ (var 1)))
    (add (mul (var 0) (var 1)) (var 0))))

def q7 : Formula :=
  Formula.all 0 (orF (Formula.eq (var 0) zero) (existsF 1 (Formula.eq (var 0) (succ (var 1)))))

def isQAxiom (φ : Formula) : Bool :=
  decide (φ = q1) || decide (φ = q2) || decide (φ = q3) ||
    decide (φ = q4) || decide (φ = q5) || decide (φ = q6) || decide (φ = q7)

theorem q1_is_axiom : isQAxiom q1 = true := by
  simp [isQAxiom]

theorem q7_is_axiom : isQAxiom q7 = true := by
  simp [isQAxiom]

theorem falsum_not_q_axiom : isQAxiom falsum = false := by
  simp [isQAxiom, falsum, q1, q2, q3, q4, q5, q6, q7]

/-! ## Logical axiom schemas (decidable) -/

def isAxK : Formula → Bool
  | Formula.imp a (Formula.imp _b c) => decide (a = c)
  | _ => false

def isAxS : Formula → Bool
  | Formula.imp (Formula.imp a (Formula.imp b c))
      (Formula.imp (Formula.imp a' b') (Formula.imp a'' c')) =>
        decide (a = a' ∧ a = a'' ∧ b = b' ∧ c = c')
  | _ => false

def isAxDNE : Formula → Bool
  | Formula.imp (Formula.not (Formula.not a)) b => decide (a = b)
  | _ => false

def isEqRefl : Formula → Bool
  | Formula.eq s t => decide (s = t)
  | _ => false

def isAxId : Formula → Bool
  | Formula.imp a b => decide (a = b)
  | _ => false

def isAxiom (φ : Formula) : Bool :=
  isQAxiom φ || isAxK φ || isAxS φ || isAxDNE φ || isEqRefl φ || isAxId φ

theorem q1_axiom : isAxiom q1 = true := by
  simp [isAxiom, isQAxiom]

theorem eq_refl_axiom (t : Term) : isAxiom (Formula.eq t t) = true := by
  simp [isAxiom, isEqRefl, isQAxiom, isAxK, isAxS, isAxDNE, isAxId]

theorem falsum_not_axiom : isAxiom falsum = false := by
  decide

/-! ## Proof trees and checker -/

inductive ProofTree : Type
  | ax : Formula → ProofTree
  | mp : ProofTree → ProofTree → ProofTree
  | gen : Nat → ProofTree → ProofTree
  | spec : Nat → Term → ProofTree → ProofTree
  deriving DecidableEq, Repr

def check : ProofTree → Option Formula
  | .ax φ => if isAxiom φ then some φ else none
  | .mp p q =>
      match check p, check q with
      | some (Formula.imp a b), some c => if a = c then some b else none
      | _, _ => none
  | .gen x p =>
      match check p with
      | some φ => some (Formula.all x φ)
      | none => none
  | .spec x t p =>
      match check p with
      | some (Formula.all y φ) =>
          if decide (x = y) && isClosedTerm t then some (substForm x t φ) else none
      | _ => none

def conclusion? (p : ProofTree) : Option Formula := check p

def ValidProof (p : ProofTree) (φ : Formula) : Prop :=
  check p = some φ

def Provable (φ : Formula) : Prop :=
  ∃ p : ProofTree, ValidProof p φ

def Cons : Prop :=
  ¬ Provable falsum

def validProofAx : ProofTree := .ax q1

theorem validProofAx_checks : ValidProof validProofAx q1 := by
  simp [ValidProof, validProofAx, check, isAxiom, isQAxiom]

theorem q1_provable : Provable q1 :=
  ⟨validProofAx, validProofAx_checks⟩

def invalidProofAx : ProofTree := .ax falsum

theorem invalidProofAx_rejected : check invalidProofAx = none := by
  simp [invalidProofAx, check, falsum_not_axiom]

theorem invalid_not_valid : ¬ ValidProof invalidProofAx falsum := by
  intro h
  simp [ValidProof, invalidProofAx_rejected] at h

def encodeProof : ProofTree → Nat
  | .ax φ => ccons 0 (encodeFormula φ)
  | .mp p q => ccons 1 (ccons (encodeProof p) (encodeProof q))
  | .gen x p => ccons 2 (ccons x (encodeProof p))
  | .spec x t p => ccons 3 (ccons x (ccons (encodeTerm t) (encodeProof p)))

theorem encodeProof_ne_zero (p : ProofTree) : encodeProof p ≠ 0 := by
  cases p with
  | ax φ => exact ccons_ne_zero _ _
  | mp p q => exact ccons_ne_zero _ _
  | gen x p => exact ccons_ne_zero _ _
  | spec x t p => exact ccons_ne_zero _ _

theorem encodeProof_ax (φ : Formula) :
    encodeProof (.ax φ) = ccons 0 (encodeFormula φ) :=
  rfl

theorem encodeProof_ax_injective {φ ψ : Formula}
    (h : encodeProof (.ax φ) = encodeProof (.ax ψ)) : φ = ψ := by
  have hp := ccons_injective (by simpa [encodeProof] using h)
  exact encodeFormula_injective hp.2

def decodeProof : Nat → Nat → Option ProofTree
  | 0, _ => none
  | fuel + 1, n =>
      if n = 0 then none
      else
        let p := uncpair (n - 1)
        match p.1 with
        | 0 => (decodeFormula fuel p.2).map ProofTree.ax
        | 1 =>
          if p.2 = 0 then none
          else
            let q := uncpair (p.2 - 1)
            match decodeProof fuel q.1, decodeProof fuel q.2 with
            | some a, some b => some (ProofTree.mp a b)
            | _, _ => none
        | 2 =>
          if p.2 = 0 then none
          else
            let q := uncpair (p.2 - 1)
            match decodeProof fuel q.2 with
            | some t => some (ProofTree.gen q.1 t)
            | none => none
        | 3 =>
          if p.2 = 0 then none
          else
            let q := uncpair (p.2 - 1)
            if q.2 = 0 then none
            else
              let r := uncpair (q.2 - 1)
              match decodeTerm fuel r.1, decodeProof fuel r.2 with
              | some t, some tree => some (ProofTree.spec q.1 t tree)
              | _, _ => none
        | _ => none

def decodeProof? (n : Nat) : Option ProofTree :=
  decodeProof (n + 1) n

theorem decodeProof_encode :
    ∀ p : ProofTree, ∀ fuel, encodeProof p < fuel →
      decodeProof fuel (encodeProof p) = some p
  | .ax φ, fuel, hfuel => by
    cases fuel with
    | zero => exact (Nat.not_lt_zero _ hfuel).elim
    | succ fuel =>
      have hne : ccons 0 (encodeFormula φ) ≠ 0 := ccons_ne_zero _ _
      have hφ : encodeFormula φ < fuel :=
        Nat.lt_of_lt_of_le (ccons_gt_tail 0 (encodeFormula φ)) (Nat.lt_succ.mp hfuel)
      simp [decodeProof, encodeProof, hne, uncpair_pred_ccons,
        decodeFormula_encode φ fuel hφ]
  | .mp p q, fuel, hfuel => by
    cases fuel with
    | zero => exact (Nat.not_lt_zero _ hfuel).elim
    | succ fuel =>
      have hne : ccons 1 (ccons (encodeProof p) (encodeProof q)) ≠ 0 :=
        ccons_ne_zero _ _
      have hne2 : ccons (encodeProof p) (encodeProof q) ≠ 0 :=
        ccons_ne_zero _ _
      have hpair : ccons (encodeProof p) (encodeProof q) < fuel :=
        Nat.lt_of_lt_of_le
          (ccons_gt_tail 1 (ccons (encodeProof p) (encodeProof q)))
          (Nat.lt_succ.mp hfuel)
      have hp : encodeProof p < fuel :=
        Nat.lt_trans (ccons_gt_head (encodeProof p) (encodeProof q)) hpair
      have hq : encodeProof q < fuel :=
        Nat.lt_trans (ccons_gt_tail (encodeProof p) (encodeProof q)) hpair
      simp [decodeProof, encodeProof, hne, hne2, uncpair_pred_ccons,
        decodeProof_encode p fuel hp, decodeProof_encode q fuel hq]
  | .gen x p, fuel, hfuel => by
    cases fuel with
    | zero => exact (Nat.not_lt_zero _ hfuel).elim
    | succ fuel =>
      have hne : ccons 2 (ccons x (encodeProof p)) ≠ 0 := ccons_ne_zero _ _
      have hne2 : ccons x (encodeProof p) ≠ 0 := ccons_ne_zero _ _
      have hpair : ccons x (encodeProof p) < fuel :=
        Nat.lt_of_lt_of_le (ccons_gt_tail 2 (ccons x (encodeProof p)))
          (Nat.lt_succ.mp hfuel)
      have hp : encodeProof p < fuel :=
        Nat.lt_trans (ccons_gt_tail x (encodeProof p)) hpair
      simp [decodeProof, encodeProof, hne, hne2, uncpair_pred_ccons,
        decodeProof_encode p fuel hp]
  | .spec x t p, fuel, hfuel => by
    cases fuel with
    | zero => exact (Nat.not_lt_zero _ hfuel).elim
    | succ fuel =>
      have hne : ccons 3 (ccons x (ccons (encodeTerm t) (encodeProof p))) ≠ 0 :=
        ccons_ne_zero _ _
      have hne2 : ccons x (ccons (encodeTerm t) (encodeProof p)) ≠ 0 :=
        ccons_ne_zero _ _
      have hne3 : ccons (encodeTerm t) (encodeProof p) ≠ 0 :=
        ccons_ne_zero _ _
      have hmid : ccons x (ccons (encodeTerm t) (encodeProof p)) < fuel :=
        Nat.lt_of_lt_of_le
          (ccons_gt_tail 3 (ccons x (ccons (encodeTerm t) (encodeProof p))))
          (Nat.lt_succ.mp hfuel)
      have hpair : ccons (encodeTerm t) (encodeProof p) < fuel :=
        Nat.lt_trans (ccons_gt_tail x (ccons (encodeTerm t) (encodeProof p))) hmid
      have ht : encodeTerm t < fuel :=
        Nat.lt_trans (ccons_gt_head (encodeTerm t) (encodeProof p)) hpair
      have hp : encodeProof p < fuel :=
        Nat.lt_trans (ccons_gt_tail (encodeTerm t) (encodeProof p)) hpair
      simp [decodeProof, encodeProof, hne, hne2, hne3, uncpair_pred_ccons,
        decodeTerm_encode t fuel ht, decodeProof_encode p fuel hp]

theorem decodeProof?_encode (p : ProofTree) :
    decodeProof? (encodeProof p) = some p :=
  decodeProof_encode p (encodeProof p + 1) (Nat.lt_succ_self _)

/-! ## Standard Nat semantics -/

def evalTerm (env : Nat → Nat) : Term → Nat
  | zero => 0
  | succ t => evalTerm env t + 1
  | add s t => evalTerm env s + evalTerm env t
  | mul s t => evalTerm env s * evalTerm env t
  | var x => env x

def evalForm (env : Nat → Nat) : Formula → Prop
  | Formula.eq s t => evalTerm env s = evalTerm env t
  | Formula.not φ => ¬ evalForm env φ
  | Formula.imp φ ψ => evalForm env φ → evalForm env ψ
  | Formula.all x φ => ∀ n : Nat, evalForm (fun y => if y = x then n else env y) φ

def envUpdate (env : Nat → Nat) (x n : Nat) : Nat → Nat :=
  fun y => if y = x then n else env y

theorem evalTerm_numeral (env : Nat → Nat) : ∀ n : Nat, evalTerm env (numeral n) = n
  | 0 => rfl
  | n + 1 => by simp [numeral, evalTerm, evalTerm_numeral env n]

theorem isClosedTerm_numeral : ∀ n : Nat, isClosedTerm (numeral n) = true
  | 0 => rfl
  | n + 1 => by simp [numeral, isClosedTerm, isClosedTerm_numeral n]

theorem isClosedTerm_eval_indep (t : Term) (ht : isClosedTerm t = true) :
    ∀ env env' : Nat → Nat, evalTerm env t = evalTerm env' t := by
  induction t with
  | zero => intro env env'; rfl
  | succ t ih =>
    intro env env'
    simp [isClosedTerm] at ht
    simp [evalTerm]
    exact ih ht env env'
  | add s t ihs iht =>
    intro env env'
    simp [isClosedTerm, Bool.and_eq_true] at ht
    simp [evalTerm]
    rw [ihs ht.1 env env', iht ht.2 env env']
  | mul s t ihs iht =>
    intro env env'
    simp [isClosedTerm, Bool.and_eq_true] at ht
    simp [evalTerm]
    rw [ihs ht.1 env env', iht ht.2 env env']
  | var _ => simp [isClosedTerm] at ht

theorem envUpdate_if_comm (env : Nat → Nat) {x y : Nat} (hne : y ≠ x)
    (n m : Nat) (z : Nat) :
    envUpdate (fun w => if w = y then m else env w) x n z =
      (if z = y then m else envUpdate env x n z) := by
  simp only [envUpdate]
  by_cases hz : z = x
  · by_cases hy : z = y
    · exact False.elim (hne (hy.symm.trans hz))
    · rw [if_pos hz, if_neg hy, if_pos hz]
  · by_cases hy : z = y
    · rw [if_neg hz, if_pos hy]
      simp [hy]
    · rw [if_neg hz, if_neg hy, if_neg hz]
      simp [hy]

theorem evalTerm_subst (env : Nat → Nat) (x : Nat) (u : Term) :
    ∀ t : Term,
      evalTerm env (substTerm x u t) =
        evalTerm (envUpdate env x (evalTerm env u)) t
  | zero => rfl
  | succ t => by simp [substTerm, evalTerm, evalTerm_subst env x u t]
  | add s t => by
      simp [substTerm, evalTerm, evalTerm_subst env x u s, evalTerm_subst env x u t]
  | mul s t => by
      simp [substTerm, evalTerm, evalTerm_subst env x u s, evalTerm_subst env x u t]
  | var y => by
      by_cases h : y = x
      · subst h
        simp [substTerm, evalTerm, envUpdate]
      · simp [substTerm, evalTerm, envUpdate, h]

theorem evalForm_env_eq_aux (φ : Formula) :
    ∀ {env env' : Nat → Nat}, (∀ z, env z = env' z) →
      (evalForm env φ ↔ evalForm env' φ) := by
  induction φ with
  | eq s t =>
    intro env env' h
    have hs : evalTerm env s = evalTerm env' s := by
      induction s with
      | zero => rfl
      | succ s ih => simp [evalTerm, ih]
      | add a b iha ihb => simp [evalTerm, iha, ihb]
      | mul a b iha ihb => simp [evalTerm, iha, ihb]
      | var z => exact h z
    have ht : evalTerm env t = evalTerm env' t := by
      induction t with
      | zero => rfl
      | succ t ih => simp [evalTerm, ih]
      | add a b iha ihb => simp [evalTerm, iha, ihb]
      | mul a b iha ihb => simp [evalTerm, iha, ihb]
      | var z => exact h z
    simp [evalForm, hs, ht]
  | not φ ih =>
    intro env env' h
    simp [evalForm, ih h]
  | imp φ ψ ihφ ihψ =>
    intro env env' h
    simp [evalForm, ihφ h, ihψ h]
  | all y φ ih =>
    intro env env' h
    dsimp [evalForm]
    constructor
    · intro hall k
      have henv : ∀ z,
          (fun w => if w = y then k else env w) z =
            (fun w => if w = y then k else env' w) z := by
        intro z
        by_cases hz : z = y
        · simp [hz]
        · simp [hz, h z]
      exact (ih henv).1 (hall k)
    · intro hall k
      have henv : ∀ z,
          (fun w => if w = y then k else env' w) z =
            (fun w => if w = y then k else env w) z := by
        intro z
        by_cases hz : z = y
        · simp [hz]
        · simp [hz, (h z).symm]
      exact (ih henv).1 (hall k)

theorem evalForm_subst_closed (env : Nat → Nat) (x : Nat) (u : Term)
    (hu : isClosedTerm u = true) :
    ∀ φ : Formula,
      evalForm env (substForm x u φ) ↔
        evalForm (envUpdate env x (evalTerm env u)) φ
  | Formula.eq s t => by
      simp [substForm, evalForm, evalTerm_subst env x u s, evalTerm_subst env x u t]
  | Formula.not φ => by
      simp [substForm, evalForm, evalForm_subst_closed env x u hu φ]
  | Formula.imp φ ψ => by
      simp [substForm, evalForm, evalForm_subst_closed env x u hu φ,
        evalForm_subst_closed env x u hu ψ]
  | Formula.all y φ => by
      by_cases hxy : y = x
      · subst hxy
        simp [substForm, evalForm]
        constructor
        · intro hall m
          have henv : ∀ z, envUpdate (envUpdate env y (evalTerm env u)) y m z =
              envUpdate env y m z := by
            intro z; simp [envUpdate]
            by_cases hz : z = y
            · simp [hz]
            · simp [hz]
          exact (evalForm_env_eq_aux φ henv).2 (hall m)
        · intro hall m
          have henv : ∀ z, envUpdate env y m z =
              envUpdate (envUpdate env y (evalTerm env u)) y m z := by
            intro z; simp [envUpdate]
            by_cases hz : z = y
            · simp [hz]
            · simp [hz]
          exact (evalForm_env_eq_aux φ henv).2 (hall m)
      · simp [substForm, evalForm, hxy]
        constructor
        · intro hall m
          have := (evalForm_subst_closed (fun w => if w = y then m else env w) x u hu φ).1
            (hall m)
          have hu' : evalTerm (fun w => if w = y then m else env w) u =
              evalTerm env u :=
            isClosedTerm_eval_indep u hu _ _
          have henv : ∀ z,
              envUpdate (fun w => if w = y then m else env w) x
                  (evalTerm (fun w => if w = y then m else env w) u) z =
                (fun w => if w = y then m else envUpdate env x (evalTerm env u) w) z := by
            intro z
            have hcomm := envUpdate_if_comm env hxy
              (evalTerm (fun w => if w = y then m else env w) u) m z
            simpa [hu'] using hcomm
          exact (evalForm_env_eq_aux φ henv).1 this
        · intro hall m
          have hu' : evalTerm (fun w => if w = y then m else env w) u =
              evalTerm env u :=
            isClosedTerm_eval_indep u hu _ _
          have henv : ∀ z,
              (fun w => if w = y then m else envUpdate env x (evalTerm env u) w) z =
                envUpdate (fun w => if w = y then m else env w) x
                  (evalTerm (fun w => if w = y then m else env w) u) z := by
            intro z
            have hcomm := envUpdate_if_comm env hxy
              (evalTerm (fun w => if w = y then m else env w) u) m z
            simpa [hu'] using hcomm.symm
          have := (evalForm_env_eq_aux φ henv).1 (hall m)
          exact (evalForm_subst_closed (fun w => if w = y then m else env w) x u hu φ).2 this

theorem evalForm_q1 (env : Nat → Nat) : evalForm env q1 := by
  dsimp [q1, evalForm, evalTerm]
  intro n
  exact Nat.succ_ne_zero n

theorem evalForm_q3 (env : Nat → Nat) : evalForm env q3 := by
  dsimp [q3, evalForm, evalTerm]
  intro n
  rfl

theorem evalForm_q5 (env : Nat → Nat) : evalForm env q5 := by
  dsimp [q5, evalForm, evalTerm]
  intro n
  rfl

theorem evalForm_q2 (env : Nat → Nat) : evalForm env q2 := by
  dsimp [q2, evalForm, evalTerm]
  intro n m h
  exact Nat.succ.inj h

theorem evalForm_q4 (env : Nat → Nat) : evalForm env q4 := by
  dsimp [q4, evalForm, evalTerm]
  intro n m
  rfl

theorem evalForm_q6 (env : Nat → Nat) : evalForm env q6 := by
  dsimp [q6, evalForm, evalTerm]
  intro n m
  exact (Nat.mul_succ n m).symm

theorem evalForm_q7 (env : Nat → Nat) : evalForm env q7 := by
  dsimp [q7, orF, existsF, evalForm, evalTerm]
  intro n
  cases n with
  | zero =>
    intro h
    exact (h rfl).elim
  | succ m =>
    intro _ hall
    exact hall m rfl

theorem evalForm_falsum (env : Nat → Nat) : ¬ evalForm env falsum := by
  dsimp [falsum, evalForm, evalTerm]
  intro h
  exact h rfl

theorem evalForm_eq_refl (env : Nat → Nat) (t : Term) :
    evalForm env (Formula.eq t t) := by
  dsimp [evalForm]

theorem isAxK_shape {φ : Formula} (h : isAxK φ = true) :
    ∃ a b, φ = Formula.imp a (Formula.imp b a) := by
  cases φ with
  | imp a ψ =>
    cases ψ with
    | imp b c =>
      have : a = c := by simpa [isAxK] using h
      subst this
      exact ⟨a, b, rfl⟩
    | eq _ _ => simp [isAxK] at h
    | not _ => simp [isAxK] at h
    | all _ _ => simp [isAxK] at h
  | eq _ _ => simp [isAxK] at h
  | not _ => simp [isAxK] at h
  | all _ _ => simp [isAxK] at h

theorem isQAxiom_iff (φ : Formula) :
    isQAxiom φ = true ↔
      (((((φ = q1 ∨ φ = q2) ∨ φ = q3) ∨ φ = q4) ∨ φ = q5) ∨ φ = q6) ∨ φ = q7 := by
  simp [isQAxiom]

theorem eval_isQAxiom (env : Nat → Nat) {φ : Formula} (h : isQAxiom φ = true) :
    evalForm env φ := by
  rcases (isQAxiom_iff φ).1 h with
    (((((rfl | rfl) | rfl) | rfl) | rfl) | rfl) | rfl
  · exact evalForm_q1 env
  · exact evalForm_q2 env
  · exact evalForm_q3 env
  · exact evalForm_q4 env
  · exact evalForm_q5 env
  · exact evalForm_q6 env
  · exact evalForm_q7 env

theorem isAxS_shape {φ : Formula} (h : isAxS φ = true) :
    ∃ a b c, φ = Formula.imp (Formula.imp a (Formula.imp b c))
      (Formula.imp (Formula.imp a b) (Formula.imp a c)) := by
  cases φ with
  | imp ψ χ =>
    cases ψ with
    | imp a ψ' =>
      cases ψ' with
      | imp b c =>
        cases χ with
        | imp χ1 χ2 =>
          cases χ1 with
          | imp a' b' =>
            cases χ2 with
            | imp a'' c' =>
              have : a = a' ∧ a = a'' ∧ b = b' ∧ c = c' := by
                simpa [isAxS] using h
              rcases this with ⟨h1, h2, h3, h4⟩
              refine ⟨a, b, c, ?_⟩
              cases h1; cases h2; cases h3; cases h4
              rfl
            | eq _ _ => simp [isAxS] at h
            | not _ => simp [isAxS] at h
            | all _ _ => simp [isAxS] at h
          | eq _ _ => simp [isAxS] at h
          | not _ => simp [isAxS] at h
          | all _ _ => simp [isAxS] at h
        | eq _ _ => simp [isAxS] at h
        | not _ => simp [isAxS] at h
        | all _ _ => simp [isAxS] at h
      | eq _ _ => simp [isAxS] at h
      | not _ => simp [isAxS] at h
      | all _ _ => simp [isAxS] at h
    | eq _ _ => simp [isAxS] at h
    | not _ => simp [isAxS] at h
    | all _ _ => simp [isAxS] at h
  | eq _ _ => simp [isAxS] at h
  | not _ => simp [isAxS] at h
  | all _ _ => simp [isAxS] at h

theorem isAxDNE_shape {φ : Formula} (h : isAxDNE φ = true) :
    ∃ a, φ = Formula.imp (Formula.not (Formula.not a)) a := by
  cases φ with
  | imp ψ χ =>
    cases ψ with
    | not ψ' =>
      cases ψ' with
      | not a =>
        have : a = χ := by simpa [isAxDNE] using h
        refine ⟨a, ?_⟩
        simp [this]
      | eq _ _ => simp [isAxDNE] at h
      | imp _ _ => simp [isAxDNE] at h
      | all _ _ => simp [isAxDNE] at h
    | eq _ _ => simp [isAxDNE] at h
    | imp _ _ => simp [isAxDNE] at h
    | all _ _ => simp [isAxDNE] at h
  | eq _ _ => simp [isAxDNE] at h
  | not _ => simp [isAxDNE] at h
  | all _ _ => simp [isAxDNE] at h

theorem eval_isAxiom (env : Nat → Nat) {φ : Formula} (hax : isAxiom φ = true) :
    evalForm env φ := by
  simp [isAxiom, Bool.or_eq_true] at hax
  rcases hax with (((((hQ | hK) | hS) | hDNE) | hR) | hId)
  · exact eval_isQAxiom env hQ
  · rcases isAxK_shape hK with ⟨a, b, rfl⟩
    intro ha _hb
    exact ha
  · rcases isAxS_shape hS with ⟨a, b, c, rfl⟩
    intro habc hab ha
    exact habc ha (hab ha)
  · rcases isAxDNE_shape hDNE with ⟨a, rfl⟩
    intro hnn
    exact Classical.not_not.mp hnn
  · cases φ with
    | eq s t =>
      have : s = t := by simpa [isEqRefl] using hR
      subst this
      exact evalForm_eq_refl env s
    | not _ => simp [isEqRefl] at hR
    | imp _ _ => simp [isEqRefl] at hR
    | all _ _ => simp [isEqRefl] at hR
  · cases φ with
    | imp a b =>
      have : a = b := by simpa [isAxId] using hId
      subst this
      intro ha
      exact ha
    | eq _ _ => simp [isAxId] at hId
    | not _ => simp [isAxId] at hId
    | all _ _ => simp [isAxId] at hId

theorem check_sound :
    ∀ p : ProofTree, ∀ φ : Formula, ∀ env : Nat → Nat,
      check p = some φ → evalForm env φ := by
  intro p
  induction p with
  | ax ψ =>
    intro φ env h
    simp [check] at h
    rcases h with ⟨hax, rfl⟩
    exact eval_isAxiom env hax
  | mp p q ihp ihq =>
    intro φ env h
    cases hp : check p with
    | none =>
      simp [check, hp] at h
    | some a =>
      cases hq : check q with
      | none =>
        simp [check, hp, hq] at h
      | some c =>
        simp [check, hp, hq] at h
        cases a with
        | imp u v =>
          simp at h
          rcases h with ⟨hc, hφ⟩
          subst hc
          subst hφ
          have himp := ihp (Formula.imp u v) env hp
          have hu := ihq u env hq
          exact himp hu
        | eq _ _ => simp at h
        | not _ => simp at h
        | all _ _ => simp at h
  | gen x p ih =>
    intro φ env h
    cases hp : check p with
    | none =>
      simp [check, hp] at h
    | some ψ =>
      simp [check, hp] at h
      cases h
      dsimp [evalForm]
      intro n
      exact ih ψ (fun y => if y = x then n else env y) hp
  | spec x t p ih =>
    intro φ env h
    cases hp : check p with
    | none =>
      simp [check, hp] at h
    | some ψ =>
      cases ψ with
      | all y θ =>
        simp [check, hp] at h
        rcases h with ⟨⟨hx, ht⟩, hφ⟩
        subst hx
        subst hφ
        have hall := ih (Formula.all x θ) env hp
        have hinst := hall (evalTerm env t)
        exact (evalForm_subst_closed env x t ht θ).2 hinst
      | eq _ _ => simp [check, hp] at h
      | not _ => simp [check, hp] at h
      | imp _ _ => simp [check, hp] at h

theorem provable_sound {φ : Formula} (h : Provable φ) (env : Nat → Nat) :
    evalForm env φ := by
  rcases h with ⟨p, hp⟩
  exact check_sound p φ env hp

theorem q_consistent : Cons := by
  intro h
  exact evalForm_falsum (fun _ => 0) (provable_sound h (fun _ => 0))

def evalFormUnit : Formula → Prop
  | Formula.eq _ _ => True
  | Formula.not φ => ¬ evalFormUnit φ
  | Formula.imp φ ψ => evalFormUnit φ → evalFormUnit ψ
  | Formula.all _ φ => evalFormUnit φ

theorem unit_models_eq : evalFormUnit (Formula.eq (succ (var 0)) zero) :=
  trivial

theorem unit_refutes_q1 : ¬ evalFormUnit q1 := by
  dsimp [q1, evalFormUnit]
  intro h
  exact h trivial

theorem nat_models_q1 : evalForm (fun _ => 0) q1 :=
  evalForm_q1 (fun _ => 0)

theorem q_forces_successor_inequality :
    evalForm (fun _ => 0) q1 ∧ ¬ evalFormUnit q1 :=
  ⟨nat_models_q1, unit_refutes_q1⟩

def sentenceWitness : Formula := q1

theorem sentenceWitness_code_pos : encodeFormula sentenceWitness ≠ 0 :=
  encodeFormula_ne_zero _

def termWitness : Term := add (numeral 2) (succ zero)

theorem termWitness_code_ne_zero : encodeTerm termWitness ≠ 0 :=
  encodeTerm_ne_zero _

/-- Arithmetized checker: a pair of codes is a valid proof/conclusion. -/
def isProofCode (n m : Nat) : Bool :=
  match decodeProof? n, decodeFormula? m with
  | some p, some φ => decide (check p = some φ)
  | _, _ => false

theorem isProofCode_iff (p : ProofTree) (φ : Formula) :
    isProofCode (encodeProof p) (encodeFormula φ) = true ↔ check p = some φ := by
  simp [isProofCode, decodeProof?_encode, decodeFormula?_encode]

theorem isProofCode_valid {p : ProofTree} {φ : Formula}
    (h : check p = some φ) :
    isProofCode (encodeProof p) (formulaCode φ) = true := by
  rw [formulaCode_eq]
  exact (isProofCode_iff p φ).2 h

theorem isProofCode_none (n m : Nat) (h : isProofCode n m = true) :
    ∃ p : ProofTree, ∃ φ : Formula,
      decodeProof? n = some p ∧ decodeFormula? m = some φ ∧ check p = some φ := by
  simp [isProofCode] at h
  cases hp : decodeProof? n with
  | none => simp [hp] at h
  | some p =>
    cases hφ : decodeFormula? m with
    | none => simp [hp, hφ] at h
    | some φ =>
      have hchk : check p = some φ := by
        simpa [isProofCode, hp, hφ] using h
      exact ⟨p, φ, rfl, rfl, hchk⟩

end OperatorKO7.Meta.DistinctionBoundary.GodelArith
